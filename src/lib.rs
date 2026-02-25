#![cfg_attr(not(test), no_std)]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, token, Address, BytesN, Env, Symbol,
};

/// Upper bound for vault creation amounts to limit pathological transfers.
const MAX_AMOUNT: i128 = 1_000_000_000_000_000;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------
//
// Contract-specific errors used in revert paths. Follows Soroban error
// conventions: use Result<T, Error> and return Err(Error::Variant) instead
// of generic panics where appropriate.

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    /// Vault with the given id does not exist.
    VaultNotFound = 1,
    /// Caller is not authorized for this operation (e.g. not verifier/creator, or release before deadline without validation).
    NotAuthorized = 2,
    /// Vault is not in Active status (e.g. already Completed, Failed, or Cancelled).
    VaultNotActive = 3,
    /// Timestamp constraint violated (e.g. redirect before end_timestamp, or invalid time window).
    InvalidTimestamp = 4,
    /// Validation is no longer allowed because current time is at or past end_timestamp.
    MilestoneExpired = 5,
    /// Vault is in an invalid status for the requested operation.
    InvalidStatus = 6,
    /// Amount must be positive (e.g. create_vault amount <= 0).
    InvalidAmount = 7,
    /// start_timestamp must be strictly less than end_timestamp.
    InvalidTimestamps = 8,
    /// Vault duration (end − start) exceeds MAX_VAULT_DURATION.
    DurationTooLong = 9,
}

/// Maximum allowed vault duration: 365 days in seconds.
const MAX_VAULT_DURATION: u64 = 31_536_000;

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub token: Address,
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataKey {
    Vault(u32),
    NextId,
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------
#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved token transfer to this contract.
    pub fn create_vault(
        env: Env,
        token: Address,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> u32 {
        creator.require_auth();

        if amount <= 0 {
            return Err(Error::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(Error::InvalidAmount);
        }

        // Validate that start_timestamp is strictly before end_timestamp.
        if end_timestamp <= start_timestamp {
            return Err(Error::InvalidTimestamps);
        }

        if end_timestamp - start_timestamp > MAX_VAULT_DURATION {
            return Err(Error::DurationTooLong);
        }

        // Pull USDC from creator into this contract.
        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(&creator, &env.current_contract_address(), &amount);

        let mut vault_count: u32 = env
            .storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0);
        let vault_id = vault_count;
        vault_count += 1;
        env.storage()
            .instance()
            .set(&DataKey::NextId, &(next_id + 1));
        let vault = ProductivityVault {
            token: token.clone(),
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);
        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .unwrap_or_else(|| panic!("vault not found"));
        vault.creator.require_auth();
        if vault.status != VaultStatus::Active {
            panic!("vault not active");
        }
        let contract = env.current_contract_address();
        let amount = vault.amount;
        let creator = vault.creator.clone();
        let token = vault.token.clone();
        let token_client = token::Client::new(&env, &token);
        token_client.transfer(&contract, &creator, &amount);
        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "vault_cancelled"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use soroban_sdk::testutils::Address as _;
    use soroban_sdk::{contract, contractimpl, contracttype, token, String};

    #[contracttype]
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum MockTokenKey {
        Balance(Address),
        Allowance(Address, Address),
    }

    #[contract]
    pub struct MockToken;

    #[contractimpl]
    impl MockToken {
        pub fn mint(env: Env, to: Address, amount: i128) {
            let balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(balance + amount));
        }

        pub fn balance(env: Env, id: Address) -> i128 {
            env.storage()
                .instance()
                .get(&MockTokenKey::Balance(id))
                .unwrap_or(0)
        }

        pub fn approve(
            env: Env,
            from: Address,
            spender: Address,
            amount: i128,
            _expiration_ledger: u32,
        ) {
            env.storage()
                .instance()
                .set(&MockTokenKey::Allowance(from, spender), &amount);
        }

        pub fn allowance(env: Env, from: Address, spender: Address) -> i128 {
            env.storage()
                .instance()
                .get(&MockTokenKey::Allowance(from, spender))
                .unwrap_or(0)
        }

        pub fn transfer(env: Env, from: Address, to: Address, amount: i128) {
            from.require_auth();
            let from_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            let to_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(from_balance - amount));
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(to_balance + amount));
        }

        pub fn transfer_from(env: Env, spender: Address, from: Address, to: Address, amount: i128) {
            spender.require_auth();
            let allow: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Allowance(from.clone(), spender.clone()))
                .unwrap_or(0);
            if allow < amount {
                panic!("insufficient allowance");
            }
            env.storage().instance().set(
                &MockTokenKey::Allowance(from.clone(), spender),
                &(allow - amount),
            );
            let from_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            let to_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(from_balance - amount));
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(to_balance + amount));
        }

        let vault_id = setup.create_default_vault();

        let vault_state = client.get_vault_state(&vault_id);
        assert!(vault_state.is_some());

        let vault = vault_state.unwrap();
        assert_eq!(vault.creator, setup.creator);
        assert_eq!(vault.amount, setup.amount);
        assert_eq!(vault.start_timestamp, setup.start_timestamp);
        assert_eq!(vault.end_timestamp, setup.end_timestamp);
        assert_eq!(vault.milestone_hash, setup.milestone_hash());
        assert_eq!(vault.verifier, Some(setup.verifier));
        assert_eq!(vault.success_destination, setup.success_dest);
        assert_eq!(vault.failure_destination, setup.failure_dest);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    /// Issue #42: milestone_hash passed to create_vault is stored and returned by get_vault_state.
    #[test]
    fn test_milestone_hash_storage_and_retrieval() {
        let setup = TestSetup::new();
        let client = setup.client();

        let custom_hash = BytesN::from_array(&setup.env, &[0xab; 32]);
        setup.env.ledger().set_timestamp(setup.start_timestamp);

        let vault_id = client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &custom_hash,
            &Some(setup.verifier.clone()),
            &setup.success_dest,
            &setup.failure_dest,
        );

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.milestone_hash, custom_hash);
    }

    #[test]
    fn test_create_vault_invalid_amount_returns_error() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &0i128,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_err(),
            "create_vault with amount 0 should return InvalidAmount"
        );
    }

    #[test]
    fn test_create_vault_invalid_timestamps_returns_error() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000u64,
            &1000u64,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_err(),
            "create_vault with start >= end should return InvalidTimestamps"
        );
    }

    #[test]
    fn test_create_vault_rejects_duration_above_max() {
        let setup = TestSetup::new();
        let client = setup.client();

        let start = 1_000u64;
        let end = start + MAX_VAULT_DURATION + 1; // 1 second over the limit

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &start,
            &end,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_err(),
            "create_vault with duration > MAX_VAULT_DURATION should return DurationTooLong"
        );
    }

    #[test]
    fn test_create_vault_accepts_duration_at_max() {
        let setup = TestSetup::new();
        let client = setup.client();

        let start = 1_000u64;
        let end = start + MAX_VAULT_DURATION; // exactly at the limit

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &start,
            &end,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_ok(),
            "create_vault with duration == MAX_VAULT_DURATION should succeed"
        );
    }

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Advance ledger to exactly end_timestamp
        setup.env.ledger().set_timestamp(setup.end_timestamp);

        // Try to validate milestone - should fail with MilestoneExpired
        let result = client.try_validate_milestone(&vault_id);
        assert!(result.is_err());

        // Advance ledger past end_timestamp
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        // Try to validate milestone - should also fail
        let result = client.try_validate_milestone(&vault_id);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Set time to just before end
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);

        let success = client.validate_milestone(&vault_id);
        assert!(success);

        let vault = client.get_vault_state(&vault_id).unwrap();
        // Validation now sets milestone_validated, NOT status = Completed
        assert!(vault.milestone_validated);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    /// Issue #14: When verifier is None, only creator may validate. Creator succeeds.
    #[test]
    fn test_validate_milestone_verifier_none_creator_succeeds() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);

        let result = client.validate_milestone(&vault_id);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.verifier, None);
    }

    /// Issue #14: When verifier is None, release_funds after deadline (no validation) still works.
    #[test]
    fn test_release_funds_verifier_none_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_release_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_release_funds(&999, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_milestone_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_validate_milestone(&999);
        assert!(result.is_err());
    }

    #[test]
    fn test_redirect_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_redirect_funds(&999, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_equal_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000,
            &1000, // start == end
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_greater_than_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &2000,
            &1000, // start > end
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    // -----------------------------------------------------------------------
    // Original branch tests (adapted for new signature and Results)
    // -----------------------------------------------------------------------

    #[test]
    fn test_create_vault_increments_id() {
        let setup = TestSetup::new();

        // Mint extra USDC for second vault.
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);

        let id_a = setup.create_default_vault();
        let id_b = setup.create_default_vault();
        assert_ne!(id_a, id_b, "vault IDs must be distinct");
        assert_eq!(id_b, id_a + 1);
    }

    #[test]
    fn test_release_funds_after_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Validate milestone.
        client.validate_milestone(&vault_id);

        let usdc = setup.usdc_client();
        let success_before = usdc.balance(&setup.success_dest);

        // Release.
        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        // Success destination received the funds.
        let success_after = usdc.balance(&setup.success_dest);
        assert_eq!(success_after - success_before, setup.amount);

        // Vault status is Completed.
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// After `release_funds`, the success destination balance must increase
    /// by the vault amount and the contract's USDC balance must decrease
    /// by the same amount (i.e., funds leave the contract and arrive at
    /// the success destination).
    #[test]
    fn test_release_funds_updates_contract_and_success_balances() {
        let setup = TestSetup::new();
        let client = setup.client();

        // Create vault at start_timestamp.
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Validate milestone so we can release before the deadline.
        client.validate_milestone(&vault_id);

        let usdc = setup.usdc_client();

        // Contract holds the locked funds after vault creation.
        let contract_before = usdc.balance(&setup.contract_id);
        let success_before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let contract_after = usdc.balance(&setup.contract_id);
        let success_after = usdc.balance(&setup.success_dest);

        // Success destination gains the vault amount.
        assert_eq!(success_after - success_before, setup.amount);
        // Contract balance decreases by the same vault amount.
        assert_eq!(contract_before - contract_after, setup.amount);
    }

    #[test]
    fn test_release_funds_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Advance ledger PAST end_timestamp.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_double_release_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        client.release_funds(&vault_id, &setup.usdc_token);
        // Second call — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_release_cancelled_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.cancel_vault(&vault_id, &setup.usdc_token);
        // Release after cancel — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_release_not_validated_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Neither validated nor past deadline — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_validate_milestone_on_completed_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);

        // Validate after completion — must error.
        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    #[test]
    fn test_redirect_funds_after_deadline_without_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.failure_dest);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.failure_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    /// After `redirect_funds`, the failure destination balance must increase
    /// by the vault amount and the contract's USDC balance must decrease
    /// by the same amount (i.e., funds leave the contract and arrive at
    /// the failure destination).
    #[test]
    fn test_redirect_funds_updates_contract_and_failure_balances() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Move past the deadline without validation so redirect is allowed.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();

        let contract_before = usdc.balance(&setup.contract_id);
        let failure_before = usdc.balance(&setup.failure_dest);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let contract_after = usdc.balance(&setup.contract_id);
        let failure_after = usdc.balance(&setup.failure_dest);

        // Failure destination gains the vault amount.
        assert_eq!(failure_after - failure_before, setup.amount);
        // Contract balance decreases by the same vault amount.
        assert_eq!(contract_before - contract_after, setup.amount);
    }

    #[test]
    fn test_redirect_funds_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Still before deadline — must error.
        assert!(client
            .try_redirect_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_double_redirect_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        // Second redirect — must error (vault already Failed).
        assert!(client
            .try_redirect_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_cancel_vault_returns_funds_to_creator() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.creator);

        let result = client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.creator) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    // -----------------------------------------------------------------------
    // More upstream tests migrated
    // -----------------------------------------------------------------------

    #[test]
    #[should_panic]
    fn test_create_vault_fails_without_auth() {
        let env = Env::default();
        let usdc_token = Address::generate(&env);
        let creator = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[0u8; 32]);

        // DO NOT authorize the creator
        let _vault_id = DisciplrVault::create_vault(
            env,
            usdc_token,
            creator,
            1000,
            100,
            200,
            milestone_hash,
            Some(verifier),
            success_addr,
            failure_addr,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_zero_amount() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &0i128,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_amount_above_max_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        let amount_above_max = MAX_AMOUNT
            .checked_add(1)
            .expect("MAX_AMOUNT + 1 overflowed");

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &amount_above_max,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic]
    fn test_create_vault_caller_differs_from_creator() {
        let env = Env::default();
        let usdc_token = Address::generate(&env);
        let creator = Address::generate(&env);
        let different_caller = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[1u8; 32]);

        different_caller.require_auth();

        pub fn burn_from(env: Env, spender: Address, from: Address, amount: i128) {
            spender.require_auth();
            let allow: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Allowance(from.clone(), spender.clone()))
                .unwrap_or(0);
            if allow < amount {
                panic!("insufficient allowance");
            }
            env.storage().instance().set(
                &MockTokenKey::Allowance(from.clone(), spender),
                &(allow - amount),
            );
            let balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(balance - amount));
        }

        pub fn decimals(env: Env) -> u32 {
            let _ = env;
            6
        }

        pub fn name(env: Env) -> String {
            String::from_str(&env, "Test Token")
        }

        pub fn symbol(env: Env) -> String {
            String::from_str(&env, "TEST")
        }
    }

    /// cancel_vault returns funds to creator and sets status to Cancelled.
    #[test]
    fn cancel_vault_returns_funds_to_creator_and_sets_cancelled() {
        let env = Env::default();
        let token_id = env.register(test::MockToken, ());
        let vault_contract_id = env.register(DisciplrVault, ());

        let creator = Address::generate(&env);
        let amount: i128 = 10_000_000; // 10 units with 6 decimals
        let start_ts: u64 = 1000;
        let end_ts: u64 = 2000;
        let milestone_hash = BytesN::from_array(&env, &[0u8; 32]);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        // Mint tokens to creator and approve vault contract to spend
        let mock_token = test::MockTokenClient::new(&env, &token_id);
        mock_token.mint(&creator, &amount);
        let exp_ledger = env.ledger().sequence() + 1000;
        mock_token.approve(&creator, &vault_contract_id, &amount, &exp_ledger);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract_id);
        let token_client = token::Client::new(&env, &token_id);

        assert_eq!(
            token_client.balance(&creator),
            amount,
            "creator should have minted amount before create_vault"
        );

        // Mock auth so creator.require_auth() and token transfer_from(spender) succeed in tests
        env.mock_all_auths();

        // Create vault as creator (funds pulled from creator to contract)
        let vault_id = vault_client.create_vault(
            &token_id,
            &creator,
            &amount,
            &start_ts,
            &end_ts,
            &milestone_hash,
            &None::<Address>,
            &success_dest,
            &failure_dest,
        );

        assert_eq!(
            token_client.balance(&creator),
            0,
            "creator balance should be 0 after create_vault (funds locked in vault)"
        );

        // Cancel vault as creator (returns funds to creator)
        vault_client.cancel_vault(&vault_id);

        let creator_balance_after = token_client.balance(&creator);
        assert_eq!(
            creator_balance_after, amount,
            "cancel_vault must return vault amount to creator"
        );

        let state = vault_client.get_vault_state(&vault_id);
        let vault = state.expect("vault should exist");
        assert_eq!(
            vault.status,
            VaultStatus::Cancelled,
            "vault status must be Cancelled after cancel_vault"
        );
        assert_eq!(vault.creator, creator);
        assert_eq!(vault.amount, amount);
    }

    #[test]
    fn test_vaultstatus_enum_values() {
        // Verify VaultStatus enum has correct discriminant values
        assert_eq!(VaultStatus::Active as u32, 0);
        assert_eq!(VaultStatus::Completed as u32, 1);
        assert_eq!(VaultStatus::Failed as u32, 2);
        assert_eq!(VaultStatus::Cancelled as u32, 3);
    }

    #[test]
    fn test_vaultstatus_enum_ordering() {
        // Verify VaultStatus can be compared
        assert!(VaultStatus::Active == VaultStatus::Active);
        assert!(VaultStatus::Active != VaultStatus::Completed);
    }

    #[test]
    fn test_productivity_vault_struct_creation() {
        // Test that ProductivityVault struct can be created
        // This verifies the struct is properly defined with all expected fields
        let _vault = ProductivityVault {
            creator: Address::generate(&Env::default()),
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash: {
                let env = Env::default();
                let mut data = [0u8; 32];
                data[0] = 0xFF;
                BytesN::<32>::from_array(&env, &data)
            },
            verifier: None,
            success_destination: Address::generate(&Env::default()),
            failure_destination: Address::generate(&Env::default()),
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_validate_milestone_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Try to validate a non-existent vault (returns error, but doesn't crash)
        let result = client.try_validate_milestone(&42u32);
        // Result could be error since vault doesn't exist, just verify it's a Result
        let _ = result;
    }

    #[test]
    fn test_release_funds_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let usdc_token = Address::generate(&env);

        // Try to release funds for non-existent vault (returns error, but doesn't crash)
        let result = client.try_release_funds(&0u32, &usdc_token);
        // Result could be error since vault doesn't exist, just verify it's a Result
        let _ = result;
    }

    #[test]
    fn test_redirect_funds_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let usdc_token = Address::generate(&env);

        // Try to redirect funds for non-existent vault (returns error, but doesn't crash)
        let result = client.try_redirect_funds(&0u32, &usdc_token);
        // Result could be error since vault doesn't exist, just verify it's a Result
        let _ = result;
    }

    #[test]
    fn test_cancel_vault_returns_bool() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let usdc_token = Address::generate(&env);

        // Try to cancel non-existent vault (returns error, but doesn't crash)
        let result = client.try_cancel_vault(&0u32, &usdc_token);
        // Result could be error since vault doesn't exist, just verify it's a Result
        let _ = result;
    }

    #[test]
    fn test_get_vault_state_returns_option() {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let result = client.get_vault_state(&0u32);
        // Non-existent vault returns None
        assert_eq!(result, None);
    }

    #[test]
    fn test_vaultstatus_clone_and_copy() {
        let status1 = VaultStatus::Active;
        let status2 = status1; // Should copy
        assert_eq!(status1, status2);
    }

    #[test]
    fn test_vault_created_event_symbol_value() {
        let env = Env::default();

        let env_clone = env.clone();
        let symbol = Symbol::new(&env_clone, "vault_created");

        let _s = symbol;
    }

    #[test]
    fn test_milestone_validated_event_symbol_value() {
        let env = Env::default();

        let env_clone = env.clone();
        let symbol = Symbol::new(&env_clone, "milestone_validated");

        // Verify symbol can be created
        let _s = symbol;
    }

    #[test]
    fn test_contract_types_are_public() {
        // Verify contract types are publicly accessible
        let _status: VaultStatus = VaultStatus::Active;
        let _enum_val = VaultStatus::Completed;
    }

    #[test]
    fn test_vault_status_all_variants_compile() {
        // Verify all VaultStatus variants exist as expected
        match VaultStatus::Active {
            VaultStatus::Active => (),
            VaultStatus::Completed => (),
            VaultStatus::Failed => (),
            VaultStatus::Cancelled => (),
        }
    }

    #[test]
    fn test_milestone_validated_function_signature() {
        // Tests that the validate_milestone function exists with expected parameters
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Verify function can be called through client
        let _result = client.try_validate_milestone(&123u32);
        // Result could be error since vault doesn't exist, just verify it exists
    }

    #[test]
    fn test_address_generation_in_tests() {
        // Verify test utilities work - Address generation for testing
        let env = Env::default();
        let addr1 = Address::generate(&env);
        let addr2 = Address::generate(&env);

        // Different addresses should be generated
        assert_ne!(addr1, addr2);
    }

    #[test]
    fn test_bytesn32_creation() {
        // Verify BytesN<32> can be created for milestone_hash
        let env = Env::default();
        let mut data = [0u8; 32];
        data[0] = 0xFF;
        data[31] = 0xAA;

        let _bytes = BytesN::<32>::from_array(&env, &data);
    }

    #[test]
    fn test_vaultstatus_default_is_active() {
        // Verify that Active is the first enum variant (index 0)
        assert_eq!(VaultStatus::Active as i32, 0);
    }

    #[test]
    fn test_productivity_vault_with_verifier() {
        let env = Env::default();
        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let data = [0u8; 32];
        let milestone_hash = BytesN::<32>::from_array(&env, &data);

        let _vault = ProductivityVault {
            creator,
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash,
            verifier: Some(verifier),
            success_destination: success_dest,
            failure_destination: failure_dest,
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_productivity_vault_without_verifier() {
        let env = Env::default();
        let creator = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let data = [0u8; 32];
        let milestone_hash = BytesN::<32>::from_array(&env, &data);

        let _vault = ProductivityVault {
            creator,
            amount: 1000i128,
            start_timestamp: 100u64,
            end_timestamp: 200u64,
            milestone_hash,
            verifier: None,
            success_destination: success_dest,
            failure_destination: failure_dest,
            status: VaultStatus::Active,
            milestone_validated: false,
        };
    }

    #[test]
    fn test_option_address_some_variant() {
        let env = Env::default();
        let verifier = Address::generate(&env);
        let option_verifier: Option<Address> = Some(verifier);
        assert!(option_verifier.is_some());
    }

    #[test]
    fn test_option_address_none_variant() {
        let option_verifier: Option<Address> = None;
        assert!(option_verifier.is_none());
    }
}
