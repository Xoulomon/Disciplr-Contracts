#![no_std]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, token, Address, BytesN, Env, Symbol,
};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    VaultNotFound = 1,
    NotAuthorized = 2,
    VaultNotActive = 3,
    InvalidTimestamp = 4,
    MilestoneExpired = 5,
    // Add InvalidStatus from our branch implementation since some parts rely on it
    InvalidStatus = 6,
}

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

/// Core vault record persisted in contract storage.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProductivityVault {
    /// Address that created (and funded) the vault.
    pub creator: Address,
    /// USDC amount locked in the vault (in stroops / smallest unit).
    pub amount: i128,
    /// Ledger timestamp when the commitment period starts.
    pub start_timestamp: u64,
    /// Ledger timestamp after which deadline-based release is allowed.
    pub end_timestamp: u64,
    /// Hash representing the milestone the creator commits to.
    pub milestone_hash: BytesN<32>,
    /// Optional designated verifier; if `None` any party may validate after deadline.
    pub verifier: Option<Address>,
    /// Funds go here on success.
    pub success_destination: Address,
    /// Funds go here on failure/redirect.
    pub failure_destination: Address,
    /// Current lifecycle status.
    pub status: VaultStatus,
    /// Set to `true` once the verifier (or authorised party) calls `validate_milestone`.
    /// Used by `release_funds` to allow early release before the deadline.
    pub milestone_validated: bool,
}

// ---------------------------------------------------------------------------
// Storage keys
// ---------------------------------------------------------------------------

#[contracttype]
#[derive(Clone)]
pub enum DataKey {
    Vault(u32),
    VaultCount,
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // -----------------------------------------------------------------------
    // create_vault
    // -----------------------------------------------------------------------

    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    ///
    /// # Validation Rules
    /// - Requires `start_timestamp < end_timestamp`. If `start_timestamp >= end_timestamp`, the function panics
    ///   because a 0-length or reverse-time window is invalid.
    pub fn create_vault(
        env: Env,
        usdc_token: Address,
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

        // Validate that start_timestamp is strictly before end_timestamp.
        // A vault with start >= end has no valid time window and must be rejected.
        if end_timestamp <= start_timestamp {
            panic!("create_vault: start_timestamp must be strictly less than end_timestamp");
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
            .set(&DataKey::VaultCount, &vault_count);

        let vault = ProductivityVault {
            creator,
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
            milestone_validated: false,
        };

        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault.clone(),
        );

        vault_id
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Auth check for verifier
        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

        // Timestamp check: rejects when current time >= end_timestamp
        if env.ledger().timestamp() >= vault.end_timestamp {
            return Err(Error::MilestoneExpired);
        }

        vault.milestone_validated = true;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // release_funds
    // -----------------------------------------------------------------------

    /// Release vault funds to `success_destination`.
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive); // Or InvalidStatus as appropriate
        }

        // Check release conditions.
        let now = env.ledger().timestamp();
        let deadline_reached = now >= vault.end_timestamp;
        let validated = vault.milestone_validated;

        if !validated && !deadline_reached {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    /// Redirect funds to `failure_destination` (e.g. after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }

        // If milestone was validated the funds should go to success, not failure.
        if vault.milestone_validated {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_redirected"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    /// Return current vault state, or `None` if the vault does not exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, Ledger},
        token::{StellarAssetClient, TokenClient},
        Address, BytesN, Env,
    };

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    struct TestSetup {
        env: Env,
        contract_id: Address,
        usdc_token: Address,
        creator: Address,
        verifier: Address,
        success_dest: Address,
        failure_dest: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
    }

    impl TestSetup {
        fn new() -> Self {
            let env = Env::default();
            env.mock_all_auths();

            // Deploy USDC mock token.
            let usdc_admin = Address::generate(&env);
            let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
            let usdc_addr = usdc_token.address();
            let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

            // Actors.
            let creator = Address::generate(&env);
            let verifier = Address::generate(&env);
            let success_dest = Address::generate(&env);
            let failure_dest = Address::generate(&env);

            // Mint USDC to creator.
            let amount: i128 = 1_000_000; // 1 USDC (6 decimals)
            usdc_asset.mint(&creator, &amount);

            // Deploy contract.
            let contract_id = env.register(DisciplrVault, ());

            TestSetup {
                env,
                contract_id,
                usdc_token: usdc_addr,
                creator,
                verifier,
                success_dest,
                failure_dest,
                amount,
                start_timestamp: 100,
                end_timestamp: 1_000,
            }
        }

        fn client(&self) -> DisciplrVaultClient<'_> {
            DisciplrVaultClient::new(&self.env, &self.contract_id)
        }

        fn usdc_client(&self) -> TokenClient<'_> {
            TokenClient::new(&self.env, &self.usdc_token)
        }

        fn milestone_hash(&self) -> BytesN<32> {
            BytesN::from_array(&self.env, &[1u8; 32])
        }

        fn create_default_vault(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &self.start_timestamp,
                &self.end_timestamp,
                &self.milestone_hash(),
                &Some(self.verifier.clone()),
                &self.success_dest,
                &self.failure_dest,
            )
        }
    }

    // -----------------------------------------------------------------------
    // Upstream Tests (Migrated & Merged)
    // -----------------------------------------------------------------------

    #[test]
    fn get_vault_state_returns_some_with_matching_fields() {
        let setup = TestSetup::new();
        let client = setup.client();

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

    #[test]
    fn test_release_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_release_funds(&999, &setup.usdc_token);
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
    #[should_panic(
        expected = "create_vault: start_timestamp must be strictly less than end_timestamp"
    )]
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
    #[should_panic(
        expected = "create_vault: start_timestamp must be strictly less than end_timestamp"
    )]
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

        // Neither validated nor past deadline — must panic.
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
}
