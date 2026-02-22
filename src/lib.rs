#![no_std]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, Address, BytesN, Env, Symbol,
};

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    VaultNotFound = 1,
    NotAuthorized = 2,
    VaultNotActive = 3,
    InvalidTimestamp = 4,
    MilestoneExpired = 5,
}

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProductivityVault {
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
#[derive(Clone)]
pub enum DataKey {
    NextVaultId,
    Vault(u32),
    VaultCount,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    ///
    /// # Validation Rules
    /// - Requires `start_timestamp < end_timestamp`. If `start_timestamp >= end_timestamp`, the function panics
    ///   because a 0-length or reverse-time window is invalid.
    pub fn create_vault(
        env: Env,
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

        let mut vault_count: u32 = env.storage().instance().get(&DataKey::VaultCount).unwrap_or(0);
        let _vault_id_initial = vault_count;
        vault_count += 1;
        env.storage().instance().set(&DataKey::VaultCount, &vault_count);

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
        };

        let vault_id: u32 = env
            .storage()
            .instance()
            .get(&DataKey::NextVaultId)
            .unwrap_or(0u32);
        
        env.storage().persistent().set(&DataKey::Vault(vault_id), &vault);
        
        env.storage().instance().set(&DataKey::NextVaultId, &(vault_id + 1));

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault,
        );
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
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

        vault.status = VaultStatus::Completed;
        env.storage().persistent().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            (),
        );
        Ok(true)
    }

    /// Release funds to success destination.
    pub fn release_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Only allow release if validated (status would be Completed) or maybe this is a redundant method
        // For now, let's just make it a stub that updates status if called.
        // In a real impl, this would handle the actual USDC transfer.
        vault.status = VaultStatus::Completed;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }

        vault.status = VaultStatus::Failed;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        vault.status = VaultStatus::Cancelled;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        //This line returns None if the vault doesn't exist.
        env.storage().persistent().get(&DataKey::Vault(vault_id))
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
        testutils::{Address as _, Events, Ledger},
        Address, BytesN, Env,
    };

    // Fixture addresses used across tests.
    struct Actors {
        creator: Address,
        success_dest: Address,
        failure_dest: Address,
    }

    /// Build a fresh Soroban test environment, register the contract, and return
    /// the typed client together with pre-generated mock actor addresses.
    fn setup() -> (Env, DisciplrVaultClient<'static>, Actors) {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let actors = Actors {
            creator: Address::generate(&env),
            success_dest: Address::generate(&env),
            failure_dest: Address::generate(&env),
        };

        (env, client, actors)
    }

    /// Helper: build a default set of valid vault parameters.
    fn make_vault_args(
        env: &Env,
    ) -> (Address, i128, u64, u64, BytesN<32>, Option<Address>, Address, Address) {
        let creator        = Address::generate(env);
        let success_dest   = Address::generate(env);
        let failure_dest   = Address::generate(env);
        let verifier       = Address::generate(env);
        let milestone_hash = BytesN::from_array(env, &[1u8; 32]);
        let amount         = 1_000_000i128; // 1 USDC (6 decimals)
        let start          = 1_000_000u64;
        let end            = 2_000_000u64;

        (creator, amount, start, end, milestone_hash, Some(verifier), success_dest, failure_dest)
    }

    fn milestone_hash_helper(env: &Env) -> BytesN<32> {
        BytesN::from_array(env, &[0xabu8; 32])
    }

    #[test]
    fn test_get_vault_state_returns_none_for_unknown_vault_id() {
        // PERTAINS TO ISSUE #30: Core requirement
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let unknown_id = 888u32;
        let result = client.get_vault_state(&unknown_id);
        assert!(result.is_none(), "The contract should return None for a non-existent vault_id");
    }

    #[test]
    fn test_create_vault_emits_event_and_returns_id() {
        let env = Env::default();
        env.mock_all_auths(); 
        let contract_id = env.register(DisciplrVault, ());
        let client      = DisciplrVaultClient::new(&env, &contract_id);

        let (creator, amount, start_timestamp, end_timestamp,
             milestone_hash, verifier, success_destination, failure_destination) =
            make_vault_args(&env);

        let vault_id = client.create_vault(
            &creator, &amount, &start_timestamp, &end_timestamp,
            &milestone_hash, &verifier, &success_destination, &failure_destination,
        );

        assert_eq!(vault_id, 0u32, "vault_id should be the placeholder 0");

        let all_events = env.events().all();
        assert_eq!(all_events.len(), 1, "exactly one event should be emitted");
    }

    #[test]
    #[should_panic(expected = "create_vault: start_timestamp must be strictly less than end_timestamp")]
    fn create_vault_rejects_start_equal_end() {
        let (env, client, actors) = setup();
        client.create_vault(&actors.creator, &100_000, &1000, &1000, &milestone_hash_helper(&env), &None, &actors.success_dest, &actors.failure_dest);
    }

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let (env, client, actors) = setup();
        let start = 1000; let end = 2000;
        env.ledger().set_timestamp(start);
        let id = client.create_vault(&actors.creator, &1000, &start, &end, &milestone_hash_helper(&env), &None, &actors.success_dest, &actors.failure_dest);
        env.ledger().set_timestamp(end);
        let _result = client.try_validate_milestone(&id);
        assert!(_result.is_err());
    }

    #[test]
    #[ignore = "validation not yet implemented in create_vault"]
    fn test_create_vault_rejects_invalid_timestamps() {
        let (env, client, actors) = setup();
        let start = 1000;
        client.create_vault(&actors.creator, &1000, &start, &start, &milestone_hash_helper(&env), &None, &actors.success_dest, &actors.failure_dest);
    }
}