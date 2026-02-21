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
    Vault(u32),
    VaultCount,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
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

        if end_timestamp <= start_timestamp {
            panic!("end_timestamp must be greater than start_timestamp");
        }

        let mut vault_count: u32 = env.storage().instance().get(&DataKey::VaultCount).unwrap_or(0);
        let vault_id = vault_count;
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
        
        env.storage().instance().set(&DataKey::Vault(vault_id), &vault);

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

        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);

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
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Only allow release if validated (status would be Completed) or maybe this is a redundant method
        // For now, let's just make it a stub that updates status if called.
        // In a real impl, this would handle the actual USDC transfer.
        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);
        Ok(true)
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
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

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);
        Ok(true)
    }

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32) -> Result<bool, Error> {
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

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);
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
    use soroban_sdk::testutils::{Address as _, Ledger};

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let start_time = 1000;
        let end_time = 2000;
        
        env.ledger().set_timestamp(start_time);

        // Sign for create_vault
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Advance ledger to exactly end_timestamp
        env.ledger().set_timestamp(end_time);

        // Try to validate milestone - should fail with MilestoneExpired (error code 5)
        // Try to validate milestone - should fail with MilestoneExpired
        let _result = client.try_validate_milestone(&vault_id);
        assert!(_result.is_err());

        // Advance ledger past end_timestamp
        env.ledger().set_timestamp(end_time + 1);

        // Try to validate milestone - should also fail
        let _result = client.try_validate_milestone(&vault_id);
        assert!(_result.is_err());
    }

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let start_time = 1000;
        let end_time = 2000;
        
        env.ledger().set_timestamp(start_time);
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Set time to just before end
        env.ledger().set_timestamp(end_time - 1);

        let success = client.validate_milestone(&vault_id);
        assert!(success);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }
}
