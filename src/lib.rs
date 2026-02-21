#![no_std]

use soroban_sdk::{contract, contractimpl, contracttype, token, Address, BytesN, Env, Symbol};

#[contracttype]
#[derive(Clone, Debug)]
pub enum DataKey {
    TokenAddress,
    VaultCount,
    Vault(u32),
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
#[derive(Clone, Debug)]
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

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // ── Functions ──────────────────────────────────────────────────────
    // initialize       — Set USDC token address (one-time).
    // create_vault     — Lock USDC into a new productivity vault.
    // validate_milestone — Verifier confirms milestone; releases funds to success dest.
    // redirect_funds   — After deadline, sends funds to failure dest.
    // cancel_vault     — Creator cancels an active vault and reclaims funds.
    // get_vault_state  — Read vault by ID.
    // vault_count      — Total vaults created.
    // ──────────────────────────────────────────────────────────────────

    /// Set USDC token address; must be called once before creating vaults.
    pub fn initialize(env: Env, token_address: Address) {
        if env.storage().instance().has(&DataKey::TokenAddress) {
            panic!("already initialized");
        }
        env.storage()
            .instance()
            .set(&DataKey::TokenAddress, &token_address);
        env.storage().instance().set(&DataKey::VaultCount, &0u32);
    }

    /// Lock USDC into a new vault; returns the vault ID.
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
        assert!(amount > 0, "amount must be positive");
        assert!(end_timestamp > start_timestamp, "end must be after start");

        let vault_id: u32 = env
            .storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0);
        env.storage()
            .instance()
            .set(&DataKey::VaultCount, &(vault_id + 1));

        let token_address: Address = env
            .storage()
            .instance()
            .get(&DataKey::TokenAddress)
            .expect("contract not initialized");
        token::Client::new(&env, &token_address).transfer(
            &creator,
            &env.current_contract_address(),
            &amount,
        );

        let vault = ProductivityVault {
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
            .persistent()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), ());

        vault_id
    }

    /// Validate milestone completion; transfers USDC to success destination.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&DataKey::Vault(vault_id))
            .expect("vault not found");

        assert!(vault.status == VaultStatus::Active, "vault is not active");
        assert!(
            env.ledger().timestamp() <= vault.end_timestamp,
            "deadline has passed"
        );

        match &vault.verifier {
            Some(v) => v.require_auth(),
            None => vault.creator.require_auth(),
        }

        vault.status = VaultStatus::Completed;
        env.storage()
            .persistent()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_address: Address = env
            .storage()
            .instance()
            .get(&DataKey::TokenAddress)
            .unwrap();
        token::Client::new(&env, &token_address).transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        true
    }

    /// After deadline, redirect funds to failure destination (callable by anyone).
    pub fn redirect_funds(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&DataKey::Vault(vault_id))
            .expect("vault not found");

        assert!(vault.status == VaultStatus::Active, "vault is not active");
        assert!(
            env.ledger().timestamp() > vault.end_timestamp,
            "deadline has not passed yet"
        );

        vault.status = VaultStatus::Failed;
        env.storage()
            .persistent()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_address: Address = env
            .storage()
            .instance()
            .get(&DataKey::TokenAddress)
            .unwrap();
        token::Client::new(&env, &token_address).transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "funds_redirected"), vault_id), ());
        true
    }

    /// Creator cancels an active vault and reclaims locked USDC.
    pub fn cancel_vault(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&DataKey::Vault(vault_id))
            .expect("vault not found");

        assert!(vault.status == VaultStatus::Active, "vault is not active");
        vault.creator.require_auth();

        vault.status = VaultStatus::Cancelled;
        env.storage()
            .persistent()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_address: Address = env
            .storage()
            .instance()
            .get(&DataKey::TokenAddress)
            .unwrap();
        token::Client::new(&env, &token_address).transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        true
    }

    /// Read vault state by ID, or None if it doesn't exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().persistent().get(&DataKey::Vault(vault_id))
    }

    /// Total number of vaults created.
    pub fn vault_count(env: Env) -> u32 {
        env.storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0)
    }
}

#[cfg(test)]
mod test;
