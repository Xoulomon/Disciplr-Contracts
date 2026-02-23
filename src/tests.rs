use super::*;
use soroban_sdk::{
    testutils::{Address as _, Ledger, LedgerInfo},
    Env,
};

// ── Helpers ───────────────────────────────────────────────────────────

/// Spin up a test environment and register the contract.
fn setup() -> (Env, soroban_sdk::Address) {
    let env = Env::default();
    env.mock_all_auths();
    let contract_id = env.register(DisciplrVault, ());
    (env, contract_id)
}

/// Build a standard vault hash (32 zero bytes).
fn zero_hash(env: &Env) -> BytesN<32> {
    BytesN::from_array(env, &[0u8; 32])
}

/// Advance the ledger timestamp past `end_timestamp`.
fn advance_past_deadline(env: &Env, end_timestamp: u64) {
    env.ledger().set(LedgerInfo {
        timestamp: end_timestamp + 1,
        protocol_version: 22,
        sequence_number: env.ledger().sequence(),
        network_id: Default::default(),
        base_reserve: 10,
        min_temp_entry_ttl: 16,
        min_persistent_entry_ttl: 100_000,
        max_entry_ttl: 10_000_000,
    });
}

/// Create a vault with sensible defaults and return (client, vault_id).
fn create_default_vault<'a>(
    env: &'a Env,
    contract_id: &'a soroban_sdk::Address,
) -> (DisciplrVaultClient<'a>, u32) {
    let client = DisciplrVaultClient::new(env, contract_id);
    let creator = Address::generate(env);
    let success = Address::generate(env);
    let failure = Address::generate(env);
    let vault_id = client.create_vault(
        &creator,
        &1_000_000i128,
        &1_000u64,
        &2_000u64,
        &zero_hash(env),
        &None,
        &success,
        &failure,
    );
    (client, vault_id)
}

// ── create_vault ──────────────────────────────────────────────────────

#[test]
fn test_create_vault_assigns_sequential_ids() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    let creator = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    let id0 = client.create_vault(
        &creator,
        &100i128,
        &0u64,
        &1u64,
        &zero_hash(&env),
        &None,
        &success,
        &failure,
    );
    let id1 = client.create_vault(
        &creator,
        &200i128,
        &0u64,
        &1u64,
        &zero_hash(&env),
        &None,
        &success,
        &failure,
    );

    assert_eq!(id0, 0);
    assert_eq!(id1, 1);
}

#[test]
fn test_create_vault_initial_status_active() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
}

// ── release_funds ─────────────────────────────────────────────────────

#[test]
fn test_release_funds_succeeds_when_active() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    assert!(client.release_funds(&vault_id));
    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Completed);
}

#[test]
fn test_release_funds_sets_status_completed() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    client.release_funds(&vault_id);
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Completed
    );
}

/// **Core idempotency test**: calling release_funds twice must fail on the
/// second attempt because the vault is already Completed.
#[test]
#[should_panic]
fn test_double_release_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    client.release_funds(&vault_id); // first call succeeds
    client.release_funds(&vault_id); // second call must panic
}

// ── redirect_funds ────────────────────────────────────────────────────

#[test]
fn test_redirect_funds_succeeds_after_deadline() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    advance_past_deadline(&env, 2_000);
    assert!(client.redirect_funds(&vault_id));
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Failed
    );
}

#[test]
#[should_panic]
fn test_redirect_funds_rejected_before_deadline() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    // Do NOT advance ledger — timestamp is below end_timestamp.
    client.redirect_funds(&vault_id);
}

/// **Core idempotency test**: double redirect must fail.
#[test]
#[should_panic]
fn test_double_redirect_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    advance_past_deadline(&env, 2_000);
    client.redirect_funds(&vault_id); // succeeds
    client.redirect_funds(&vault_id); // must panic
}

// ── Cross-function idempotency (release then redirect, redirect then release) ──

/// Release then redirect: redirect must be rejected because vault is Completed.
#[test]
#[should_panic]
fn test_release_then_redirect_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    client.release_funds(&vault_id);
    advance_past_deadline(&env, 2_000);
    client.redirect_funds(&vault_id); // must panic — already Completed
}

/// Redirect then release: release must be rejected because vault is Failed.
#[test]
#[should_panic]
fn test_redirect_then_release_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    advance_past_deadline(&env, 2_000);
    client.redirect_funds(&vault_id); // succeeds
    client.release_funds(&vault_id); // must panic — already Failed
}

// ── cancel_vault ──────────────────────────────────────────────────────

#[test]
fn test_cancel_vault_sets_cancelled() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    assert!(client.cancel_vault(&vault_id));
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Cancelled
    );
}

#[test]
#[should_panic]
fn test_double_cancel_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    client.cancel_vault(&vault_id);
    client.cancel_vault(&vault_id); // must panic
}

#[test]
#[should_panic]
fn test_release_then_cancel_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    client.release_funds(&vault_id);
    client.cancel_vault(&vault_id); // must panic — already Completed
}

// ── validate_milestone ────────────────────────────────────────────────

#[test]
fn test_validate_milestone_no_verifier() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    let caller = Address::generate(&env);
    assert!(client.validate_milestone(&vault_id, &caller));
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Completed
    );
}

#[test]
#[should_panic]
fn test_validate_milestone_twice_rejected() {
    let (env, contract_id) = setup();
    let (client, vault_id) = create_default_vault(&env, &contract_id);
    let caller = Address::generate(&env);
    client.validate_milestone(&vault_id, &caller);
    client.validate_milestone(&vault_id, &caller); // must panic
}

#[test]
fn test_validate_milestone_with_verifier() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    let vault_id = client.create_vault(
        &creator,
        &500i128,
        &0u64,
        &1_000u64,
        &zero_hash(&env),
        &Some(verifier.clone()),
        &success,
        &failure,
    );

    assert!(client.validate_milestone(&vault_id, &verifier));
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Completed
    );
}

#[test]
#[should_panic]
fn test_validate_milestone_wrong_verifier_rejected() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let impostor = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    let vault_id = client.create_vault(
        &creator,
        &500i128,
        &0u64,
        &1_000u64,
        &zero_hash(&env),
        &Some(verifier),
        &success,
        &failure,
    );

    client.validate_milestone(&vault_id, &impostor); // must panic
}

// ── get_vault_state ───────────────────────────────────────────────────

#[test]
fn test_get_vault_state_missing_returns_none() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    assert!(client.get_vault_state(&99u32).is_none());
}

// ── load_vault panics on unknown id ───────────────────────────────────

#[test]
#[should_panic]
fn test_release_unknown_vault_panics() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    client.release_funds(&99u32);
}

#[test]
#[should_panic]
fn test_redirect_unknown_vault_panics() {
    let (env, contract_id) = setup();
    let client = DisciplrVaultClient::new(&env, &contract_id);
    advance_past_deadline(&env, 0);
    client.redirect_funds(&99u32);
}
