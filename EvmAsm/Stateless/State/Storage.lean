/-
  EvmAsm.Stateless.State.Storage

  Per-account storage trie: maps `slot : U256` to `value : U256`.
  Two top-level operations:

  - `get_storage(address, slot) -> U256`
       1. Look up account via `state.get_account(address)`.
       2. Read account.storage_root.
       3. `value = MPT.Get(storage_root, keccak256(slot))`.
       4. Return RLP-decoded U256 (or 0 on missing).
  - `set_storage(address, slot, value) -> ()`
       Tracked in BlockState's `storage_changes` overlay. The
       actual MPT mutation happens at end-of-block in
       `compute_state_root_and_trie_changes`.

  ## Copy-on-write tracker

  Each tx maintains a fresh dict[(address, slot) -> value]. On
  REVERT the tx-level entries are discarded; on commit they
  bubble up to BlockState.

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.Storage

-- TODO(stateless-state): expose `get_storage`, `set_storage`,
-- and the CoW tracker.

end EvmAsm.Stateless.State.Storage
