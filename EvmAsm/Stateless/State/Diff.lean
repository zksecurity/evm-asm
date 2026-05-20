/-
  EvmAsm.Stateless.State.Diff

  Block-level diff produced by `apply_body`. Captures the
  account/storage/code changes between pre-state and post-state.

  Mirrors Python's `BlockDiff` from `forks/amsterdam/state.py`.

      class BlockDiff:
          account_changes : dict[Address, Account]
          storage_changes : dict[(Address, Slot), Value]
          code_changes    : dict[CodeHash, Bytes]

  Built by:
  1. Running each transaction's STF over BlockState.
  2. Merging the final BlockState changes into a flat diff.

  Consumed by:
  - `StateRoot.compute_state_root_and_trie_changes(pre_state, diff)`
    -> new state_root.

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.Diff

-- TODO(stateless-state): expose `BlockDiff` record + constructor
-- from a finalised BlockState.

end EvmAsm.Stateless.State.Diff
