/-
  EvmAsm.Stateless.State.TxState

  Per-transaction rollback frame. Layered over BlockState during
  one tx's execution; commits or discards on tx finish.

  Mirrors Python's `TransactionState` in
  `forks/amsterdam/state_tracker.py`.

  ## Fields

      class TransactionState:
          block_state       : BlockState        # parent overlay
          account_changes   : dict[Address, Account]
          storage_changes   : dict[(Address, Slot), Value]
          code_changes      : dict[CodeHash, Bytes]
          # Snapshot taken on entry; reverted-to on REVERT / failure

  ## Commit / revert

  - **Commit**: bubble all three change dicts up to the BlockState
    parent. Increase the parent's `accessed_*` sets accordingly.
  - **Revert**: drop the entire TxState. The parent BlockState is
    unchanged.

  Used in nested call frames too (each SSTORE'd slot is checkpointed;
  on REVERT inside a CALL, the inner frame's TxState dies but the
  outer caller's TxState stays).

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.TxState

-- TODO(stateless-state): expose TxState record + snapshot /
-- commit / revert helpers.

end EvmAsm.Stateless.State.TxState
