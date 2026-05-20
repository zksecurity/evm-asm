/-
  EvmAsm.Stateless.State.PreState

  Bundle the read-only "pre-state" picture the stateless guest
  builds from the witness:

      struct PreState {
          node_db        : NODE_DB_BUCKETS
          code_db        : CODE_DB_BUCKETS
          state_root     : Hash32   # from parent_header.state_root
      }

  Mirrors Python's `WitnessState` from
  `forks/amsterdam/witness_state.py`. The pre-state has no
  copy-on-write -- it's the immutable starting point that
  BlockState layers mutations over.

  ## Construction (during stateless guest setup)

      pre_state = PreState{
          node_db    = Stateless.Witness.NodeDb.build_node_db(...)
          code_db    = Stateless.Witness.CodeDb.build_code_db(...)
          state_root = decoded_parent_header.state_root
      }

  ## Read paths

  - `pre_state.get_account(addr)`:
      `MPT.Get(state_root, keccak256(addr))` →
      `Account.decode(bytes)`.
  - `pre_state.get_storage(addr, slot)`:
      `account = pre_state.get_account(addr)`,
      `MPT.Get(account.storage_root, keccak256(slot))`.
  - `pre_state.get_code(hash)`:
      `CodeDb.Lookup(hash)`.

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.PreState

-- TODO(stateless-state): expose the PreState record + reader
-- helpers (get_account, get_storage, get_code).

end EvmAsm.Stateless.State.PreState
