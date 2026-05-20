/-
  EvmAsm.Stateless.State.StateRoot

  Compute the post-state root after applying a `BlockDiff` to
  the pre-state's MPT. Mirrors Python's
  `compute_state_root_and_trie_changes` from
  `forks/amsterdam/state.py`.

  ## Algorithm

  For each account in `diff.account_changes`:
    addr_path = keccak256(addr) as nibbles
    if account is deleted (EIP-161 empty):
        MPT.Set(state_root, addr_path, b"")   # actually a delete
    else:
        # Storage changes for this account first
        for ((same_addr, slot), val) in diff.storage_changes:
            slot_path = keccak256(slot) as nibbles
            MPT.Set(account.storage_root,
                    slot_path, rlp.encode(val))
        account.storage_root = MPT.Root(updated subtree)
        MPT.Set(state_root, addr_path,
                rlp.encode(account))

  For each code in `diff.code_changes`:
    CodeDb already has it as a witness entry; no MPT mutation
    needed (codeHash references unchanged).

  Final post-state root = MPT.Root(updated trie).

  ## RISC-V plan

  Composes `MPT.Set` (each address/slot insertion) with
  `MPT.Root` (final re-hash). The mutated nodes live in a working-
  RAM region appended to the existing NODE_DB_BUCKETS.

  ## PR-K10 status

  Scaffold only. This is one of the most complex pieces of the
  stateless guest -- compose many MPT mutations and re-hash.
  Multiple follow-up PRs will likely be needed.
-/

namespace EvmAsm.Stateless.State.StateRoot

-- TODO(stateless-state): expose
-- `compute_state_root_and_trie_changes(pre_state, diff) ->
--  new_state_root_ptr`.

end EvmAsm.Stateless.State.StateRoot
