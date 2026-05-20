/-
  EvmAsm.Stateless.Witness.MPT.Set

  Incremental `mpt_set(root, key, value) -> new_root`. Mutates
  the trie in place using the witness `node_db` as the source of
  ancestor nodes. Used during state-root recompute after the
  block STF produces a diff.

  ## Algorithm (Python `IncrementalMPT.set`)

      def mpt_set(root, key, value):
          path = keccak256(key) as nibbles
          # Walk down to the leaf position, recording the path of
          # nodes encountered.
          touched_chain = walk_recording(root, path)
          # Splice in the new (path, value) at the leaf:
          new_node = make_leaf(remaining_path, value)
          # Bubble up the chain, replacing each ancestor with a
          # version that points at the next-level new node.
          for parent in reversed(touched_chain):
              new_parent = parent.replace_child(branch_idx, new_node)
              new_node = new_parent
          return keccak256(rlp.encode(new_node))

  ## RISC-V plan (sketch)

  Maintain a stack of (node_ptr, node_kind, child_idx) frames as
  we descend. After splicing the new leaf, re-encode each frame
  bottom-up, computing the new node's hash via
  `zkvm_keccak256`. Push new nodes into a "post-state node_db" so
  later `set` calls can chase them.

  ## PR-K9 status

  Scaffold only. The most complex piece of the MPT subtree;
  multiple follow-up PRs will likely be needed.
-/

namespace EvmAsm.Stateless.Witness.MPT.Set

-- TODO(stateless-witness): expose `mpt_set(root, key_ptr,
-- key_len, value_ptr, value_len) -> new_root_ptr` and a paired
-- `mpt_delete` for storage SSTORE-to-zero / account selfdestruct.

end EvmAsm.Stateless.Witness.MPT.Set
