/-
  EvmAsm.Stateless.Witness.MPT.Root

  Compute the root hash of a (possibly mutated) MPT subtree.
  Used in two places:

  1. After `mpt_set` mutations, to re-hash the updated subtree
     and produce a new state_root for the block.
  2. At verification time, to confirm the post-state root the
     guest computes matches the value committed by the block
     header.

  ## Algorithm

      def mpt_root(node):
          if isinstance(node, hash):  return node
          encoded = rlp.encode(node)
          if len(encoded) < 32:        return encoded  # inlined
          return keccak256(encoded)

  ## RISC-V plan

  Walk the in-memory node tree (the working RAM region where
  `mpt_set` deposited mutated nodes), RLP-encode each, keccak,
  and return the root hash.

  ## PR-K9 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Witness.MPT.Root

-- TODO(stateless-witness): expose `mpt_root(node_id) ->
-- root_hash_ptr`.

end EvmAsm.Stateless.Witness.MPT.Root
