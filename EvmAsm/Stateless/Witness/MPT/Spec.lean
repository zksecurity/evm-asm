/-
  EvmAsm.Stateless.Witness.MPT.Spec

  Placeholder for cpsTriple specs over the MPT module.

  Final form:

  - `mpt_walk_spec`  -- given a valid witness `node_db`, walking
                        from `root` with `path` reaches the trie
                        slot prescribed by Python's
                        `IncrementalMPT`.
  - `mpt_get_spec`   -- end-to-end `mpt_get(root, key)` matches
                        the Python reference (including the
                        `None` case on missing keys).
  - `mpt_set_spec`   -- mutation result has a recomputed root
                        consistent with the inserted leaf.
  - `mpt_root_spec`  -- root hash equals the recursive `rlp`
                        + `keccak256` chain of the in-memory
                        node tree.

  TODO(stateless-proofs).
-/

namespace EvmAsm.Stateless.Witness.MPT.Spec

-- TODO(stateless-proofs): cpsTripleWithin for mpt_walk / get /
-- set / root.

end EvmAsm.Stateless.Witness.MPT.Spec
