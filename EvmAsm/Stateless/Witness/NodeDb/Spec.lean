/-
  EvmAsm.Stateless.Witness.NodeDb.Spec

  Placeholder for cpsTriple specs over the `NodeDb` Programs.

  Final form:

  - `build_node_db_spec_within` -- given an SSZ-encoded
    `witness.state` (well-formed list of byte arrays) at
    `state_section`, after running `Program.build_node_db`, the
    `NODE_DB_BUCKETS` table holds `(keccak256(elem_i), ptr_i, len_i)`
    for every element of the list.
  - `lookup_node_spec_within` -- given the NODE_DB_BUCKETS table
    populated by `build_node_db`, looking up `hash` returns the
    matching `(ptr, len)` iff `hash` is a known entry, else
    `(0, 0, MISSING_NODE)`.

  TODO(stateless-proofs): the triples reference Programs that
  don't exist yet (PR-K9 scaffold). Future proof PRs write into
  this file directly.
-/

namespace EvmAsm.Stateless.Witness.NodeDb.Spec

-- TODO(stateless-proofs): cpsTripleWithin for build_node_db /
-- lookup_node.

end EvmAsm.Stateless.Witness.NodeDb.Spec
