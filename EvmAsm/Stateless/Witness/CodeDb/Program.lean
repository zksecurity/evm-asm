/-
  EvmAsm.Stateless.Witness.CodeDb.Program

  Build the keccak-indexed lookup table for contract-code
  preimages from `witness.codes` (an SSZ List of variable-length
  ByteLists).

  Identical shape to `Witness.NodeDb.Program`, just sourced from
  the SSZ field at inner offset 1 of the witness container
  (`state` is offset 0, `codes` offset 1, `headers` offset 2).
  Output table base: `CODE_DB_BUCKETS` (see `MemoryLayout.lean`,
  1 MiB).

  ## PR-K9 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Witness.CodeDb.Program

-- TODO(stateless-witness): expose `build_code_db` Program
-- analogous to `Witness.NodeDb.Program.build_node_db` but
-- iterating `witness.codes` into `CODE_DB_BUCKETS`.

end EvmAsm.Stateless.Witness.CodeDb.Program
