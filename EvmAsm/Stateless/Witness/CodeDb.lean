/-
  EvmAsm.Stateless.Witness.CodeDb

  Umbrella for the contract-code lookup table. Mirrors
  `build_code_db` from `forks/amsterdam/witness_state.py`:

      def build_code_db(codes):
          return {keccak256(code_bytes): code_bytes for code_bytes in codes}

  Same shape as `NodeDb` but indexes `witness.codes` (the
  contract-code preimages required by EXTCODE*, CALL, and CREATE
  paths). The hash key is the EVM-level `codeHash` stored in each
  account.

  ## Subtree

  - `Program.lean` — iterate over `witness.codes`, keccak each, write
                     to `CODE_DB_BUCKETS`.
  - `Spec.lean`    — cpsTriple placeholders.

  Lookup is intentionally homed in `NodeDb/Lookup.lean` --
  parameterised by the bucket-array base address so both NodeDb
  and CodeDb share the implementation. (Refactor in a follow-up
  if the codepath diverges.)
-/

import EvmAsm.Stateless.Witness.CodeDb.Program
import EvmAsm.Stateless.Witness.CodeDb.Spec
