/-
  EvmAsm.Stateless.Block.Spec

  Placeholder for cpsTriple specs over the Block subtree.

  Final form:

  - `execute_block_spec`     -- composing ValidateHeader + ApplyBody
                                + StateRoot yields the same
                                end-of-block state Python's
                                `execute_block` would.
  - `apply_body_spec`        -- per-tx loop matches Python's
                                `apply_body` semantics tx-by-tx.
  - `validate_header_spec`   -- accepts iff Python accepts.

  TODO(stateless-proofs).
-/

namespace EvmAsm.Stateless.Block.Spec

-- TODO(stateless-proofs): cpsTripleWithin for the Block subtree.

end EvmAsm.Stateless.Block.Spec
