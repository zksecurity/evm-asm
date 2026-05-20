/-
  EvmAsm.Stateless.VM.Spec

  Placeholder for cpsTriple specs over the VM subtree.

  Final form composes the per-opcode `cpsTripleWithin` specs
  already in `EvmAsm/Evm64/<Op>/Spec.lean` into:

  - `execute_message_spec` -- one EVM frame's run matches the
                              Python `execute_message` semantics
                              tick-for-tick.

  And per-feature specs:

  - `frame_init_spec`        -- frame setup is consistent.
  - `gas_charging_spec`      -- gas math matches the YP schedule.
  - `memory_expansion_spec`  -- expand_memory matches YP.
  - `precompile_dispatch_spec` -- routes to Unimplemented for
                                  every address 0x01..0x14.

  TODO(stateless-proofs).
-/

namespace EvmAsm.Stateless.VM.Spec

-- TODO(stateless-proofs): cpsTripleWithin for the VM subtree.

end EvmAsm.Stateless.VM.Spec
