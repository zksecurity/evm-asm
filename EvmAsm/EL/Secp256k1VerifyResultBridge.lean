/-
  EvmAsm.EL.Secp256k1VerifyResultBridge

  Bridge from the zkVM `zkvm_secp256k1_verify` accelerator output (a single
  boolean `verified` flag) to the Lean-level result consumed by EL transaction
  validation paths. Unlike precompile bridges, this surface does NOT produce a
  stack word — secp256k1_verify is a non-precompile accelerator used by
  `EvmAsm.EL.Transaction` validation.
-/

namespace EvmAsm.EL

namespace Secp256k1VerifyResultBridge

/--
Accelerator output payload for `zkvm_secp256k1_verify`. The C signature writes
into a `bool* verified` out-parameter; we model that as a single field.
-/
structure AcceleratorOutput where
  verified : Bool
  deriving Repr, DecidableEq

/-- Distinctive token: Secp256k1VerifyResultBridge.verifiedFromOutput. -/
def verifiedFromOutput (output : AcceleratorOutput) : Bool :=
  output.verified

@[simp] theorem verifiedFromOutput_eq (output : AcceleratorOutput) :
    verifiedFromOutput output = output.verified := rfl

@[simp] theorem verifiedFromOutput_mk (b : Bool) :
    verifiedFromOutput { verified := b } = b := rfl

end Secp256k1VerifyResultBridge

end EvmAsm.EL
