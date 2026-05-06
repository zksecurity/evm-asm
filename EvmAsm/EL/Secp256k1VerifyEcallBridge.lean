/-
  EvmAsm.EL.Secp256k1VerifyEcallBridge

  Pure zkVM `zkvm_secp256k1_verify` accelerator ECALL surface. Unlike the
  precompile bridges (KECCAK / SHA256 / RIPEMD160), this is the non-precompile
  accelerator used by EL transaction-validation paths (#122 work) and does not
  produce a stack word — its result is a `Bool` `verified` flag plus the
  accelerator-level `ZkvmStatus`.
-/

import EvmAsm.EL.Secp256k1VerifyInputBridge
import EvmAsm.EL.Secp256k1VerifyResultBridge
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Secp256k1VerifyEcallBridge

/-- Selector reserved for the `zkvm_secp256k1_verify` accelerator ECALL. -/
def secp256k1VerifySelector : BitVec 64 :=
  EvmAsm.Rv64.SyscallIdWord.secp256k1_verify

/-- ECALL request passed to the zkVM secp256k1-verify accelerator. -/
structure Secp256k1VerifyRequest where
  selector : BitVec 64
  input    : Secp256k1VerifyInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM secp256k1-verify accelerator. -/
structure Secp256k1VerifyResult where
  status : EvmAsm.Accelerators.ZkvmStatus
  output : Secp256k1VerifyResultBridge.AcceleratorOutput

/-- Build the secp256k1-verify accelerator request from already-loaded input. -/
def requestFromInput
    (input : Secp256k1VerifyInputBridge.AcceleratorInput) : Secp256k1VerifyRequest :=
  { selector := secp256k1VerifySelector, input := input }

/-- Boolean `verified` flag exposed by a secp256k1-verify accelerator result. -/
def verifiedFromResult (result : Secp256k1VerifyResult) : Bool :=
  Secp256k1VerifyResultBridge.verifiedFromOutput result.output

/--
Pure execution boundary for the secp256k1-verify ECALL. The signature-check
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, the status return, and the verified flag extracted from
the returned output buffer.

Distinctive token: Secp256k1VerifyEcallBridge.executeSecp256k1VerifyEcall.
-/
def executeSecp256k1VerifyEcall
    (accelerator : Secp256k1VerifyInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Secp256k1VerifyResultBridge.AcceleratorOutput)
    (request : Secp256k1VerifyRequest) : Secp256k1VerifyResult :=
  let result := accelerator request.input
  { status := result.1, output := result.2 }

theorem requestFromInput_selector
    (input : Secp256k1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = secp256k1VerifySelector := rfl

theorem requestFromInput_input
    (input : Secp256k1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeSecp256k1VerifyEcall_status
    (accelerator : Secp256k1VerifyInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Secp256k1VerifyResultBridge.AcceleratorOutput)
    (request : Secp256k1VerifyRequest) :
    (executeSecp256k1VerifyEcall accelerator request).status =
      (accelerator request.input).1 := by
  rfl

theorem executeSecp256k1VerifyEcall_output
    (accelerator : Secp256k1VerifyInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Secp256k1VerifyResultBridge.AcceleratorOutput)
    (request : Secp256k1VerifyRequest) :
    (executeSecp256k1VerifyEcall accelerator request).output =
      (accelerator request.input).2 := by
  rfl

theorem executeSecp256k1VerifyEcall_verified
    (accelerator : Secp256k1VerifyInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Secp256k1VerifyResultBridge.AcceleratorOutput)
    (request : Secp256k1VerifyRequest) :
    verifiedFromResult (executeSecp256k1VerifyEcall accelerator request) =
      Secp256k1VerifyResultBridge.verifiedFromOutput
        (accelerator request.input).2 := by
  rfl

theorem executeSecp256k1VerifyEcall_fromMemory_verified
    (accelerator : Secp256k1VerifyInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Secp256k1VerifyResultBridge.AcceleratorOutput)
    (memory : Secp256k1VerifyInputBridge.MemoryReader)
    (msgStart sigStart pubkeyStart : Nat) :
    verifiedFromResult
        (executeSecp256k1VerifyEcall accelerator
          (requestFromInput
            (Secp256k1VerifyInputBridge.acceleratorInputFromMemory
              memory msgStart sigStart pubkeyStart))) =
      Secp256k1VerifyResultBridge.verifiedFromOutput
        (accelerator
          (Secp256k1VerifyInputBridge.acceleratorInputFromMemory
            memory msgStart sigStart pubkeyStart)).2 := by
  rfl

end Secp256k1VerifyEcallBridge

end EvmAsm.EL
