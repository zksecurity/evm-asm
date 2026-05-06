/-
  EvmAsm.EL.Secp256k1EcrecoverEcallBridge

  Pure zkVM secp256k1 ECRECOVER accelerator ECALL surface.
-/

import EvmAsm.EL.Secp256k1EcrecoverInputBridge
import EvmAsm.EL.Secp256k1EcrecoverResultBridge
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Secp256k1EcrecoverEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the secp256k1 ECRECOVER accelerator ECALL surface. -/
def secp256k1EcrecoverSelector : Rv64Word :=
  EvmAsm.Rv64.SyscallIdWord.secp256k1_ecrecover

/-- ECALL request passed to the zkVM secp256k1 ECRECOVER accelerator. -/
structure Secp256k1EcrecoverRequest where
  selector : Rv64Word
  input : Secp256k1EcrecoverInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM secp256k1 ECRECOVER accelerator. -/
structure Secp256k1EcrecoverResult where
  status : ZkvmStatus
  output : Secp256k1EcrecoverResultBridge.AcceleratorOutput

/-- Build the secp256k1 ECRECOVER request from already-loaded input. -/
def requestFromInput
    (input : Secp256k1EcrecoverInputBridge.AcceleratorInput) :
    Secp256k1EcrecoverRequest :=
  { selector := secp256k1EcrecoverSelector, input := input }

/-- Project the output public key exposed by a successful ECRECOVER result. -/
def outputPubkeyFromResult (result : Secp256k1EcrecoverResult) :
    Secp256k1EcrecoverResultBridge.PublicKeyBytes :=
  result.output.pubkey

/--
Pure execution boundary for the secp256k1 ECRECOVER ECALL. The recovery
operation itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeSecp256k1EcrecoverEcall
    (accelerator : Secp256k1EcrecoverInputBridge.AcceleratorInput →
      Secp256k1EcrecoverResultBridge.AcceleratorResult)
    (request : Secp256k1EcrecoverRequest) : Secp256k1EcrecoverResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Secp256k1EcrecoverInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = secp256k1EcrecoverSelector := rfl

theorem requestFromInput_input
    (input : Secp256k1EcrecoverInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeSecp256k1EcrecoverEcall_status
    (accelerator : Secp256k1EcrecoverInputBridge.AcceleratorInput →
      Secp256k1EcrecoverResultBridge.AcceleratorResult)
    (request : Secp256k1EcrecoverRequest) :
    (executeSecp256k1EcrecoverEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeSecp256k1EcrecoverEcall_output
    (accelerator : Secp256k1EcrecoverInputBridge.AcceleratorInput →
      Secp256k1EcrecoverResultBridge.AcceleratorResult)
    (request : Secp256k1EcrecoverRequest) :
    (executeSecp256k1EcrecoverEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeSecp256k1EcrecoverEcall_outputPubkey
    (accelerator : Secp256k1EcrecoverInputBridge.AcceleratorInput →
      Secp256k1EcrecoverResultBridge.AcceleratorResult)
    (request : Secp256k1EcrecoverRequest) :
    outputPubkeyFromResult (executeSecp256k1EcrecoverEcall accelerator request) =
      (accelerator request.input).output.pubkey := rfl

theorem executeSecp256k1EcrecoverEcall_fromMemory_outputPubkey
    (accelerator : Secp256k1EcrecoverInputBridge.AcceleratorInput →
      Secp256k1EcrecoverResultBridge.AcceleratorResult)
    (memory : Secp256k1EcrecoverInputBridge.MemoryReader)
    (msgStart sigStart : Nat) (recid : Byte) :
    outputPubkeyFromResult
        (executeSecp256k1EcrecoverEcall accelerator
          (requestFromInput
            (Secp256k1EcrecoverInputBridge.secp256k1EcrecoverInputFromMemory
              memory msgStart sigStart recid))) =
      (accelerator
        (Secp256k1EcrecoverInputBridge.secp256k1EcrecoverInputFromMemory
          memory msgStart sigStart recid)).output.pubkey := rfl

end Secp256k1EcrecoverEcallBridge

end EvmAsm.EL
