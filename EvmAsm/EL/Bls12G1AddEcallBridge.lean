/-
  EvmAsm.EL.Bls12G1AddEcallBridge

  Pure zkVM BLS12-381 G1 addition accelerator ECALL surface.
-/

import EvmAsm.EL.Bls12G1AddInputBridge
import EvmAsm.EL.Bls12G1AddResultBridge
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Bls12G1AddEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BLS12-381 G1 add accelerator ECALL surface. -/
def bls12G1AddSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_g1_add

/-- ECALL request passed to the zkVM BLS12-381 G1 add accelerator. -/
structure Bls12G1AddRequest where
  selector : Rv64Word
  input : Bls12G1AddInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BLS12-381 G1 add accelerator. -/
structure Bls12G1AddResult where
  status : ZkvmStatus
  output : Bls12G1AddResultBridge.AcceleratorOutput

/-- Build the BLS12-381 G1 add accelerator request from already-loaded input points. -/
def requestFromInput
    (input : Bls12G1AddInputBridge.AcceleratorInput) : Bls12G1AddRequest :=
  { selector := bls12G1AddSelector, input := input }

/-- Project the output point exposed by a successful BLS12-381 G1 add result. -/
def outputPointFromResult (result : Bls12G1AddResult) :
    Bls12G1AddInputBridge.G1PointBytes :=
  result.output.point

/--
Pure execution boundary for the BLS12-381 G1 add ECALL. The curve operation
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12G1AddEcall
    (accelerator : Bls12G1AddInputBridge.AcceleratorInput →
      Bls12G1AddResultBridge.AcceleratorResult)
    (request : Bls12G1AddRequest) : Bls12G1AddResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bls12G1AddInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12G1AddSelector := rfl

theorem requestFromInput_input
    (input : Bls12G1AddInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBls12G1AddEcall_status
    (accelerator : Bls12G1AddInputBridge.AcceleratorInput →
      Bls12G1AddResultBridge.AcceleratorResult)
    (request : Bls12G1AddRequest) :
    (executeBls12G1AddEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBls12G1AddEcall_output
    (accelerator : Bls12G1AddInputBridge.AcceleratorInput →
      Bls12G1AddResultBridge.AcceleratorResult)
    (request : Bls12G1AddRequest) :
    (executeBls12G1AddEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBls12G1AddEcall_outputPoint
    (accelerator : Bls12G1AddInputBridge.AcceleratorInput →
      Bls12G1AddResultBridge.AcceleratorResult)
    (request : Bls12G1AddRequest) :
    outputPointFromResult (executeBls12G1AddEcall accelerator request) =
      (accelerator request.input).output.point := rfl

theorem executeBls12G1AddEcall_fromMemory_outputPoint
    (accelerator : Bls12G1AddInputBridge.AcceleratorInput →
      Bls12G1AddResultBridge.AcceleratorResult)
    (memory : Bls12G1AddInputBridge.MemoryReader)
    (p1Start p2Start : Nat) :
    outputPointFromResult
        (executeBls12G1AddEcall accelerator
          (requestFromInput
            (Bls12G1AddInputBridge.bls12G1AddInputFromMemory
              memory p1Start p2Start))) =
      (accelerator
        (Bls12G1AddInputBridge.bls12G1AddInputFromMemory
          memory p1Start p2Start)).output.point := rfl

end Bls12G1AddEcallBridge

end EvmAsm.EL
