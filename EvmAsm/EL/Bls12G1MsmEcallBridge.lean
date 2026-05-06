/-
  EvmAsm.EL.Bls12G1MsmEcallBridge

  Pure zkVM BLS12-381 G1 MSM accelerator ECALL surface.
-/

import EvmAsm.EL.Bls12G1MsmInputBridge
import EvmAsm.EL.Bls12G1MsmResultBridge
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Bls12G1MsmEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BLS12-381 G1 MSM accelerator ECALL surface. -/
def bls12G1MsmSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_g1_msm

/-- ECALL request passed to the zkVM BLS12-381 G1 MSM accelerator. -/
structure Bls12G1MsmRequest where
  selector : Rv64Word
  input : Bls12G1MsmInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BLS12-381 G1 MSM accelerator. -/
structure Bls12G1MsmResult where
  status : ZkvmStatus
  output : Bls12G1MsmResultBridge.AcceleratorOutput

/-- Build the BLS12-381 G1 MSM accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bls12G1MsmInputBridge.AcceleratorInput) : Bls12G1MsmRequest :=
  { selector := bls12G1MsmSelector, input := input }

/-- Project the output point exposed by a successful BLS12-381 G1 MSM result. -/
def outputPointFromResult (result : Bls12G1MsmResult) :
    Bls12G1MsmInputBridge.G1PointBytes :=
  result.output.point

/--
Pure execution boundary for the BLS12-381 G1 MSM ECALL. The curve operation
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12G1MsmEcall
    (accelerator : Bls12G1MsmInputBridge.AcceleratorInput →
      Bls12G1MsmResultBridge.AcceleratorResult)
    (request : Bls12G1MsmRequest) : Bls12G1MsmResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bls12G1MsmInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12G1MsmSelector := rfl

theorem requestFromInput_input
    (input : Bls12G1MsmInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBls12G1MsmEcall_status
    (accelerator : Bls12G1MsmInputBridge.AcceleratorInput →
      Bls12G1MsmResultBridge.AcceleratorResult)
    (request : Bls12G1MsmRequest) :
    (executeBls12G1MsmEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBls12G1MsmEcall_output
    (accelerator : Bls12G1MsmInputBridge.AcceleratorInput →
      Bls12G1MsmResultBridge.AcceleratorResult)
    (request : Bls12G1MsmRequest) :
    (executeBls12G1MsmEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBls12G1MsmEcall_outputPoint
    (accelerator : Bls12G1MsmInputBridge.AcceleratorInput →
      Bls12G1MsmResultBridge.AcceleratorResult)
    (request : Bls12G1MsmRequest) :
    outputPointFromResult (executeBls12G1MsmEcall accelerator request) =
      (accelerator request.input).output.point := rfl

theorem executeBls12G1MsmEcall_fromMemory_outputPoint
    (accelerator : Bls12G1MsmInputBridge.AcceleratorInput →
      Bls12G1MsmResultBridge.AcceleratorResult)
    (memory : Bls12G1MsmInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    outputPointFromResult
        (executeBls12G1MsmEcall accelerator
          (requestFromInput
            (Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory
              memory pairsStart numPairs))) =
      (accelerator
        (Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory
          memory pairsStart numPairs)).output.point := rfl

end Bls12G1MsmEcallBridge

end EvmAsm.EL
