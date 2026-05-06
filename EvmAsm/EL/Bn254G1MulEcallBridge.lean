/-
  EvmAsm.EL.Bn254G1MulEcallBridge

  Pure zkVM BN254 G1 scalar-multiplication accelerator ECALL surface.
-/

import EvmAsm.EL.Bn254G1MulInputBridge
import EvmAsm.EL.Bn254G1MulResultBridge
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Bn254G1MulEcallBridge

abbrev Rv64Word := BitVec 64
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Selector reserved for the BN254 G1 mul accelerator ECALL surface. -/
def bn254G1MulSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bn254_g1_mul

/-- ECALL request passed to the zkVM BN254 G1 mul accelerator. -/
structure Bn254G1MulRequest where
  selector : Rv64Word
  input : Bn254G1MulInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BN254 G1 mul accelerator. -/
structure Bn254G1MulResult where
  status : ZkvmStatus
  output : Bn254G1MulResultBridge.AcceleratorOutput

/-- Build the BN254 G1 mul accelerator request from already-loaded input bytes. -/
def requestFromInput
    (input : Bn254G1MulInputBridge.AcceleratorInput) : Bn254G1MulRequest :=
  { selector := bn254G1MulSelector, input := input }

/-- Project the output point exposed by a successful BN254 G1 mul result. -/
def outputPointFromResult (result : Bn254G1MulResult) :
    Bn254G1MulInputBridge.G1PointBytes :=
  result.output.point

/--
Pure execution boundary for the BN254 G1 mul ECALL. The curve operation itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, selector, status code, and output buffer.
-/
def executeBn254G1MulEcall
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) : Bn254G1MulResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }

theorem requestFromInput_selector
    (input : Bn254G1MulInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bn254G1MulSelector := rfl

theorem requestFromInput_input
    (input : Bn254G1MulInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBn254G1MulEcall_status
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    (executeBn254G1MulEcall accelerator request).status =
      (accelerator request.input).status := rfl

theorem executeBn254G1MulEcall_output
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    (executeBn254G1MulEcall accelerator request).output =
      (accelerator request.input).output := rfl

theorem executeBn254G1MulEcall_outputPoint
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (request : Bn254G1MulRequest) :
    outputPointFromResult (executeBn254G1MulEcall accelerator request) =
      (accelerator request.input).output.point := rfl

theorem executeBn254G1MulEcall_fromMemory_outputPoint
    (accelerator : Bn254G1MulInputBridge.AcceleratorInput →
      Bn254G1MulResultBridge.AcceleratorResult)
    (memory : Bn254G1MulInputBridge.MemoryReader)
    (pointStart scalarStart : Nat) :
    outputPointFromResult
        (executeBn254G1MulEcall accelerator
          (requestFromInput
            (Bn254G1MulInputBridge.bn254G1MulInputFromMemory
              memory pointStart scalarStart))) =
      (accelerator
        (Bn254G1MulInputBridge.bn254G1MulInputFromMemory
          memory pointStart scalarStart)).output.point := rfl

end Bn254G1MulEcallBridge

end EvmAsm.EL
