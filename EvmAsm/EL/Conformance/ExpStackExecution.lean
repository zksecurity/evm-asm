/-
  EvmAsm.EL.Conformance.ExpStackExecution

  Lean-side conformance vectors for the EXP stack execution bridge
  (GH #92 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.Exp.StackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace ExpStackExecution

abbrev EvmWord := EvmAsm.Evm64.EvmWord

abbrev ExpStackState := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackState

abbrev ExpStackResult := EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult

abbrev ExpVisibleEffects :=
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpVisibleEffects

deriving instance DecidableEq for
  EvmAsm.Evm64.ExpStackExecutionBridge.ExpStackResult

def runExpStack? (input : ExpStackState) : Option ExpStackResult :=
  EvmAsm.Evm64.ExpStackExecutionBridge.runExpStack? input

def expStackValueVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-value"
    input := { stack := [2, 8, 99] }
    expected :=
      .value
        { effects :=
            { stackWords := [256]
              dynamicGas := 50
              totalGas := 60 }
          stack := [99] } }

def expStackUnderflowVector : TestVector ExpStackState ExpStackResult :=
  { id := "exp-stack-underflow"
    input := { stack := [2] }
    expected := .error "stack-underflow" }

theorem runExpStack?_value :
    runExpStack? { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] } =
      some
        { effects :=
            { stackWords := [(256 : EvmWord)]
              dynamicGas := 50
              totalGas := 60 }
          stack := [(99 : EvmWord)] } := by
  native_decide

theorem runExpStack?_underflow :
    runExpStack? { stack := [(2 : EvmWord)] } = none := rfl

theorem expStackValueVector_passed :
    checkVector? runExpStack? expStackValueVector = .passed :=
  checkVector?_some_passed runExpStack?
    "exp-stack-value"
    { stack := [(2 : EvmWord), (8 : EvmWord), (99 : EvmWord)] }
    { effects :=
        { stackWords := [(256 : EvmWord)]
          dynamicGas := 50
          totalGas := 60 }
      stack := [(99 : EvmWord)] }
    runExpStack?_value

theorem expStackUnderflowVector_passed :
    checkVector? runExpStack? expStackUnderflowVector =
      .errored "exp-stack-underflow" "stack-underflow" :=
  checkVector?_none_error runExpStack?
    "exp-stack-underflow"
    "stack-underflow"
    { stack := [(2 : EvmWord)] }
    runExpStack?_underflow

/-- Compact checked-vector batch for EXP stack execution.
    Distinctive token: ExpStackExecutionConformance.expStackConformanceVectors #92 #125. -/
def expStackConformanceVectors : List CheckResult :=
  [ checkVector? runExpStack? expStackValueVector
  , checkVector? runExpStack? expStackUnderflowVector
  ]

theorem expStackConformanceVectors_passed :
    expStackConformanceVectors =
      [.passed, .errored "exp-stack-underflow" "stack-underflow"] := by
  simp [expStackConformanceVectors, expStackValueVector_passed,
    expStackUnderflowVector_passed]

end ExpStackExecution
end Conformance
end EvmAsm.EL
