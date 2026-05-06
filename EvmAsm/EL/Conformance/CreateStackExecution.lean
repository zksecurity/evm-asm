/-
  EvmAsm.EL.Conformance.CreateStackExecution

  Lean-side conformance vector for the CREATE stack execution bridge
  (GH #115 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.CreateStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace CreateStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind
abbrev CreateStackState :=
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState

deriving instance DecidableEq for
  EvmAsm.EL.CreateStackExecutionBridge.CreateStackState

structure CreateStackInput where
  kind : CreateKind
  creator : Address
  memory : List Byte
  gas : EvmWord
  stackState : CreateStackState

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def deployedAddress : Address := 0x1234

def vectorExecutor (request : CreateRequest) : CreateResult :=
  if request.kind = .create ∧ request.initcode = [(0xbb : Byte), 0xcc] ∧
      request.value = 7 ∧ request.gas = 321 ∧ request.salt? = none then
    { status := .deployed
      address? := some deployedAddress
      state := WorldState.empty
      returndata := []
      gasRemaining := 300 }
  else
    { status := .failed
      address? := none
      state := WorldState.empty
      returndata := []
      gasRemaining := 0 }

def runCreateStackVector? (input : CreateStackInput) : Option CreateStackState :=
  EvmAsm.EL.CreateStackExecutionBridge.runCreateStack?
    input.kind input.creator (readByteAt input.memory) input.gas vectorExecutor
    input.stackState

def createStackVector : TestVector CreateStackInput CreateStackState :=
  { id := "create-stack-execution"
    input :=
      { kind := .create
        creator := 0xabcd
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := 321
        stackState := { stack := [(7 : EvmWord), 1, 2, 99] } }
    expected :=
      .value { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] } }

theorem runCreateStackVector?_create :
    runCreateStackVector?
      { kind := .create
        creator := (0xabcd : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        gas := (321 : EvmWord)
        stackState := { stack := [(7 : EvmWord), 1, 2, 99] } } =
      some { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] } := by
  native_decide

theorem createStackVector_passed :
    checkVector? runCreateStackVector? createStackVector = .passed :=
  checkVector?_some_passed runCreateStackVector?
    "create-stack-execution"
    { kind := .create
      creator := (0xabcd : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      gas := (321 : EvmWord)
      stackState := { stack := [(7 : EvmWord), 1, 2, 99] } }
    { stack := [(deployedAddress.zeroExtend 256 : EvmWord), 99] }
    runCreateStackVector?_create

/-- Compact checked-vector batch for CREATE stack execution.
    Distinctive token:
    CreateStackExecutionConformance.createStackConformanceVectors #115 #125. -/
def createStackConformanceVectors : List CheckResult :=
  [checkVector? runCreateStackVector? createStackVector]

theorem createStackConformanceVectors_passed :
    createStackConformanceVectors = [.passed] := by
  simp [createStackConformanceVectors, createStackVector_passed]

end CreateStackExecution
end Conformance
end EvmAsm.EL
