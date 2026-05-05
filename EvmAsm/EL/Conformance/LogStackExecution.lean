/-
  EvmAsm.EL.Conformance.LogStackExecution

  Lean-side conformance vector for the LOG stack execution bridge
  (GH #112 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.LogStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace LogStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind
abbrev LogStackState := EvmAsm.EL.LogStackExecutionBridge.LogStackState
abbrev CallSideEffects := EvmAsm.EL.LogStackExecutionBridge.CallSideEffects
abbrev MemoryReader := EvmAsm.EL.LogStackExecutionBridge.MemoryReader

deriving instance DecidableEq for EvmAsm.EL.LogEntry
deriving instance DecidableEq for EvmAsm.EL.LogState
deriving instance DecidableEq for
  EvmAsm.EL.MessageCallExecution.CallSideEffects
deriving instance DecidableEq for
  EvmAsm.EL.LogStackExecutionBridge.LogStackState

structure LogStackInput where
  kind : LogKind
  emitter : Address
  memory : List Byte
  state : LogStackState

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def runLogStack? (input : LogStackInput) : Option LogStackState :=
  EvmAsm.EL.LogStackExecutionBridge.runLogStack?
    input.kind input.emitter (readByteAt input.memory) input.state

def logStackVector : TestVector LogStackInput LogStackState :=
  { id := "log-stack-log1"
    input :=
      { kind := .log1
        emitter := 0x1234
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 0xabc, 99] } }
    expected :=
      .value
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := 0x1234
                        topics := [(0xabc : EvmWord)]
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(99 : EvmWord)] } }

theorem runLogStack?_log1_vector :
    runLogStack?
      { kind := .log1
        emitter := (0x1234 : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 0xabc, 99] } } =
      some
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := (0x1234 : Address)
                        topics := [(0xabc : EvmWord)]
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(99 : EvmWord)] } := rfl

theorem logStackVector_passed :
    checkVector? runLogStack? logStackVector = .passed :=
  checkVector?_some_passed runLogStack?
    "log-stack-log1"
    { kind := .log1
      emitter := (0x1234 : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      state :=
        { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
          stack := [(1 : EvmWord), 2, 0xabc, 99] } }
    { effects :=
        { refundCounter := 0
          logs :=
            { entries :=
                [ { emitter := (0x1234 : Address)
                    topics := [(0xabc : EvmWord)]
                    data := [(0xbb : Byte), 0xcc] } ] }
          accountsToDelete := []
          touchedAccounts := [] }
      stack := [(99 : EvmWord)] }
    runLogStack?_log1_vector

/-- Compact checked-vector batch for LOG stack execution.
    Distinctive token:
    LogStackExecutionConformance.logStackConformanceVectors #112 #125. -/
def logStackConformanceVectors : List CheckResult :=
  [checkVector? runLogStack? logStackVector]

theorem logStackConformanceVectors_passed :
    logStackConformanceVectors = [.passed] := by
  simp [logStackConformanceVectors, logStackVector_passed]

end LogStackExecution
end Conformance
end EvmAsm.EL
