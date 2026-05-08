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

/-- LOG0 appends a log entry with no topics and consumes offset/size only.
    Distinctive token: log0StackConformanceVector #112 #125. -/
def log0StackConformanceVector : TestVector LogStackInput LogStackState :=
  { id := "log-stack-log0"
    input :=
      { kind := .log0
        emitter := 0x1234
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 42] } }
    expected :=
      .value
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := 0x1234
                        topics := []
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(42 : EvmWord)] } }

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

/-- LOG2 appends a log entry with two topics and consumes offset/size/topics.
    Distinctive token: logStackLog2Vector #112 #125. -/
def logStackLog2Vector : TestVector LogStackInput LogStackState :=
  { id := "log-stack-log2"
    input :=
      { kind := .log2
        emitter := 0x2345
        memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 0xabc, 0xdef, 77] } }
    expected :=
      .value
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := 0x2345
                        topics := [(0xabc : EvmWord), (0xdef : EvmWord)]
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(77 : EvmWord)] } }

def logStackLog4Vector : TestVector LogStackInput LogStackState :=
  { id := "log-stack-log4"
    input :=
      { kind := .log4
        emitter := 0x5678
        memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd, 0xee]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack :=
              [ (1 : EvmWord), 3, 0x11, 0x22, 0x33, 0x44, 0xdead ] } }
    expected :=
      .value
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := 0x5678
                        topics :=
                          [(0x11 : EvmWord), (0x22 : EvmWord),
                           (0x33 : EvmWord), (0x44 : EvmWord)]
                        data := [(0xbb : Byte), 0xcc, 0xdd] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(0xdead : EvmWord)] } }

/-- LOG stack conformance inputs as reusable test vectors.
    Distinctive token:
    LogStackExecutionConformance.logStackConformanceTestVectors #112 #125. -/
def logStackConformanceTestVectors : List (TestVector LogStackInput LogStackState) :=
  [ log0StackConformanceVector
  , logStackVector
  , logStackLog2Vector
  , logStackLog4Vector
  ]

def logStackConformanceVectorIds : List String :=
  logStackConformanceTestVectors.map TestVector.id

theorem logStackConformanceTestVectors_length :
    logStackConformanceTestVectors.length = 4 := rfl

theorem logStackConformanceVectorIds_eq :
    logStackConformanceVectorIds =
      ["log-stack-log0", "log-stack-log1", "log-stack-log2", "log-stack-log4"] := rfl

theorem logStackConformanceVectorIds_length :
    logStackConformanceVectorIds.length = 4 := rfl

theorem logStackConformanceVectorIds_nodup :
    logStackConformanceVectorIds.Nodup := by
  decide

theorem runLogStack?_log0_vector :
    runLogStack?
      { kind := .log0
        emitter := (0x1234 : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 42] } } =
      some
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := (0x1234 : Address)
                        topics := []
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(42 : EvmWord)] } := rfl

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

theorem runLogStack?_log2_vector :
    runLogStack?
      { kind := .log2
        emitter := (0x2345 : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack := [(1 : EvmWord), 2, 0xabc, 0xdef, 77] } } =
      some
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := (0x2345 : Address)
                        topics := [(0xabc : EvmWord), (0xdef : EvmWord)]
                        data := [(0xbb : Byte), 0xcc] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(77 : EvmWord)] } := rfl

theorem runLogStack?_log4_vector :
    runLogStack?
      { kind := .log4
        emitter := (0x5678 : Address)
        memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd, 0xee]
        state :=
          { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
            stack :=
              [ (1 : EvmWord), 3, 0x11, 0x22, 0x33, 0x44, 0xdead ] } } =
      some
        { effects :=
            { refundCounter := 0
              logs :=
                { entries :=
                    [ { emitter := (0x5678 : Address)
                        topics :=
                          [(0x11 : EvmWord), (0x22 : EvmWord),
                           (0x33 : EvmWord), (0x44 : EvmWord)]
                        data := [(0xbb : Byte), 0xcc, 0xdd] } ] }
              accountsToDelete := []
              touchedAccounts := [] }
          stack := [(0xdead : EvmWord)] } := rfl

theorem log0StackConformanceVector_passed :
    checkVector? runLogStack? log0StackConformanceVector = .passed :=
  checkVector?_some_passed runLogStack?
    "log-stack-log0"
    { kind := .log0
      emitter := (0x1234 : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc]
      state :=
        { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
          stack := [(1 : EvmWord), 2, 42] } }
    { effects :=
        { refundCounter := 0
          logs :=
            { entries :=
                [ { emitter := (0x1234 : Address)
                    topics := []
                    data := [(0xbb : Byte), 0xcc] } ] }
          accountsToDelete := []
          touchedAccounts := [] }
      stack := [(42 : EvmWord)] }
    runLogStack?_log0_vector

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

theorem logStackLog2Vector_passed :
    checkVector? runLogStack? logStackLog2Vector = .passed :=
  checkVector?_some_passed runLogStack?
    "log-stack-log2"
    { kind := .log2
      emitter := (0x2345 : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd]
      state :=
        { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
          stack := [(1 : EvmWord), 2, 0xabc, 0xdef, 77] } }
    { effects :=
        { refundCounter := 0
          logs :=
            { entries :=
                [ { emitter := (0x2345 : Address)
                    topics := [(0xabc : EvmWord), (0xdef : EvmWord)]
                    data := [(0xbb : Byte), 0xcc] } ] }
          accountsToDelete := []
          touchedAccounts := [] }
      stack := [(77 : EvmWord)] }
    runLogStack?_log2_vector

theorem logStackLog4Vector_passed :
    checkVector? runLogStack? logStackLog4Vector = .passed :=
  checkVector?_some_passed runLogStack?
    "log-stack-log4"
    { kind := .log4
      emitter := (0x5678 : Address)
      memory := [(0xaa : Byte), 0xbb, 0xcc, 0xdd, 0xee]
      state :=
        { effects := EvmAsm.EL.MessageCallExecution.CallSideEffects.empty
          stack :=
            [ (1 : EvmWord), 3, 0x11, 0x22, 0x33, 0x44, 0xdead ] } }
    { effects :=
        { refundCounter := 0
          logs :=
            { entries :=
                [ { emitter := (0x5678 : Address)
                    topics :=
                      [(0x11 : EvmWord), (0x22 : EvmWord),
                       (0x33 : EvmWord), (0x44 : EvmWord)]
                    data := [(0xbb : Byte), 0xcc, 0xdd] } ] }
          accountsToDelete := []
          touchedAccounts := [] }
      stack := [(0xdead : EvmWord)] }
    runLogStack?_log4_vector

/-- Compact checked-vector batch for LOG stack execution.
    Distinctive token:
    LogStackExecutionConformance.logStackConformanceVectors #112 #125. -/
def logStackConformanceVectors : List CheckResult :=
  checkBatch? runLogStack? logStackConformanceTestVectors

theorem logStackConformanceVectors_passed :
    logStackConformanceVectors = [.passed, .passed, .passed, .passed] := by
  simp [logStackConformanceVectors, logStackConformanceTestVectors,
    log0StackConformanceVector_passed, logStackVector_passed,
    logStackLog2Vector_passed, logStackLog4Vector_passed]

end LogStackExecution
end Conformance
end EvmAsm.EL
