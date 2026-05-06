/-
  EvmAsm.EL.LogStackExecutionBridge

  Pure stack-to-log execution bridge for LOG0 through LOG4 (GH #112).
-/

import EvmAsm.Evm64.LogArgsStackDecode
import EvmAsm.EL.LogExecutionBridge

namespace EvmAsm.EL

namespace LogStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind
abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args
abbrev CallSideEffects := LogExecutionBridge.CallSideEffects
abbrev MemoryReader := LogExecutionBridge.MemoryReader

/-- Runtime state visible to the pure LOG stack bridge. -/
structure LogStackState where
  effects : CallSideEffects
  stack : List EvmWord

def stackRestAfterLog? (kind : LogKind) : List EvmWord -> Option (List EvmWord)
  | _offset :: _size :: rest =>
      match kind with
      | .log0 => some rest
      | .log1 =>
          match rest with
          | _topic0 :: rest => some rest
          | _ => none
      | .log2 =>
          match rest with
          | _topic0 :: _topic1 :: rest => some rest
          | _ => none
      | .log3 =>
          match rest with
          | _topic0 :: _topic1 :: _topic2 :: rest => some rest
          | _ => none
      | .log4 =>
          match rest with
          | _topic0 :: _topic1 :: _topic2 :: _topic3 :: rest => some rest
          | _ => none
  | _ => none

/--
Run the pure LOG stack effect: decode the opcode-specific stack arguments,
read the memory data slice, append the log side effect, and consume all LOG
arguments without pushing a result.

Distinctive token: LogStackExecutionBridge.runLogStack? #112.
-/
def runLogStack? (kind : LogKind) (emitter : Address) (readByte : MemoryReader) :
    LogStackState -> Option LogStackState
  | state =>
      match EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind state.stack,
          stackRestAfterLog? kind state.stack with
      | some args, some rest =>
          some
            { effects :=
                LogExecutionBridge.appendLogFromMemory
                  state.effects emitter readByte args
              stack := rest }
      | _, _ => none

theorem stackRestAfterLog?_log0
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log0 (offset :: size :: rest) = some rest := rfl

theorem stackRestAfterLog?_log1
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log1 (offset :: size :: topic0 :: rest) = some rest := rfl

theorem stackRestAfterLog?_log2
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log2 (offset :: size :: topic0 :: topic1 :: rest) =
      some rest := rfl

theorem stackRestAfterLog?_log3
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    stackRestAfterLog? .log3
        (offset :: size :: topic0 :: topic1 :: topic2 :: rest) =
      some rest := rfl

theorem stackRestAfterLog?_log4
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    stackRestAfterLog? .log4
        (offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest) =
      some rest := rfl

@[simp] theorem stackRestAfterLog?_nil (kind : LogKind) :
    stackRestAfterLog? kind [] = none := rfl

@[simp] theorem stackRestAfterLog?_singleton (kind : LogKind) (offset : EvmWord) :
    stackRestAfterLog? kind [offset] = none := rfl

theorem runLogStack?_eq_none_iff
    (kind : LogKind) (emitter : Address) (readByte : MemoryReader)
    (state : LogStackState) :
    runLogStack? kind emitter readByte state = none ↔
      EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind state.stack = none ∨
        stackRestAfterLog? kind state.stack = none := by
  cases state with
  | mk effects stack =>
      simp [runLogStack?]
      cases h_decode :
          EvmAsm.Evm64.LogArgsStackDecode.decodeLogStack? kind stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterLog? kind stack with
          | none => simp
          | some rest => simp

theorem runLogStack?_log0
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    runLogStack? .log0 emitter readByte
        { effects := effects, stack := offset :: size :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [])
          stack := rest } := rfl

theorem runLogStack?_log1
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log1 emitter readByte
        { effects := effects, stack := offset :: size :: topic0 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [topic0])
          stack := rest } := rfl

theorem runLogStack?_log2
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log2 emitter readByte
        { effects := effects, stack := offset :: size :: topic0 :: topic1 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size [topic0, topic1])
          stack := rest } := rfl

theorem runLogStack?_log3
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    runLogStack? .log3 emitter readByte
        { effects := effects,
          stack := offset :: size :: topic0 :: topic1 :: topic2 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size
                [topic0, topic1, topic2])
          stack := rest } := rfl

theorem runLogStack?_log4
    (effects : CallSideEffects) (emitter : Address) (readByte : MemoryReader)
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    runLogStack? .log4 emitter readByte
        { effects := effects,
          stack := offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest } =
      some
        { effects :=
            LogExecutionBridge.appendLogFromMemory effects emitter readByte
              (EvmAsm.Evm64.LogArgsStackDecode.mkArgs offset size
                [topic0, topic1, topic2, topic3])
          stack := rest } := rfl

theorem runLogStack?_stack_length
    {kind : LogKind} {emitter : Address} {readByte : MemoryReader}
    {state out : LogStackState}
    (h_run : runLogStack? kind emitter readByte state = some out) :
    out.stack.length + EvmAsm.Evm64.LogArgs.stackArgumentCount kind =
      state.stack.length := by
  cases state with
  | mk effects stack =>
      cases kind
      all_goals
        cases stack with
        | nil => simp [runLogStack?] at h_run
        | cons offset tail =>
            cases tail with
            | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
            | cons size rest =>
                first
                | simp [runLogStack?, stackRestAfterLog?] at h_run
                  cases h_run
                  simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                    EvmAsm.Evm64.LogArgs.topicCount]
                | cases rest with
                  | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                  | cons topic0 rest =>
                      first
                      | simp [runLogStack?, stackRestAfterLog?] at h_run
                        cases h_run
                        simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                          EvmAsm.Evm64.LogArgs.topicCount]
                      | cases rest with
                        | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                        | cons topic1 rest =>
                            first
                            | simp [runLogStack?, stackRestAfterLog?] at h_run
                              cases h_run
                              simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                EvmAsm.Evm64.LogArgs.topicCount]
                            | cases rest with
                              | nil => simp [runLogStack?, stackRestAfterLog?] at h_run
                              | cons topic2 rest =>
                                  first
                                  | simp [runLogStack?, stackRestAfterLog?] at h_run
                                    cases h_run
                                    simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                      EvmAsm.Evm64.LogArgs.topicCount]
                                  | cases rest with
                                    | nil =>
                                        simp [runLogStack?, stackRestAfterLog?] at h_run
                                    | cons topic3 rest =>
                                        simp [runLogStack?, stackRestAfterLog?] at h_run
                                        cases h_run
                                        simp [EvmAsm.Evm64.LogArgs.stackArgumentCount,
                                          EvmAsm.Evm64.LogArgs.topicCount]

end LogStackExecutionBridge

end EvmAsm.EL
