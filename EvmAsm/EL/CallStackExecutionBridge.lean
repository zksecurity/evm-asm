/-
  EvmAsm.EL.CallStackExecutionBridge

  Pure stack-to-executor bridge for CALL-family opcodes (GH #114).
-/

import EvmAsm.Evm64.CallArgsStackDecode
import EvmAsm.EL.CallExecutionBridge

namespace EvmAsm.EL

namespace CallStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CallKind := EvmAsm.Evm64.CallArgs.Kind
abbrev MemoryReader := CallExecutionBridge.MemoryReader
abbrev CallExecutor := MessageCallExecution.CallExecutor
abbrev CallVisibleEffects := CallExecutionBridge.CallVisibleEffects

structure CallStackState where
  stack : List EvmWord

structure CallStackResult where
  effects : CallVisibleEffects
  stack : List EvmWord

def stackRestAfterCall? : CallKind -> List EvmWord -> Option (List EvmWord)
  | .call, _gas :: _to :: _value :: _inputOffset :: _inputSize ::
      _outputOffset :: _outputSize :: rest => some rest
  | .staticcall, _gas :: _to :: _inputOffset :: _inputSize ::
      _outputOffset :: _outputSize :: rest => some rest
  | .delegatecall, _gas :: _to :: _inputOffset :: _inputSize ::
      _outputOffset :: _outputSize :: rest => some rest
  | _, _ => none

def runCallStack? (kind : CallKind) (state : WorldState) (caller callee : Address)
    (apparentValue : Word256) (readByte : MemoryReader) (isStatic : Bool)
    (executor : CallExecutor) : CallStackState -> Option CallStackResult
  | stackState =>
      match kind with
      | .call =>
          match EvmAsm.Evm64.CallArgsStackDecode.decodeCallStack? stackState.stack,
              stackRestAfterCall? .call stackState.stack with
          | some args, some rest =>
              let input :=
                CallExecutionBridge.callInputFromMemory
                  state caller callee readByte isStatic args
              some
                { effects :=
                    CallExecutionBridge.callVisibleEffectsFromResult
                      (executor input) args
                  stack := rest }
          | _, _ => none
      | .staticcall =>
          match EvmAsm.Evm64.CallArgsStackDecode.decodeStaticCallStack? stackState.stack,
              stackRestAfterCall? .staticcall stackState.stack with
          | some args, some rest =>
              let input :=
                CallExecutionBridge.staticCallInputFromMemory
                  state caller callee readByte args
              some
                { effects :=
                    CallExecutionBridge.staticCallVisibleEffectsFromResult
                      (executor input) args
                  stack := rest }
          | _, _ => none
      | .delegatecall =>
          match EvmAsm.Evm64.CallArgsStackDecode.decodeDelegateCallStack? stackState.stack,
              stackRestAfterCall? .delegatecall stackState.stack with
          | some args, some rest =>
              let input :=
                CallExecutionBridge.delegateCallInputFromMemory
                  state caller callee apparentValue readByte isStatic args
              some
                { effects :=
                    CallExecutionBridge.delegateCallVisibleEffectsFromResult
                      (executor input) args
                  stack := rest }
          | _, _ => none

theorem stackRestAfterCall?_call
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    stackRestAfterCall? .call
        (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
          outputSize :: rest) =
      some rest := rfl

theorem stackRestAfterCall?_staticcall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    stackRestAfterCall? .staticcall
        (gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: rest) =
      some rest := rfl

theorem stackRestAfterCall?_delegatecall
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    stackRestAfterCall? .delegatecall
        (gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: rest) =
      some rest := rfl

theorem runCallStack?_call
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    runCallStack? .call state caller callee apparentValue readByte isStatic executor
        { stack :=
            gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
              outputSize :: rest } =
      some
        { effects :=
            CallExecutionBridge.callVisibleEffectsFromResult
              (executor
                (CallExecutionBridge.callInputFromMemory state caller callee readByte
                  isStatic
                  { gas := gas, to := to, value := value,
                    input := { offset := inputOffset, size := inputSize },
                    output := { offset := outputOffset, size := outputSize } }))
              { gas := gas, to := to, value := value,
                input := { offset := inputOffset, size := inputSize },
                output := { offset := outputOffset, size := outputSize } }
          stack := rest } := rfl

theorem runCallStack?_staticcall
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    runCallStack? .staticcall state caller callee apparentValue readByte isStatic executor
        { stack := gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest } =
      some
        { effects :=
            CallExecutionBridge.staticCallVisibleEffectsFromResult
              (executor
                (CallExecutionBridge.staticCallInputFromMemory
                  state caller callee readByte
                  { gas := gas, to := to,
                    input := { offset := inputOffset, size := inputSize },
                    output := { offset := outputOffset, size := outputSize } }))
              { gas := gas, to := to,
                input := { offset := inputOffset, size := inputSize },
                output := { offset := outputOffset, size := outputSize } }
          stack := rest } := rfl

theorem runCallStack?_delegatecall
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    runCallStack? .delegatecall state caller callee apparentValue readByte isStatic executor
        { stack := gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest } =
      some
        { effects :=
            CallExecutionBridge.delegateCallVisibleEffectsFromResult
              (executor
                (CallExecutionBridge.delegateCallInputFromMemory
                  state caller callee apparentValue readByte isStatic
                  { gas := gas, to := to,
                    input := { offset := inputOffset, size := inputSize },
                    output := { offset := outputOffset, size := outputSize } }))
              { gas := gas, to := to,
                input := { offset := inputOffset, size := inputSize },
                output := { offset := outputOffset, size := outputSize } }
          stack := rest } := rfl

theorem runCallStack?_call_eq_none_iff
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (stackState : CallStackState) :
    runCallStack? .call state caller callee apparentValue readByte isStatic
        executor stackState = none ↔
      EvmAsm.Evm64.CallArgsStackDecode.decodeCallStack? stackState.stack = none ∨
        stackRestAfterCall? .call stackState.stack = none := by
  cases stackState with
  | mk stack =>
      simp [runCallStack?]
      cases h_decode :
          EvmAsm.Evm64.CallArgsStackDecode.decodeCallStack? stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterCall? .call stack with
          | none => simp
          | some rest => simp

theorem runCallStack?_staticcall_eq_none_iff
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (stackState : CallStackState) :
    runCallStack? .staticcall state caller callee apparentValue readByte
        isStatic executor stackState = none ↔
      EvmAsm.Evm64.CallArgsStackDecode.decodeStaticCallStack?
          stackState.stack = none ∨
        stackRestAfterCall? .staticcall stackState.stack = none := by
  cases stackState with
  | mk stack =>
      simp [runCallStack?]
      cases h_decode :
          EvmAsm.Evm64.CallArgsStackDecode.decodeStaticCallStack? stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterCall? .staticcall stack with
          | none => simp
          | some rest => simp

theorem runCallStack?_delegatecall_eq_none_iff
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (executor : CallExecutor)
    (stackState : CallStackState) :
    runCallStack? .delegatecall state caller callee apparentValue readByte
        isStatic executor stackState = none ↔
      EvmAsm.Evm64.CallArgsStackDecode.decodeDelegateCallStack?
          stackState.stack = none ∨
        stackRestAfterCall? .delegatecall stackState.stack = none := by
  cases stackState with
  | mk stack =>
      simp [runCallStack?]
      cases h_decode :
          EvmAsm.Evm64.CallArgsStackDecode.decodeDelegateCallStack? stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterCall? .delegatecall stack with
          | none => simp
          | some rest => simp

/--
Distinctive token: CallStackExecutionBridge.runCallStack?_eq_none_iff #114 #107.
-/
theorem runCallStack?_eq_none_iff
    (kind : CallKind) (state : WorldState) (caller callee : Address)
    (apparentValue : Word256) (readByte : MemoryReader) (isStatic : Bool)
    (executor : CallExecutor) (stackState : CallStackState) :
    runCallStack? kind state caller callee apparentValue readByte isStatic
        executor stackState = none ↔
      (kind = .call ∧
        (EvmAsm.Evm64.CallArgsStackDecode.decodeCallStack?
            stackState.stack = none ∨
          stackRestAfterCall? .call stackState.stack = none)) ∨
      (kind = .staticcall ∧
        (EvmAsm.Evm64.CallArgsStackDecode.decodeStaticCallStack?
            stackState.stack = none ∨
          stackRestAfterCall? .staticcall stackState.stack = none)) ∨
      (kind = .delegatecall ∧
        (EvmAsm.Evm64.CallArgsStackDecode.decodeDelegateCallStack?
            stackState.stack = none ∨
          stackRestAfterCall? .delegatecall stackState.stack = none)) := by
  cases kind
  · simp [runCallStack?_call_eq_none_iff]
  · simp [runCallStack?_staticcall_eq_none_iff]
  · simp [runCallStack?_delegatecall_eq_none_iff]

theorem runCallStack?_effects_stack_length
    {kind : CallKind} {state : WorldState} {caller callee : Address}
    {apparentValue : Word256} {readByte : MemoryReader} {isStatic : Bool}
    {executor : CallExecutor} {stackState : CallStackState} {out : CallStackResult}
    (h_run :
      runCallStack? kind state caller callee apparentValue readByte isStatic executor
        stackState = some out) :
    out.effects.stackWords.length = EvmAsm.Evm64.CallArgs.resultCount kind := by
  cases kind <;>
    simp [runCallStack?, CallExecutionBridge.callVisibleEffectsFromResult,
      CallExecutionBridge.staticCallVisibleEffectsFromResult,
      CallExecutionBridge.delegateCallVisibleEffectsFromResult,
      CallResultEffectsBridge.callVisibleEffects,
      CallStackBridge.callStackResult,
      EvmAsm.Evm64.CallArgs.resultCount] at h_run ⊢
  all_goals
    repeat' first | split at h_run | cases h_run | simp at h_run
    simp

end CallStackExecutionBridge

end EvmAsm.EL
