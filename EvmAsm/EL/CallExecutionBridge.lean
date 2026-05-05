/-
  EvmAsm.EL.CallExecutionBridge

  CALL-family execution input bridge from stack-decoded arguments to the
  message-call executor surface (GH #114).
-/

import EvmAsm.EL.CallInputBridge
import EvmAsm.EL.CallResultEffectsBridge

namespace EvmAsm.EL

namespace CallExecutionBridge

abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall
abbrev MemoryReader := CallInputBridge.MemoryReader
abbrev CallExecutionInput := MessageCallExecution.CallExecutionInput
abbrev CallVisibleEffects := CallResultEffectsBridge.CallVisibleEffects

/--
Build the message-call executor input for CALL from stack-decoded arguments,
caller/callee addresses, a world state, and a pure memory reader.

Distinctive token: CallExecutionBridge.callInputFromMemory #114.
-/
def callInputFromMemory
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (isStatic : Bool) (args : CallArgs) : CallExecutionInput :=
  { state := state
    frame := CallInputBridge.callFrameFromMemory caller callee readByte isStatic args }

def staticCallInputFromMemory
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (args : StaticCallArgs) : CallExecutionInput :=
  { state := state
    frame := CallInputBridge.staticCallFrameFromMemory caller callee readByte args }

def delegateCallInputFromMemory
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (args : DelegateCallArgs) :
    CallExecutionInput :=
  { state := state
    frame := CallInputBridge.delegateCallFrameFromMemory caller callee apparentValue
      readByte isStatic args }

theorem callInputFromMemory_state
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (isStatic : Bool) (args : CallArgs) :
    (callInputFromMemory state caller callee readByte isStatic args).state = state := rfl

theorem staticCallInputFromMemory_state
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (args : StaticCallArgs) :
    (staticCallInputFromMemory state caller callee readByte args).state = state := rfl

theorem delegateCallInputFromMemory_state
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallInputFromMemory state caller callee apparentValue readByte isStatic args).state =
      state := rfl

theorem callInputFromMemory_frame
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (isStatic : Bool) (args : CallArgs) :
    (callInputFromMemory state caller callee readByte isStatic args).frame =
      CallInputBridge.callFrameFromMemory caller callee readByte isStatic args := rfl

theorem staticCallInputFromMemory_frame
    (state : WorldState) (caller callee : Address) (readByte : MemoryReader)
    (args : StaticCallArgs) :
    (staticCallInputFromMemory state caller callee readByte args).frame =
      CallInputBridge.staticCallFrameFromMemory caller callee readByte args := rfl

theorem delegateCallInputFromMemory_frame
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (readByte : MemoryReader) (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallInputFromMemory state caller callee apparentValue readByte isStatic args).frame =
      CallInputBridge.delegateCallFrameFromMemory caller callee apparentValue
        readByte isStatic args := rfl

theorem callInputFromMemory_outputRange
    (args : CallArgs) :
    CallArgsBridge.callOutputRange args = args.output := rfl

theorem staticCallInputFromMemory_outputRange
    (args : StaticCallArgs) :
    CallArgsBridge.staticCallOutputRange args = args.output := rfl

theorem delegateCallInputFromMemory_outputRange
    (args : DelegateCallArgs) :
    CallArgsBridge.delegateCallOutputRange args = args.output := rfl

def callVisibleEffectsFromResult (result : CallResult) (args : CallArgs) :
    CallVisibleEffects :=
  CallResultEffectsBridge.callVisibleEffects result (CallArgsBridge.callOutputRange args)

def staticCallVisibleEffectsFromResult (result : CallResult) (args : StaticCallArgs) :
    CallVisibleEffects :=
  CallResultEffectsBridge.callVisibleEffects result (CallArgsBridge.staticCallOutputRange args)

def delegateCallVisibleEffectsFromResult (result : CallResult) (args : DelegateCallArgs) :
    CallVisibleEffects :=
  CallResultEffectsBridge.callVisibleEffects result (CallArgsBridge.delegateCallOutputRange args)

theorem callVisibleEffectsFromResult_stack_length (result : CallResult) (args : CallArgs) :
    (callVisibleEffectsFromResult result args).stackWords.length = 1 := rfl

theorem staticCallVisibleEffectsFromResult_stack_length
    (result : CallResult) (args : StaticCallArgs) :
    (staticCallVisibleEffectsFromResult result args).stackWords.length = 1 := rfl

theorem delegateCallVisibleEffectsFromResult_stack_length
    (result : CallResult) (args : DelegateCallArgs) :
    (delegateCallVisibleEffectsFromResult result args).stackWords.length = 1 := rfl

theorem callVisibleEffectsFromResult_output_length_le
    (result : CallResult) (args : CallArgs) :
    (callVisibleEffectsFromResult result args).outputBytes.length ≤ args.output.size.toNat := by
  exact CallResultEffectsBridge.callVisibleEffects_output_length_le_range result args.output

theorem staticCallVisibleEffectsFromResult_output_length_le
    (result : CallResult) (args : StaticCallArgs) :
    (staticCallVisibleEffectsFromResult result args).outputBytes.length ≤
      args.output.size.toNat := by
  exact CallResultEffectsBridge.callVisibleEffects_output_length_le_range result args.output

theorem delegateCallVisibleEffectsFromResult_output_length_le
    (result : CallResult) (args : DelegateCallArgs) :
    (delegateCallVisibleEffectsFromResult result args).outputBytes.length ≤
      args.output.size.toNat := by
  exact CallResultEffectsBridge.callVisibleEffects_output_length_le_range result args.output

end CallExecutionBridge

end EvmAsm.EL
