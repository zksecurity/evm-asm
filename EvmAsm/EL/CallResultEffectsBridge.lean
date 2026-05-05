/-
  EvmAsm.EL.CallResultEffectsBridge

  Caller-visible CALL-family result effects (GH #114).
-/

import EvmAsm.EL.CallStackBridge

namespace EvmAsm.EL

namespace CallResultEffectsBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallResult := EvmAsm.EL.CallResult
abbrev Byte := EvmAsm.EL.Byte
abbrev Word256 := EvmAsm.EL.Word256

/-- Caller-visible effects of a CALL-family result: the stack result word and
    the capped output bytes copied into the caller output range.

    Distinctive token: CallResultEffectsBridge.callVisibleEffects #114. -/
structure CallVisibleEffects where
  stackWords : List Word256
  outputBytes : List Byte
  deriving Repr

def callVisibleEffects (result : CallResult) (outputRange : MemoryRange) :
    CallVisibleEffects :=
  { stackWords := CallStackBridge.callStackResult result
    outputBytes := CallOutputBridge.copiedOutputForRange result outputRange }

theorem callVisibleEffects_stackWords (result : CallResult) (outputRange : MemoryRange) :
    (callVisibleEffects result outputRange).stackWords =
      CallStackBridge.callStackResult result := rfl

theorem callVisibleEffects_outputBytes (result : CallResult) (outputRange : MemoryRange) :
    (callVisibleEffects result outputRange).outputBytes =
      CallOutputBridge.copiedOutputForRange result outputRange := rfl

theorem callVisibleEffects_stack_length (result : CallResult) (outputRange : MemoryRange) :
    (callVisibleEffects result outputRange).stackWords.length = 1 := rfl

theorem callVisibleEffects_output_length_le_range
    (result : CallResult) (outputRange : MemoryRange) :
    (callVisibleEffects result outputRange).outputBytes.length ≤ outputRange.size.toNat := by
  exact CallOutputBridge.copiedOutputForRange_length_le_range result outputRange

theorem callVisibleEffects_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (outputRange : MemoryRange) :
    callVisibleEffects
        { status := .success, state := state, output := output, gasRemaining := gasRemaining }
        outputRange =
      { stackWords := [1], outputBytes := output.take outputRange.size.toNat } := rfl

theorem callVisibleEffects_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (outputRange : MemoryRange) :
    callVisibleEffects
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining }
        outputRange =
      { stackWords := [0], outputBytes := output.take outputRange.size.toNat } := rfl

theorem callVisibleEffects_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (outputRange : MemoryRange) :
    callVisibleEffects
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        outputRange =
      { stackWords := [0], outputBytes := [] } := by
  simp [callVisibleEffects, CallStackBridge.callStackResult,
    CallOutputBridge.callResultSuccessFlag, CallOutputBridge.copiedOutputForRange_failure]

theorem callVisibleEffects_stack_head_eq_one_iff
    (result : CallResult) (outputRange : MemoryRange) :
    (callVisibleEffects result outputRange).stackWords.head? = some 1 ↔
      result.status = .success := by
  simpa [callVisibleEffects] using
    CallStackBridge.callStackResult_head_eq_one_iff result

end CallResultEffectsBridge

end EvmAsm.EL
