/-
  EvmAsm.EL.CallStackBridge

  CALL-family stack-result bridge for GH #114.
-/

import EvmAsm.EL.CallOutputBridge

namespace EvmAsm.EL

namespace CallStackBridge

abbrev CallResult := EvmAsm.EL.CallResult
abbrev Word256 := EvmAsm.EL.Word256

/--
The CALL-family opcodes push exactly one stack word: 1 for success, 0 for
revert/failure.

Distinctive token: CallStackBridge.callStackResult #114.
-/
def callStackResult (result : CallResult) : List Word256 :=
  [CallOutputBridge.callResultSuccessFlag result]

theorem callStackResult_length (result : CallResult) :
    (callStackResult result).length = 1 := rfl

theorem callStackResult_head? (result : CallResult) :
    (callStackResult result).head? =
      some (CallOutputBridge.callResultSuccessFlag result) := rfl

theorem callStackResult_get_zero (result : CallResult) :
    (callStackResult result)[0]? =
      some (CallOutputBridge.callResultSuccessFlag result) := rfl

theorem callStackResult_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callStackResult
        { status := .success, state := state, output := output, gasRemaining := gasRemaining } =
      [1] := rfl

theorem callStackResult_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callStackResult
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining } =
      [0] := rfl

theorem callStackResult_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callStackResult
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining } =
      [0] := rfl

theorem callStackResult_head_eq_one_iff (result : CallResult) :
    (callStackResult result).head? = some 1 ↔ result.status = .success := by
  cases result with
  | mk status state output gasRemaining =>
      cases status <;> simp [callStackResult, CallOutputBridge.callResultSuccessFlag]

theorem callStackResult_get_zero_eq_one_iff (result : CallResult) :
    (callStackResult result)[0]? = some 1 ↔ result.status = .success := by
  simpa [callStackResult]
    using CallOutputBridge.callResultSuccessFlag_eq_one_iff result

end CallStackBridge

end EvmAsm.EL
