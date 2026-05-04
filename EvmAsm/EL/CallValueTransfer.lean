/-
  EvmAsm.EL.CallValueTransfer

  Pure CALL value-transfer world-state effect (GH #114).  This module
  records the balance movement for the value-transferring CALL case.
  Balance sufficiency, account creation rules, and the full handler
  stack/state specs remain later slices.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.MessageCall

namespace EvmAsm.EL
namespace CallValueTransfer

/-- Debit `value` from the caller and credit it to the callee.

    This helper assumes the caller/callee account records already exist
    and the caller has sufficient balance.  Those preconditions are
    intentionally left to the later executable handler/spec layer; here
    we expose the pure state transformer and projection lemmas. -/
def transferValue
    (state : WorldState) (caller callee : Address)
    (callerBalance calleeBalance value : Word256) : WorldState :=
  let state' := WorldState.setAccountBalance state caller (callerBalance - value)
  WorldState.setAccountBalance state' callee (calleeBalance + value)

/-- Apply the value-transfer effect carried by a message-call frame, given the
    concrete pre-call balances for caller and callee. -/
def transferFrameValue
    (state : WorldState) (frame : CallFrame)
    (callerBalance calleeBalance : Word256) : WorldState :=
  transferValue state frame.caller frame.callee callerBalance calleeBalance
    frame.transferredValue

theorem transferValue_state
    (state : WorldState) (caller callee : Address)
    (callerBalance calleeBalance value : Word256) :
    transferValue state caller callee callerBalance calleeBalance value =
      WorldState.setAccountBalance
        (WorldState.setAccountBalance state caller (callerBalance - value))
        callee (calleeBalance + value) := rfl

theorem transferFrameValue_eq_transferValue
    (state : WorldState) (frame : CallFrame) (callerBalance calleeBalance : Word256) :
    transferFrameValue state frame callerBalance calleeBalance =
      transferValue state frame.caller frame.callee callerBalance calleeBalance
        frame.transferredValue := rfl

theorem transferValue_callerBalance?
    {state : WorldState} {caller callee : Address}
    {callerAccount : Account}
    (callerBalance calleeBalance value : Word256)
    (h_caller : WorldState.getAccount state caller = some callerAccount)
    (h_ne : caller ≠ callee) :
    WorldState.accountBalance?
        (transferValue state caller callee callerBalance calleeBalance value)
        caller =
      some (callerBalance - value) := by
  rw [transferValue_state]
  have h_after_caller :
      WorldState.getAccount
          (WorldState.setAccountBalance state caller (callerBalance - value))
          caller =
        some { callerAccount with balance := callerBalance - value } :=
    WorldState.getAccount_setAccountBalance_same h_caller
  rw [WorldState.accountBalance?, WorldState.getAccount_setAccountBalance_ne]
  · simp [h_after_caller]
  · exact h_ne

theorem transferValue_calleeBalance?
    {state : WorldState} {caller callee : Address}
    {calleeAccount : Account}
    (callerBalance calleeBalance value : Word256)
    (h_callee : WorldState.getAccount state callee = some calleeAccount)
    (h_ne : caller ≠ callee) :
    WorldState.accountBalance?
        (transferValue state caller callee callerBalance calleeBalance value)
        callee =
      some (calleeBalance + value) := by
  rw [transferValue_state]
  exact WorldState.accountBalance?_setAccountBalance_same
    (state := WorldState.setAccountBalance state caller (callerBalance - value))
    (addr := callee)
    (account := calleeAccount)
    (by
      rw [WorldState.getAccount_setAccountBalance_ne]
      · exact h_callee
      · exact fun h_eq => h_ne h_eq.symm)

theorem transferValue_otherAccount
    (state : WorldState) {caller callee other : Address}
    (callerBalance calleeBalance value : Word256)
    (h_other_caller : other ≠ caller) (h_other_callee : other ≠ callee) :
    WorldState.getAccount
        (transferValue state caller callee callerBalance calleeBalance value)
        other =
      WorldState.getAccount state other := by
  rw [transferValue_state]
  rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_other_callee)]
  rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_other_caller)]

theorem transferFrameValue_forStaticCall
    (state : WorldState) (caller callee : Address) (input : List Byte) (gas : Nat)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue state (CallFrame.forStaticCall caller callee input gas)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance 0 := rfl

theorem transferFrameValue_forDelegateCall
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (input : List Byte) (gas : Nat) (isStatic : Bool)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue
        state
        (CallFrame.forDelegateCall caller callee apparentValue input gas isStatic)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance 0 := rfl

theorem transferFrameValue_forCall
    (state : WorldState) (caller callee : Address) (value : Word256)
    (input : List Byte) (gas : Nat) (isStatic : Bool)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue
        state (CallFrame.forCall caller callee value input gas isStatic)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance value := rfl

end CallValueTransfer
end EvmAsm.EL
