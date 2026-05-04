/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect bridge (GH #113).
-/

import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace SelfdestructEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects

/-- Pure result surface for SELFDESTRUCT state and side effects. -/
structure SelfdestructEffect where
  state : WorldState
  sideEffects : CallSideEffects

/-- Post-Cancun SELFDESTRUCT transfers the account balance to the beneficiary
    and touches the beneficiary, but it does not schedule account deletion.
    Distinctive token: SelfdestructEffects.postCancunSelfdestructEffect. -/
def postCancunSelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) : SelfdestructEffect :=
  { state :=
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance
    sideEffects :=
      { refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := [beneficiary] } }

theorem postCancunSelfdestructEffect_state
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).state =
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance := rfl

theorem postCancunSelfdestructEffect_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.refundCounter =
      0 := rfl

theorem postCancunSelfdestructEffect_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.logs =
      LogState.empty := rfl

theorem postCancunSelfdestructEffect_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.accountsToDelete =
      [] := rfl

theorem postCancunSelfdestructEffect_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem postCancunSelfdestructEffect_accountBalance?
    {state : WorldState} {account beneficiary : Address} {accountRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_account : WorldState.getAccount state account = some accountRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        account =
      some (accountBalance - accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_callerBalance?
    accountBalance beneficiaryBalance accountBalance h_account h_ne

theorem postCancunSelfdestructEffect_beneficiaryBalance?
    {state : WorldState} {account beneficiary : Address} {beneficiaryRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_beneficiary : WorldState.getAccount state beneficiary = some beneficiaryRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        beneficiary =
      some (beneficiaryBalance + accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_calleeBalance?
    accountBalance beneficiaryBalance accountBalance h_beneficiary h_ne

end SelfdestructEffects

end EvmAsm.EL
