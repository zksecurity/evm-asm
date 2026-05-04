/-
  EvmAsm.EL.TerminatingCallOutput

  Bridge from terminating opcode results to executable-spec-shaped
  message-call output (GH #113 / #121).
-/

import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingCallOutput

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev CallSideEffects := MessageCallExecution.CallSideEffects
abbrev MessageCallOutput := MessageCallExecution.MessageCallOutput

/-- Package a terminating-opcode call result into the executable-spec-shaped
    message-call output surface. Distinctive token: terminatingMessageCallOutput. -/
def terminatingMessageCallOutput
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    MessageCallOutput :=
  MessageCallExecution.messageCallOutput_fromResult
    (TerminatingArgsBridge.mkResultFromArgs kind state data gasRemaining args)
    effects

theorem terminatingMessageCallOutput_gasLeft
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).gasLeft =
      gasRemaining := by
  cases kind <;> rfl

theorem terminatingMessageCallOutput_status
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).status =
      match kind with
      | .stop => CallStatus.success
      | .return_ => CallStatus.success
      | .revert => CallStatus.revert
      | .invalid => CallStatus.failure
      | .selfdestruct => CallStatus.success := by
  cases kind <;> rfl

theorem terminatingMessageCallOutput_logs
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).logs =
      if EvmAsm.Evm64.TerminatingArgs.isSuccess kind then
        effects.logs
      else
        LogState.empty := by
  cases kind <;> rfl

theorem terminatingMessageCallOutput_refundCounter
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).refundCounter =
      if EvmAsm.Evm64.TerminatingArgs.isSuccess kind then
        effects.refundCounter
      else
        0 := by
  cases kind <;> rfl

theorem terminatingMessageCallOutput_accountsToDelete
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).accountsToDelete =
      if EvmAsm.Evm64.TerminatingArgs.isSuccess kind then
        effects.accountsToDelete
      else
        [] := by
  cases kind <;> rfl

theorem terminatingMessageCallOutput_touchedAccounts
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (terminatingMessageCallOutput kind state data gasRemaining args effects).touchedAccounts =
      if EvmAsm.Evm64.TerminatingArgs.isSuccess kind then
        effects.touchedAccounts
      else
        [] := by
  cases kind <;> rfl

end TerminatingCallOutput

end EvmAsm.EL
