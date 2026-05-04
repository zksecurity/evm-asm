/-
  EvmAsm.EL.TerminatingCallerVisible

  Bridge from terminating opcode results to the executable-spec caller-visible
  message-call result surface (GH #113 / #121).
-/

import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingCallerVisible

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev CallExecutionInput := MessageCallExecution.CallExecutionInput
abbrev CallerVisibleResult := MessageCallExecution.CallerVisibleResult

/-- Caller-visible state selected by a terminating opcode result. Successful
    terminations commit `state`; reverts and failures restore `input.state`.
    Distinctive token: committedTerminatingState. -/
def committedTerminatingState
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState) :
    WorldState :=
  match kind with
  | .stop => state
  | .return_ => state
  | .revert => input.state
  | .invalid => input.state
  | .selfdestruct => state

/-- Caller-visible output selected by a terminating opcode result. RETURN and
    REVERT propagate their memory slice; STOP, INVALID, and SELFDESTRUCT expose
    empty output. -/
def propagatedTerminatingOutput (kind : TerminatingKind) (data : List Byte) :
    List Byte :=
  match kind with
  | .stop => []
  | .return_ => data
  | .revert => data
  | .invalid => []
  | .selfdestruct => []

/-- Package a terminating-opcode result through `toCallerVisible`, the
    executable-spec caller-visible result surface. Distinctive token:
    terminatingCallerVisibleResult. -/
def terminatingCallerVisibleResult
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (data : List Byte) (gasRemaining : Nat) (args : TerminatingArgs) :
    CallerVisibleResult :=
  MessageCallExecution.toCallerVisible input
    (TerminatingArgsBridge.mkResultFromArgs kind state data gasRemaining args)

theorem terminatingCallerVisibleResult_status
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (data : List Byte) (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input kind state data gasRemaining args).status =
      match kind with
      | .stop => CallStatus.success
      | .return_ => CallStatus.success
      | .revert => CallStatus.revert
      | .invalid => CallStatus.failure
      | .selfdestruct => CallStatus.success := by
  cases kind <;> rfl

theorem terminatingCallerVisibleResult_state
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (data : List Byte) (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input kind state data gasRemaining args).state =
      committedTerminatingState input kind state := by
  cases kind <;> rfl

theorem terminatingCallerVisibleResult_output
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (data : List Byte) (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input kind state data gasRemaining args).output =
      propagatedTerminatingOutput kind data := by
  cases kind <;> rfl

theorem terminatingCallerVisibleResult_gasRemaining
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (data : List Byte) (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input kind state data gasRemaining args).gasRemaining =
      gasRemaining := by
  cases kind <;> rfl

theorem terminatingCallerVisibleResult_return_state
    (input : CallExecutionInput) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input .return_ state data gasRemaining args).state =
      state := rfl

theorem terminatingCallerVisibleResult_revert_state
    (input : CallExecutionInput) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input .revert state data gasRemaining args).state =
      input.state := rfl

theorem terminatingCallerVisibleResult_return_output
    (input : CallExecutionInput) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input .return_ state data gasRemaining args).output =
      data := rfl

theorem terminatingCallerVisibleResult_revert_output
    (input : CallExecutionInput) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (terminatingCallerVisibleResult input .revert state data gasRemaining args).output =
      data := rfl

end TerminatingCallerVisible

end EvmAsm.EL
