/-
  EvmAsm.EL.MessageCallExecution

  Pure execution hooks for message-call processing (GH #121).
-/

import EvmAsm.EL.MessageCall

namespace EvmAsm.EL

namespace MessageCallExecution

/-- Input surface for executing one message-call frame against a world state. -/
structure CallExecutionInput where
  state : WorldState
  frame : CallFrame

/-- Abstract executor hook for the EVM interpreter or an executable-spec bridge. -/
abbrev CallExecutor := CallExecutionInput → CallResult

/-- A result consumes no more gas than the frame supplied to the call. -/
def callGasBounded (input : CallExecutionInput) (result : CallResult) : Prop :=
  result.gasRemaining ≤ input.frame.gas

/-- Successful calls commit their returned state; reverts and failures restore
    the caller-visible world state from before the call. -/
def committedState (input : CallExecutionInput) (result : CallResult) : WorldState :=
  match result.status with
  | .success => result.state
  | .revert => input.state
  | .failure => input.state

/-- Output bytes propagated back to the caller. Reverts preserve their return
    data, while failures expose an empty output. -/
def propagatedOutput (result : CallResult) : List Byte :=
  match result.status with
  | .success => result.output
  | .revert => result.output
  | .failure => []

/-- Caller-visible execution summary used by transaction and CALL-family layers. -/
structure CallerVisibleResult where
  status : CallStatus
  state : WorldState
  output : List Byte
  gasRemaining : Nat

def toCallerVisible (input : CallExecutionInput) (result : CallResult) :
    CallerVisibleResult :=
  { status := result.status
    state := committedState input result
    output := propagatedOutput result
    gasRemaining := result.gasRemaining }

theorem committedState_success (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    committedState input
        { status := .success, state := state, output := output, gasRemaining := gasRemaining } =
      state := rfl

theorem committedState_revert (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    committedState input
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining } =
      input.state := rfl

theorem committedState_failure (input : CallExecutionInput)
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    committedState input
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining } =
      input.state := rfl

theorem propagatedOutput_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    propagatedOutput
        { status := .success, state := state, output := output, gasRemaining := gasRemaining } =
      output := rfl

theorem propagatedOutput_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    propagatedOutput
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining } =
      output := rfl

theorem propagatedOutput_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    propagatedOutput
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining } =
      [] := rfl

theorem callGasBounded_of_le {input : CallExecutionInput} {result : CallResult}
    (h_le : result.gasRemaining ≤ input.frame.gas) :
    callGasBounded input result := h_le

theorem toCallerVisible_status (input : CallExecutionInput) (result : CallResult) :
    (toCallerVisible input result).status = result.status := rfl

theorem toCallerVisible_state (input : CallExecutionInput) (result : CallResult) :
    (toCallerVisible input result).state = committedState input result := rfl

theorem toCallerVisible_output (input : CallExecutionInput) (result : CallResult) :
    (toCallerVisible input result).output = propagatedOutput result := rfl

end MessageCallExecution

end EvmAsm.EL
