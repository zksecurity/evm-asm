/-
  EvmAsm.EL.MessageCallExecution

  Pure execution hooks for message-call processing (GH #121).
-/

import EvmAsm.EL.Logs
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

/-- Side effects surfaced by the executable-spec `MessageCallOutput`. The
    output bytes and committed state remain in `CallResult`/`CallerVisibleResult`;
    this record tracks the auxiliary effects that are cleared on errors. -/
structure CallSideEffects where
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address

namespace CallSideEffects

def empty : CallSideEffects :=
  { refundCounter := 0
    logs := LogState.empty
    accountsToDelete := []
    touchedAccounts := [] }

@[simp] theorem refundCounter_empty : empty.refundCounter = 0 := rfl
@[simp] theorem logs_empty : empty.logs = LogState.empty := rfl
@[simp] theorem accountsToDelete_empty : empty.accountsToDelete = [] := rfl
@[simp] theorem touchedAccounts_empty : empty.touchedAccounts = [] := rfl

end CallSideEffects

/-- Executable-spec-shaped message-call output surface. Mirrors the Python
    `MessageCallOutput` fields while using `status` as the Lean error summary. -/
structure MessageCallOutput where
  gasLeft : Nat
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address
  status : CallStatus

/-- Successful calls keep their side effects; reverts and failures clear them,
    matching the executable spec's `if evm.error` branch. -/
def visibleSideEffects (result : CallResult) (effects : CallSideEffects) :
    CallSideEffects :=
  match result.status with
  | .success => effects
  | .revert => CallSideEffects.empty
  | .failure => CallSideEffects.empty

/-- Build the executable-spec-shaped output from the verified call result plus
    auxiliary side effects. Distinctive token: messageCallOutput_fromResult. -/
def messageCallOutput_fromResult (result : CallResult) (effects : CallSideEffects) :
    MessageCallOutput :=
  let visible := visibleSideEffects result effects
  { gasLeft := result.gasRemaining
    refundCounter := visible.refundCounter
    logs := visible.logs
    accountsToDelete := visible.accountsToDelete
    touchedAccounts := visible.touchedAccounts
    status := result.status }

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

theorem visibleSideEffects_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    visibleSideEffects
        { status := .success, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      effects := rfl

theorem visibleSideEffects_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    visibleSideEffects
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      CallSideEffects.empty := rfl

theorem visibleSideEffects_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    visibleSideEffects
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      CallSideEffects.empty := rfl

theorem messageCallOutput_fromResult_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    messageCallOutput_fromResult
        { status := .success, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      { gasLeft := gasRemaining
        refundCounter := effects.refundCounter
        logs := effects.logs
        accountsToDelete := effects.accountsToDelete
        touchedAccounts := effects.touchedAccounts
        status := .success } := rfl

theorem messageCallOutput_fromResult_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    messageCallOutput_fromResult
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      { gasLeft := gasRemaining
        refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := []
        status := .revert } := rfl

theorem messageCallOutput_fromResult_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (effects : CallSideEffects) :
    messageCallOutput_fromResult
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        effects =
      { gasLeft := gasRemaining
        refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := []
        status := .failure } := rfl

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
