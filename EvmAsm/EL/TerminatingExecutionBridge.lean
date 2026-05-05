/-
  EvmAsm.EL.TerminatingExecutionBridge

  Executable-spec bridge from terminating opcode stack/memory inputs to
  caller-visible and message-call output surfaces (GH #113).
-/

import EvmAsm.EL.TerminatingCallOutput
import EvmAsm.EL.TerminatingCallerVisible
import EvmAsm.EL.TerminatingDataMemory

namespace EvmAsm.EL

namespace TerminatingExecutionBridge

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev MemoryReader := TerminatingDataMemory.MemoryReader
abbrev CallExecutionInput := MessageCallExecution.CallExecutionInput
abbrev CallerVisibleResult := MessageCallExecution.CallerVisibleResult
abbrev CallSideEffects := MessageCallExecution.CallSideEffects
abbrev MessageCallOutput := MessageCallExecution.MessageCallOutput

/-- Caller-visible executable-spec result obtained by reading RETURN/REVERT
    data from memory and then applying the normal message-call visibility
    rules. Distinctive token: TerminatingExecutionBridge.resultFromMemoryCallerVisible. -/
def resultFromMemoryCallerVisible
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    CallerVisibleResult :=
  MessageCallExecution.toCallerVisible input
    (TerminatingDataMemory.resultFromMemory kind state readByte gasRemaining args)

/-- Executable-spec-shaped message-call output obtained by reading
    RETURN/REVERT data from memory and applying the normal side-effect
    visibility rules. -/
def resultFromMemoryMessageCallOutput
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    MessageCallOutput :=
  MessageCallExecution.messageCallOutput_fromResult
    (TerminatingDataMemory.resultFromMemory kind state readByte gasRemaining args)
    effects

theorem resultFromMemoryCallerVisible_eq
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    resultFromMemoryCallerVisible input kind state readByte gasRemaining args =
      TerminatingCallerVisible.terminatingCallerVisibleResult input kind state
        (TerminatingDataMemory.terminatingDataFromMemory readByte args)
        gasRemaining args := rfl

theorem resultFromMemoryMessageCallOutput_eq
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    resultFromMemoryMessageCallOutput kind state readByte gasRemaining args effects =
      TerminatingCallOutput.terminatingMessageCallOutput kind state
        (TerminatingDataMemory.terminatingDataFromMemory readByte args)
        gasRemaining args effects := rfl

theorem resultFromMemoryCallerVisible_status
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemoryCallerVisible input kind state readByte gasRemaining args).status =
      match kind with
      | .stop => CallStatus.success
      | .return_ => CallStatus.success
      | .revert => CallStatus.revert
      | .invalid => CallStatus.failure
      | .selfdestruct => CallStatus.success := by
  exact TerminatingCallerVisible.terminatingCallerVisibleResult_status input kind
    state (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args

theorem resultFromMemoryCallerVisible_state
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemoryCallerVisible input kind state readByte gasRemaining args).state =
      TerminatingCallerVisible.committedTerminatingState input kind state := by
  exact TerminatingCallerVisible.terminatingCallerVisibleResult_state input kind
    state (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args

theorem resultFromMemoryCallerVisible_output
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemoryCallerVisible input kind state readByte gasRemaining args).output =
      TerminatingCallerVisible.propagatedTerminatingOutput kind
        (TerminatingDataMemory.terminatingDataFromMemory readByte args) := by
  exact TerminatingCallerVisible.terminatingCallerVisibleResult_output input kind
    state (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args

theorem resultFromMemoryCallerVisible_gasRemaining
    (input : CallExecutionInput) (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemoryCallerVisible input kind state readByte gasRemaining args).gasRemaining =
      gasRemaining := by
  exact TerminatingCallerVisible.terminatingCallerVisibleResult_gasRemaining input kind
    state (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args

theorem resultFromMemoryMessageCallOutput_status
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (resultFromMemoryMessageCallOutput kind state readByte gasRemaining args effects).status =
      match kind with
      | .stop => CallStatus.success
      | .return_ => CallStatus.success
      | .revert => CallStatus.revert
      | .invalid => CallStatus.failure
      | .selfdestruct => CallStatus.success := by
  exact TerminatingCallOutput.terminatingMessageCallOutput_status kind state
    (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args effects

theorem resultFromMemoryMessageCallOutput_gasLeft
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (resultFromMemoryMessageCallOutput kind state readByte gasRemaining args effects).gasLeft =
      gasRemaining := by
  exact TerminatingCallOutput.terminatingMessageCallOutput_gasLeft kind state
    (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args effects

theorem resultFromMemoryMessageCallOutput_logs
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) (effects : CallSideEffects) :
    (resultFromMemoryMessageCallOutput kind state readByte gasRemaining args effects).logs =
      if EvmAsm.Evm64.TerminatingArgs.isSuccess kind then
        effects.logs
      else
        LogState.empty := by
  exact TerminatingCallOutput.terminatingMessageCallOutput_logs kind state
    (TerminatingDataMemory.terminatingDataFromMemory readByte args)
    gasRemaining args effects

end TerminatingExecutionBridge

end EvmAsm.EL
