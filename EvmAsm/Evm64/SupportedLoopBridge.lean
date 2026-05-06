/-
  EvmAsm.Evm64.SupportedLoopBridge

  Concrete adapter from the supported pure handler table to the interpreter
  loop (GH #107 / GH #108).
-/

import EvmAsm.Evm64.HandlerLoopBridge
import EvmAsm.Evm64.SupportedHandlers

namespace EvmAsm.Evm64

namespace SupportedLoopBridge

/--
Interpreter-loop handler backed by every pure opcode handler currently wired
into `SupportedHandlers.supportedHandlerTable`.

Distinctive token: SupportedLoopBridge.supportedLoopHandler #107 #108.
-/
def supportedLoopHandler : InterpreterLoop.Handler :=
  HandlerLoopBridge.toLoopHandler SupportedHandlers.supportedHandlerTable

@[simp] theorem supportedLoopHandler_apply
    (opcode : EvmOpcode) (state : EvmState) :
    supportedLoopHandler opcode state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state := rfl

theorem stepWithSupportedHandler_of_decode
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state := by
  exact HandlerLoopBridge.stepWithTableHandler_of_decode
    SupportedHandlers.supportedHandlerTable h_decode

theorem stepWithSupportedHandler_of_decode_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state).status := by
  rw [stepWithSupportedHandler_of_decode h_decode]

theorem stepWithSupportedHandler_of_lookup
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = handler state := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state

theorem stepWithSupportedHandler_of_lookup_status
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      (handler state).status := by
  rw [stepWithSupportedHandler_of_lookup h_decode h_lookup]

/--
When the supported interpreter loop decodes a valid PUSH opcode, the one-step
handler has the same bundled PC and stack effect as the executable PUSH bridge.

Distinctive token:
SupportedLoopBridge.stepWithSupportedHandler_PUSH_effectFromCode
#101 #107 #108.
-/
theorem stepWithSupportedHandler_PUSH_effectFromCode
    {state : EvmState} {n : Nat}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (InterpreterLoop.stepWithHandler supportedLoopHandler state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    h_valid state

theorem stepWithSupportedHandler_PUSH_status
    {state : EvmState} {n : Nat}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_of_valid_status
    h_valid state

theorem stepWithSupportedHandler_DUP_status_of_some
    {state : EvmState} {n : Nat} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.DUP n))
    (h_valid : EvmOpcode.validDupIndex n = true)
    (h_stack : DupSwapHandlers.dupStack? n state.stack = some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_DUP_of_valid_status_of_some
    h_valid h_stack

theorem stepWithSupportedHandler_SWAP_status_of_some
    {state : EvmState} {n : Nat} {stack' : List EvmWord}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state =
      some (EvmOpcode.SWAP n))
    (h_valid : EvmOpcode.validSwapIndex n = true)
    (h_stack : DupSwapHandlers.swapStack? n state.stack = some stack') :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      state.status := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_SWAP_of_valid_status_of_some
    h_valid h_stack

/--
When the combined supported loop decodes STOP, one interpreter step terminates
successfully.

Distinctive token: SupportedLoopBridge.stepWithSupportedHandler_STOP #107 #108 #113.
-/
theorem stepWithSupportedHandler_STOP
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.stop := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_STOP

theorem stepWithSupportedHandler_STOP_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .stopped := by
  rw [stepWithSupportedHandler_STOP h_decode]
  exact EvmState.stop_status state

/--
When the combined supported loop decodes INVALID, one interpreter step enters
the invalid/error state.

Distinctive token: SupportedLoopBridge.stepWithSupportedHandler_INVALID #107 #108 #113.
-/
theorem stepWithSupportedHandler_INVALID
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.invalid := by
  exact stepWithSupportedHandler_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_INVALID

theorem stepWithSupportedHandler_INVALID_status
    {state : EvmState}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_INVALID h_decode]
  exact EvmState.invalid_status state

theorem stepWithSupportedHandler_missing_invalid
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.invalid := by
  exact HandlerLoopBridge.stepWithTableHandler_missing_invalid h_decode h_lookup

theorem stepWithSupportedHandler_missing_invalid_status
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    (InterpreterLoop.stepWithHandler supportedLoopHandler state).status =
      .error := by
  rw [stepWithSupportedHandler_missing_invalid h_decode h_lookup]
  exact EvmState.invalid_status state

theorem loopFuel_supported_succ_running_decode
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state) := by
  exact HandlerLoopBridge.loopFuel_succ_running_decode
    SupportedHandlers.supportedHandlerTable nSteps h_status h_decode

theorem loopFuel_supported_succ_running_decode_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state)).status := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]

theorem loopFuel_supported_succ_running_lookup
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps (handler state) := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]
  rw [SupportedHandlers.dispatchOpcode_of_lookup h_lookup state]

theorem loopFuel_supported_succ_running_lookup_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      (InterpreterLoop.loopFuel supportedLoopHandler nSteps (handler state)).status := by
  rw [loopFuel_supported_succ_running_lookup nSteps h_status h_decode h_lookup]

theorem loopFuel_supported_succ_running_STOP
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_STOP

theorem loopFuel_supported_stop_fixed :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop = state.stop
  | 0, _ => rfl
  | nSteps + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_supported_stop_fixed_status
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop).status =
      .stopped := by
  rw [loopFuel_supported_stop_fixed nSteps state]
  exact EvmState.stop_status state

theorem loopFuel_supported_succ_running_STOP_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .stopped := by
  rw [loopFuel_supported_succ_running_STOP nSteps h_status h_decode]
  exact loopFuel_supported_stop_fixed_status nSteps state

theorem loopFuel_supported_succ_running_INVALID
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_INVALID

theorem loopFuel_supported_invalid_fixed :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid = state.invalid
  | 0, _ => rfl
  | nSteps + 1, state => by
      simp [InterpreterLoop.loopFuel]

theorem loopFuel_supported_invalid_fixed_status
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid).status =
      .error := by
  rw [loopFuel_supported_invalid_fixed nSteps state]
  exact EvmState.invalid_status state

theorem loopFuel_supported_succ_running_INVALID_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_succ_running_INVALID nSteps h_status h_decode]
  exact loopFuel_supported_invalid_fixed_status nSteps state

theorem loopFuel_supported_missing_invalid
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]
  exact congrArg (InterpreterLoop.loopFuel supportedLoopHandler nSteps)
    (HandlerTable.dispatchOpcode_none h_lookup state)

theorem loopFuel_supported_missing_invalid_status
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_missing_invalid nSteps h_status h_decode h_lookup]
  exact loopFuel_supported_invalid_fixed_status nSteps state

theorem loopFuel_supported_succ_running_unsupported_invalid
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid :=
  HandlerLoopBridge.loopFuel_succ_running_unsupported_invalid
    SupportedHandlers.supportedHandlerTable nSteps h_status h_decode

theorem loopFuel_supported_succ_running_unsupported_status
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state).status =
      .error := by
  rw [loopFuel_supported_succ_running_unsupported_invalid nSteps h_status h_decode]
  exact loopFuel_supported_invalid_fixed_status nSteps state

end SupportedLoopBridge

end EvmAsm.Evm64
