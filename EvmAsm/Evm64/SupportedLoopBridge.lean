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

theorem stepWithSupportedHandler_of_lookup
    {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = handler state := by
  rw [stepWithSupportedHandler_of_decode h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state

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

theorem stepWithSupportedHandler_missing_invalid
    {state : EvmState} {opcode : EvmOpcode}
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = none) :
    InterpreterLoop.stepWithHandler supportedLoopHandler state = state.invalid := by
  exact HandlerLoopBridge.stepWithTableHandler_missing_invalid h_decode h_lookup

theorem loopFuel_supported_succ_running_decode
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps
        (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable opcode state) := by
  exact HandlerLoopBridge.loopFuel_succ_running_decode
    SupportedHandlers.supportedHandlerTable nSteps h_status h_decode

theorem loopFuel_supported_succ_running_lookup
    (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode)
    (h_lookup : SupportedHandlers.supportedHandlerTable opcode = some handler) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps (handler state) := by
  rw [loopFuel_supported_succ_running_decode nSteps h_status h_decode]
  rw [SupportedHandlers.dispatchOpcode_of_lookup h_lookup state]

theorem loopFuel_supported_succ_running_STOP
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .STOP) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.stop := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_STOP

theorem loopFuel_supported_succ_running_INVALID
    (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some .INVALID) :
    InterpreterLoop.loopFuel supportedLoopHandler (nSteps + 1) state =
      InterpreterLoop.loopFuel supportedLoopHandler nSteps state.invalid := by
  exact loopFuel_supported_succ_running_lookup nSteps h_status h_decode
    SupportedHandlers.supportedHandlerTable_INVALID

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

end SupportedLoopBridge

end EvmAsm.Evm64
