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
