/-
  EvmAsm.Evm64.HandlerLoopSimulationBridge

  Lift handler-table dispatch agreement through the pure interpreter loop
  simulation surface (GH #107 / GH #109).
-/

import EvmAsm.Evm64.HandlerLoopBridge

namespace EvmAsm.Evm64

namespace HandlerLoopSimulationBridge

/--
If a handler table dispatches each decoded opcode like the executable-spec
handler, then the table-backed interpreter loop matches the executable-spec
loop for every fuel budget.

Distinctive token: HandlerLoopSimulationBridge.loopFuel_table_matchesSpec #107 #109.
-/
theorem loopFuel_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    ∀ (fuel : Nat) (state : EvmState),
      InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) fuel state =
        InterpreterLoop.loopFuel spec fuel state := by
  exact InterpreterSimulation.loopFuel_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch)

theorem stepWithTable_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state =
      InterpreterLoop.stepWithHandler spec state := by
  exact InterpreterSimulation.stepWithHandler_matchesSpec
    (HandlerLoopBridge.handlerMatchesSpec_of_dispatch_eq table spec h_dispatch) state

theorem loopFuel_table_matchesSpec_at
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (fuel : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) fuel state =
      InterpreterLoop.loopFuel spec fuel state := by
  exact loopFuel_table_matchesSpec table spec h_dispatch fuel state

end HandlerLoopSimulationBridge

end EvmAsm.Evm64
