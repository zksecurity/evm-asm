/-
  EvmAsm.Evm64.HandlerLoopSimulationBridge

  Lift handler-table dispatch agreement through the pure interpreter loop
  simulation surface (GH #107 / GH #109).
-/

import EvmAsm.Evm64.HandlerLoopBridge
import EvmAsm.Evm64.InterpreterLoopSimulation

namespace EvmAsm.Evm64

namespace HandlerLoopSimulationBridge

/--
If a handler table dispatches each decoded opcode like the executable-spec
handler, then the table-backed interpreter loop matches the executable-spec
loop for every nSteps budget.

Distinctive token: HandlerLoopSimulationBridge.loopFuel_table_matchesSpec #107 #109.
-/
theorem loopFuel_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    ∀ (nSteps : Nat) (state : EvmState),
      InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state =
        InterpreterLoop.loopFuel spec nSteps state := by
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

theorem stepWithTable_matchesSpec_status
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (state : EvmState) :
    (InterpreterLoop.stepWithHandler (HandlerLoopBridge.toLoopHandler table) state).status =
      (InterpreterLoop.stepWithHandler spec state).status := by
  rw [stepWithTable_matchesSpec table spec h_dispatch state]

theorem loopFuel_table_matchesSpec_at
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state =
      InterpreterLoop.loopFuel spec nSteps state := by
  exact loopFuel_table_matchesSpec table spec h_dispatch nSteps state

theorem loopFuel_table_matchesSpec_at_status
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state)
    (nSteps : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel (HandlerLoopBridge.toLoopHandler table) nSteps state).status =
      (InterpreterLoop.loopFuel spec nSteps state).status := by
  rw [loopFuel_table_matchesSpec_at table spec h_dispatch nSteps state]

theorem loopResultsMatch_table_matchesSpec
    (table : HandlerTable) (spec : InterpreterLoop.Handler)
    (h_dispatch : ∀ (opcode : EvmOpcode) (state : EvmState),
      InterpreterLoop.decodeCurrentOpcode? state = some opcode →
        HandlerTable.dispatchOpcode table opcode state = spec opcode state) :
    InterpreterLoopSimulation.LoopResultsMatch
      (HandlerLoopBridge.toLoopHandler table) spec := by
  exact loopFuel_table_matchesSpec table spec h_dispatch

end HandlerLoopSimulationBridge

end EvmAsm.Evm64
