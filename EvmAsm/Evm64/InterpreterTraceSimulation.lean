/-
  EvmAsm.Evm64.InterpreterTraceSimulation

  Trace-level simulation bridge for the pure interpreter loop (GH #109).
-/

import EvmAsm.Evm64.InterpreterSimulation
import EvmAsm.Evm64.InterpreterTrace

namespace EvmAsm.Evm64

namespace InterpreterTraceSimulation

/--
Per-opcode handler agreement preserves the decoded-opcode trace of the
executable fuel loop.

Distinctive token: InterpreterTraceSimulation.loopTrace_matchesSpec #109.
-/
theorem loopTrace_matchesSpec
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec) :
    ∀ (fuel : Nat) (state : EvmState),
      InterpreterTrace.loopTrace impl fuel state =
        InterpreterTrace.loopTrace spec fuel state
  | 0, _ => rfl
  | fuel + 1, state => by
      cases h_status : state.status <;>
        simp [InterpreterTrace.loopTrace, h_status]
      cases h_decode : InterpreterLoop.decodeCurrentOpcode? state with
      | none =>
          simp
      | some opcode =>
          rw [InterpreterSimulation.stepWithHandler_matchesSpec h_match state]
          simp [loopTrace_matchesSpec h_match fuel
            (InterpreterLoop.stepWithHandler spec state)]

/-- Handler agreement preserves both the final fuel-loop state and its decoded
    trace. -/
theorem loopFuelAndTrace_matchesSpec
    {impl spec : InterpreterLoop.Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state,
      InterpreterTrace.loopTrace impl fuel state) =
    (InterpreterLoop.loopFuel spec fuel state,
      InterpreterTrace.loopTrace spec fuel state) := by
  simp [
    InterpreterSimulation.loopFuel_matchesSpec h_match fuel state,
    loopTrace_matchesSpec h_match fuel state]

end InterpreterTraceSimulation

end EvmAsm.Evm64
