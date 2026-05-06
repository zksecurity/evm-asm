/-
  EvmAsm.Evm64.InterpreterLoopSimulation

  Whole-loop simulation relation for the pure interpreter loop (GH #109).
-/

import EvmAsm.Evm64.InterpreterSimulation

namespace EvmAsm.Evm64

namespace InterpreterLoopSimulation

abbrev Handler := InterpreterLoop.Handler

/-- Whole-loop result agreement for all fuel budgets and starting states. -/
def LoopResultsMatch (impl spec : Handler) : Prop :=
  ∀ (fuel : Nat) (state : EvmState),
    InterpreterLoop.loopFuel impl fuel state =
      InterpreterLoop.loopFuel spec fuel state

theorem LoopResultsMatch.refl (handler : Handler) :
    LoopResultsMatch handler handler := by
  intro fuel state
  rfl

theorem LoopResultsMatch.symm
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec) :
    LoopResultsMatch spec impl := by
  intro fuel state
  exact (h_match fuel state).symm

theorem LoopResultsMatch.trans
    {impl mid spec : Handler}
    (h_left : LoopResultsMatch impl mid)
    (h_right : LoopResultsMatch mid spec) :
    LoopResultsMatch impl spec := by
  intro fuel state
  exact (h_left fuel state).trans (h_right fuel state)

/-- Distinctive token: InterpreterLoopSimulation.loopResultsMatch_of_handlerMatchesSpec #109. -/
theorem loopResultsMatch_of_handlerMatchesSpec
    {impl spec : Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec) :
    LoopResultsMatch impl spec := by
  intro fuel state
  exact InterpreterSimulation.loopFuel_matchesSpec h_match fuel state

theorem loopFuel_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel impl fuel state =
      InterpreterLoop.loopFuel spec fuel state :=
  h_match fuel state

theorem loopFuel_status_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).status =
      (InterpreterLoop.loopFuel spec fuel state).status := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]

theorem loopResultsMatch_of_eq
    {impl spec : Handler}
    (h_eq : ∀ (opcode : EvmOpcode) (state : EvmState), impl opcode state = spec opcode state) :
    LoopResultsMatch impl spec := by
  apply loopResultsMatch_of_handlerMatchesSpec
  intro opcode state _h_decode
  exact h_eq opcode state

theorem loopResultsMatch_step_one
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (state : EvmState) :
    InterpreterLoop.loopFuel impl 1 state =
      InterpreterLoop.loopFuel spec 1 state :=
  h_match 1 state

theorem loopResultsMatch_step_one_status
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (state : EvmState) :
    (InterpreterLoop.loopFuel impl 1 state).status =
      (InterpreterLoop.loopFuel spec 1 state).status := by
  rw [loopResultsMatch_step_one h_match state]

theorem stepWithHandler_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    InterpreterLoop.stepWithHandler impl state =
      InterpreterLoop.stepWithHandler spec state := by
  have h_loop := loopResultsMatch_step_one h_match state
  rw [InterpreterLoop.loopFuel_succ_running impl 0 state h_status] at h_loop
  rw [InterpreterLoop.loopFuel_succ_running spec 0 state h_status] at h_loop
  exact h_loop

theorem stepWithHandler_status_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).status =
      (InterpreterLoop.stepWithHandler spec state).status := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]

end InterpreterLoopSimulation

end EvmAsm.Evm64
