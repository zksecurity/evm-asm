/-
  EvmAsm.Evm64.InterpreterLoopCompose

  Whole-loop composition hooks for the pure interpreter loop (GH #109).
-/

import EvmAsm.Evm64.InterpreterLoop

namespace EvmAsm.Evm64

namespace InterpreterLoopCompose

abbrev Handler := InterpreterLoop.Handler

/-- Non-running states are fixed points for every fuel budget. -/
theorem loopFuel_of_not_running
    (handler : Handler) (fuel : Nat) (state : EvmState)
    (h_status : state.status ≠ .running) :
    InterpreterLoop.loopFuel handler fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ _ =>
      cases h : state.status <;> simp [InterpreterLoop.loopFuel, h] at h_status ⊢

/-- Distinctive token: InterpreterLoopCompose.loopFuel_add #109. -/
theorem loopFuel_add
    (handler : Handler) (fuelA fuelB : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (fuelA + fuelB) state =
      InterpreterLoop.loopFuel handler fuelB
        (InterpreterLoop.loopFuel handler fuelA state) := by
  induction fuelA generalizing state with
  | zero => simp
  | succ fuelA ih =>
      rw [Nat.succ_add]
      cases h_status : state.status
      · simp [InterpreterLoop.loopFuel, h_status]
        exact ih (InterpreterLoop.stepWithHandler handler state)
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]
      · simp [InterpreterLoop.loopFuel, h_status, loopFuel_of_not_running]

theorem loopFuel_one_add
    (handler : Handler) (fuel : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (1 + fuel) state =
      InterpreterLoop.loopFuel handler fuel
        (InterpreterLoop.loopFuel handler 1 state) := by
  exact loopFuel_add handler 1 fuel state

theorem loopFuel_add_one
    (handler : Handler) (fuel : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel handler (fuel + 1) state =
      InterpreterLoop.loopFuel handler 1
        (InterpreterLoop.loopFuel handler fuel state) := by
  exact loopFuel_add handler fuel 1 state

end InterpreterLoopCompose

end EvmAsm.Evm64
