/-
  EvmAsm.Evm64.InterpreterLoopStatus

  Status/control lemmas for the pure interpreter loop (GH #108).
-/

import EvmAsm.Evm64.InterpreterLoop

namespace EvmAsm.Evm64

namespace InterpreterLoopStatus

abbrev Handler := InterpreterLoop.Handler

/-- Predicate for states that the fuel-bounded interpreter loop leaves fixed.
    Distinctive token: InterpreterLoopStatus.loopFuel_nonRunning #108. -/
def nonRunning (state : EvmState) : Prop :=
  state.status ≠ .running

theorem nonRunning_of_stopped {state : EvmState}
    (h_status : state.status = .stopped) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_returned {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .returned data) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_reverted {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .reverted data) : nonRunning state := by
  simp [nonRunning, h_status]

theorem nonRunning_of_error {state : EvmState}
    (h_status : state.status = .error) : nonRunning state := by
  simp [nonRunning, h_status]

theorem loopFuel_nonRunning
    (handler : Handler) (fuel : Nat) (state : EvmState)
    (h_nonRunning : nonRunning state) :
    InterpreterLoop.loopFuel handler fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases h_status : state.status <;>
        simp [InterpreterLoop.loopFuel, h_status, nonRunning] at h_nonRunning ⊢

theorem loopFuel_stopped
    (handler : Handler) (fuel : Nat) (state : EvmState)
    (h_status : state.status = .stopped) :
    InterpreterLoop.loopFuel handler fuel state = state :=
  loopFuel_nonRunning handler fuel state (nonRunning_of_stopped h_status)

theorem loopFuel_returned
    (handler : Handler) (fuel : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .returned data) :
    InterpreterLoop.loopFuel handler fuel state = state :=
  loopFuel_nonRunning handler fuel state (nonRunning_of_returned h_status)

theorem loopFuel_reverted
    (handler : Handler) (fuel : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .reverted data) :
    InterpreterLoop.loopFuel handler fuel state = state :=
  loopFuel_nonRunning handler fuel state (nonRunning_of_reverted h_status)

theorem loopFuel_error
    (handler : Handler) (fuel : Nat) (state : EvmState)
    (h_status : state.status = .error) :
    InterpreterLoop.loopFuel handler fuel state = state :=
  loopFuel_nonRunning handler fuel state (nonRunning_of_error h_status)

theorem loopFuel_one_eof_invalid
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_eof_invalid handler h_pc]

theorem loopFuel_one_unsupported_invalid
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_of_unsupported handler h_decode]

theorem loopFuel_one_decode
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  simp [InterpreterLoop.stepWithHandler_of_decode handler h_decode]

end InterpreterLoopStatus

end EvmAsm.Evm64
