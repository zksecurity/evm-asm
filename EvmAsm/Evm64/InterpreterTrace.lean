/-
  EvmAsm.Evm64.InterpreterTrace

  Decoded-opcode trace bridge for the pure interpreter loop (GH #108).
-/

import EvmAsm.Evm64.InterpreterLoop

namespace EvmAsm.Evm64

namespace InterpreterTrace

abbrev Handler := InterpreterLoop.Handler

/--
Trace the supported opcodes decoded by `InterpreterLoop.loopFuel`. EOF or an
unsupported byte contributes no opcode and transitions through the loop's
`invalid` branch.

Distinctive token: InterpreterTrace.loopTrace #108.
-/
def loopTrace (handler : Handler) : Nat → EvmState → List EvmOpcode
  | 0, _ => []
  | fuel + 1, state =>
      match state.status with
      | .running =>
          match InterpreterLoop.decodeCurrentOpcode? state with
          | some opcode =>
              opcode :: loopTrace handler fuel (InterpreterLoop.stepWithHandler handler state)
          | none => []
      | _ => []

@[simp] theorem loopTrace_zero (handler : Handler) (state : EvmState) :
    loopTrace handler 0 state = [] := rfl

theorem loopTrace_succ_decode
    (handler : Handler) (fuel : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    loopTrace handler (fuel + 1) state =
      opcode :: loopTrace handler fuel (InterpreterLoop.stepWithHandler handler state) := by
  simp [loopTrace, h_status, h_decode]

theorem loopTrace_succ_unsupported
    (handler : Handler) (fuel : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    loopTrace handler (fuel + 1) state = [] := by
  simp [loopTrace, h_status, h_decode]

theorem loopTrace_succ_stopped
    (handler : Handler) (fuel : Nat) {state : EvmState}
    (h_status : state.status = .stopped) :
    loopTrace handler (fuel + 1) state = [] := by
  simp [loopTrace, h_status]

theorem loopTrace_succ_returned
    (handler : Handler) (fuel : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .returned data) :
    loopTrace handler (fuel + 1) state = [] := by
  simp [loopTrace, h_status]

theorem loopTrace_succ_reverted
    (handler : Handler) (fuel : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .reverted data) :
    loopTrace handler (fuel + 1) state = [] := by
  simp [loopTrace, h_status]

theorem loopTrace_succ_error
    (handler : Handler) (fuel : Nat) {state : EvmState}
    (h_status : state.status = .error) :
    loopTrace handler (fuel + 1) state = [] := by
  simp [loopTrace, h_status]

theorem loopTrace_length_le_fuel (handler : Handler) :
    ∀ (fuel : Nat) (state : EvmState), (loopTrace handler fuel state).length ≤ fuel
  | 0, _ => Nat.zero_le 0
  | fuel + 1, state => by
      cases h_status : state.status <;>
        simp [loopTrace, h_status]
      cases h_decode : InterpreterLoop.decodeCurrentOpcode? state with
      | none =>
          simp
      | some opcode =>
          simp [
            Nat.succ_le_succ (loopTrace_length_le_fuel handler fuel
              (InterpreterLoop.stepWithHandler handler state))]

end InterpreterTrace

end EvmAsm.Evm64
