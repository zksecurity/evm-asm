/-
  EvmAsm.Evm64.InterpreterLoop

  Pure fetch/decode/dispatch loop scaffold for the EVM interpreter (GH #108).
-/

import EvmAsm.Evm64.Dispatch
import EvmAsm.Evm64.Termination

namespace EvmAsm.Evm64

namespace InterpreterLoop

/-- Fetch the opcode byte at the current EVM PC. -/
def fetchOpcodeByte? (state : EvmState) : Option (BitVec 8) :=
  if h_pc : state.pc < state.code.length then
    some state.code[state.pc]
  else
    none

/-- Decode the current opcode byte through the modeled dispatch table. -/
def decodeCurrentOpcode? (state : EvmState) : Option EvmOpcode :=
  match fetchOpcodeByte? state with
  | some byte => EvmOpcode.decodeByte? byte.toNat
  | none => none

/-- Pluggable interpreter handler surface. Concrete opcode wrappers can later
    instantiate this by dispatching to verified handler specs. -/
abbrev Handler := EvmOpcode → EvmState → EvmState

/-- One fetch/decode/dispatch step. EOF or an unsupported opcode transitions
    to `invalid`; modeled opcodes are delegated to the supplied handler.
    Distinctive token: InterpreterLoop.stepWithHandler. -/
def stepWithHandler (handler : Handler) (state : EvmState) : EvmState :=
  match decodeCurrentOpcode? state with
  | some opcode => handler opcode state
  | none => state.invalid

/-- Fuel-bounded interpreter loop. Non-running states are returned unchanged;
    running states take at most `nSteps` fetch/decode/dispatch steps.
    Distinctive token: InterpreterLoop.loopFuel. -/
def loopFuel (handler : Handler) : Nat → EvmState → EvmState
  | 0, state => state
  | nSteps + 1, state =>
      match state.status with
      | .running => loopFuel handler nSteps (stepWithHandler handler state)
      | _ => state

theorem fetchOpcodeByte?_of_lt
    {state : EvmState} (h_pc : state.pc < state.code.length) :
    fetchOpcodeByte? state = some state.code[state.pc] := by
  simp [fetchOpcodeByte?, h_pc]

theorem fetchOpcodeByte?_of_ge
    {state : EvmState} (h_pc : state.code.length ≤ state.pc) :
    fetchOpcodeByte? state = none := by
  simp [fetchOpcodeByte?, show ¬ state.pc < state.code.length from by omega]

theorem decodeCurrentOpcode?_of_fetch
    {state : EvmState} {byte : BitVec 8}
    (h_fetch : fetchOpcodeByte? state = some byte) :
    decodeCurrentOpcode? state = EvmOpcode.decodeByte? byte.toNat := by
  simp [decodeCurrentOpcode?, h_fetch]

theorem decodeCurrentOpcode?_of_eof
    {state : EvmState} (h_fetch : fetchOpcodeByte? state = none) :
    decodeCurrentOpcode? state = none := by
  simp [decodeCurrentOpcode?, h_fetch]

theorem stepWithHandler_of_decode
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_decode : decodeCurrentOpcode? state = some opcode) :
    stepWithHandler handler state = handler opcode state := by
  simp [stepWithHandler, h_decode]

theorem stepWithHandler_of_unsupported
    (handler : Handler) {state : EvmState}
    (h_decode : decodeCurrentOpcode? state = none) :
    stepWithHandler handler state = state.invalid := by
  simp [stepWithHandler, h_decode]

@[simp] theorem loopFuel_zero (handler : Handler) (state : EvmState) :
    loopFuel handler 0 state = state := rfl

theorem loopFuel_succ_running
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .running) :
    loopFuel handler (nSteps + 1) state =
      loopFuel handler nSteps (stepWithHandler handler state) := by
  simp [loopFuel, h_status]

theorem loopFuel_succ_stopped
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .stopped) :
    loopFuel handler (nSteps + 1) state = state := by
  simp [loopFuel, h_status]

theorem loopFuel_succ_returned
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .returned data) :
    loopFuel handler (nSteps + 1) state = state := by
  simp [loopFuel, h_status]

theorem loopFuel_succ_reverted
    (handler : Handler) (nSteps : Nat) (state : EvmState) (data : List (BitVec 8))
    (h_status : state.status = .reverted data) :
    loopFuel handler (nSteps + 1) state = state := by
  simp [loopFuel, h_status]

theorem loopFuel_succ_error
    (handler : Handler) (nSteps : Nat) (state : EvmState)
    (h_status : state.status = .error) :
    loopFuel handler (nSteps + 1) state = state := by
  simp [loopFuel, h_status]

theorem stepWithHandler_eof_invalid
    (handler : Handler) {state : EvmState}
    (h_pc : state.code.length ≤ state.pc) :
    stepWithHandler handler state = state.invalid := by
  exact stepWithHandler_of_unsupported handler
    (decodeCurrentOpcode?_of_eof (fetchOpcodeByte?_of_ge h_pc))

end InterpreterLoop

end EvmAsm.Evm64
