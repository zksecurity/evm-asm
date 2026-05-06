/-
  EvmAsm.Evm64.InterpreterExecutableStepBridge

  Lift executable-spec byte fetch/decode facts through one running interpreter
  loop step (GH #109).
-/

import EvmAsm.Evm64.InterpreterExecutableFetchBridge

namespace EvmAsm.Evm64

namespace InterpreterExecutableStepBridge

/--
An executable-spec opcode byte at the current PC drives one running loop step
to the same handler result as direct opcode dispatch.

Distinctive token: InterpreterExecutableStepBridge.loopFuel_one_of_execSpecByte #109.
-/
theorem loopFuel_one_of_execSpecByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecByte
    handler h_pc h_code h_decode

theorem loopFuel_one_of_roundtrip
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  exact loopFuel_one_of_execSpecByte handler h_status h_pc h_code h_roundtrip.2

/--
One-step running-loop bridge for executable-spec `PUSH1` through `PUSH32`
bytes.

Distinctive token:
InterpreterExecutableStepBridge.loopFuel_one_of_execSpecPushByte #109 #101.
-/
theorem loopFuel_one_of_execSpecPushByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {n : Nat}
    (h_status : state.status = .running)
    (h_low : 1 ≤ n) (h_high : n ≤ 32)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecPushByte n : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler (EvmOpcode.PUSH n) state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecPushByte
    handler h_low h_high h_pc h_code

/--
One-step running-loop bridge for executable-spec `LOG0` through `LOG4` bytes.

Distinctive token:
InterpreterExecutableStepBridge.loopFuel_one_of_execSpecLogByte #109 #112.
-/
theorem loopFuel_one_of_execSpecLogByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} (kind : LogArgs.Kind)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecLogByte kind : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler (EvmOpcode.LOG kind) state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecLogByte
    handler kind h_pc h_code

theorem loopFuel_one_of_unsupported
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterLoop.stepWithHandler_of_unsupported handler (by
    simp [InterpreterLoop.decodeCurrentOpcode?,
      InterpreterLoop.fetchOpcodeByte?, h_pc, h_code, h_decode])

theorem loopFuel_one_of_eof
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterLoop.stepWithHandler_eof_invalid handler h_pc

end InterpreterExecutableStepBridge

end EvmAsm.Evm64
