/-
  EvmAsm.Evm64.InterpreterExecutableFetchBridge

  Connect executable-spec opcode bytes to the pure interpreter fetch/decode
  surface (GH #109).
-/

import EvmAsm.Evm64.ExecutableSpecOpcodeBridge
import EvmAsm.Evm64.InterpreterLoop

namespace EvmAsm.Evm64

namespace InterpreterExecutableFetchBridge

/--
If the byte fetched from `state.code[state.pc]` decodes to an opcode, the
interpreter's current-opcode decoder returns that opcode.

Distinctive token: InterpreterExecutableFetchBridge.decodeCurrentOpcode?_of_execSpecByte #109.
-/
theorem decodeCurrentOpcode?_of_execSpecByte
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.decodeCurrentOpcode? state = some opcode := by
  simp [InterpreterLoop.decodeCurrentOpcode?, InterpreterLoop.fetchOpcodeByte?,
    h_pc, h_code, h_decode]

theorem stepWithHandler_of_execSpecByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.stepWithHandler handler state = handler opcode state := by
  exact InterpreterLoop.stepWithHandler_of_decode handler
    (decodeCurrentOpcode?_of_execSpecByte h_pc h_code h_decode)

theorem decodeCurrentOpcode?_of_roundtrip
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.decodeCurrentOpcode? state = some opcode := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code h_roundtrip.2

theorem stepWithHandler_of_roundtrip
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.stepWithHandler handler state = handler opcode state := by
  exact stepWithHandler_of_execSpecByte handler h_pc h_code h_roundtrip.2

theorem decodeCurrentOpcode?_of_execSpec_CALL
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.CALL : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.CALL := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.CALL, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_CREATE
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.CREATE : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.CREATE := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.CREATE, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_RETURN
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.RETURN : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.RETURN := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.RETURN, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_REVERT
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.REVERT : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.REVERT := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.REVERT, EvmOpcode.decodeByte?])

theorem decodeCurrentOpcode?_of_execSpec_INVALID
    {state : EvmState}
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] = (ExecutableSpecOpcodeBridge.Ops.INVALID : BitVec 8)) :
    InterpreterLoop.decodeCurrentOpcode? state = some EvmOpcode.INVALID := by
  exact decodeCurrentOpcode?_of_execSpecByte h_pc h_code (by
    simp [ExecutableSpecOpcodeBridge.Ops.INVALID, EvmOpcode.decodeByte?])

end InterpreterExecutableFetchBridge

end EvmAsm.Evm64
