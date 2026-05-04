/-
  EvmAsm.Evm64.Dispatch

  First dispatch slice for GH #106. This module defines the pure opcode-byte
  decoder used by later RV64 jump-table or branch-tree dispatch programs. It is
  stacked on the static gas table slice because both layers share the
  `EvmOpcode` identifier type.
-/

import EvmAsm.Evm64.Gas

namespace EvmAsm.Evm64

namespace EvmOpcode

/-- Decode one EVM opcode byte into the opcode families currently modeled in
    `EvmAsm.Evm64`. Unsupported bytes return `none`; later feature slices can
    extend this table as new opcode handlers land. -/
def decodeByte? : Nat → Option EvmOpcode
  | 0x00 => some STOP
  | 0x01 => some ADD
  | 0x02 => some MUL
  | 0x03 => some SUB
  | 0x04 => some DIV
  | 0x06 => some MOD
  | 0x0a => some EXP
  | 0x0b => some SIGNEXTEND
  | 0x10 => some LT
  | 0x11 => some GT
  | 0x12 => some SLT
  | 0x13 => some SGT
  | 0x14 => some EQ
  | 0x15 => some ISZERO
  | 0x16 => some AND
  | 0x17 => some OR
  | 0x18 => some XOR
  | 0x19 => some NOT
  | 0x1a => some BYTE
  | 0x1b => some SHL
  | 0x1c => some SHR
  | 0x1d => some SAR
  | 0x30 => some ADDRESS
  | 0x32 => some ORIGIN
  | 0x33 => some CALLER
  | 0x34 => some CALLVALUE
  | 0x35 => some CALLDATALOAD
  | 0x36 => some CALLDATASIZE
  | 0x37 => some CALLDATACOPY
  | 0x3a => some GASPRICE
  | 0x41 => some COINBASE
  | 0x42 => some TIMESTAMP
  | 0x43 => some NUMBER
  | 0x44 => some PREVRANDAO
  | 0x45 => some GASLIMIT
  | 0x46 => some CHAINID
  | 0x47 => some SELFBALANCE
  | 0x48 => some BASEFEE
  | 0x50 => some POP
  | 0x51 => some MLOAD
  | 0x52 => some MSTORE
  | 0x53 => some MSTORE8
  | 0x59 => some MSIZE
  | 0x5f => some PUSH0
  | 0x60 => some (PUSH 1)
  | 0x61 => some (PUSH 2)
  | 0x62 => some (PUSH 3)
  | 0x63 => some (PUSH 4)
  | 0x64 => some (PUSH 5)
  | 0x65 => some (PUSH 6)
  | 0x66 => some (PUSH 7)
  | 0x67 => some (PUSH 8)
  | 0x68 => some (PUSH 9)
  | 0x69 => some (PUSH 10)
  | 0x6a => some (PUSH 11)
  | 0x6b => some (PUSH 12)
  | 0x6c => some (PUSH 13)
  | 0x6d => some (PUSH 14)
  | 0x6e => some (PUSH 15)
  | 0x6f => some (PUSH 16)
  | 0x70 => some (PUSH 17)
  | 0x71 => some (PUSH 18)
  | 0x72 => some (PUSH 19)
  | 0x73 => some (PUSH 20)
  | 0x74 => some (PUSH 21)
  | 0x75 => some (PUSH 22)
  | 0x76 => some (PUSH 23)
  | 0x77 => some (PUSH 24)
  | 0x78 => some (PUSH 25)
  | 0x79 => some (PUSH 26)
  | 0x7a => some (PUSH 27)
  | 0x7b => some (PUSH 28)
  | 0x7c => some (PUSH 29)
  | 0x7d => some (PUSH 30)
  | 0x7e => some (PUSH 31)
  | 0x7f => some (PUSH 32)
  | 0x80 => some (DUP 1)
  | 0x81 => some (DUP 2)
  | 0x82 => some (DUP 3)
  | 0x83 => some (DUP 4)
  | 0x84 => some (DUP 5)
  | 0x85 => some (DUP 6)
  | 0x86 => some (DUP 7)
  | 0x87 => some (DUP 8)
  | 0x88 => some (DUP 9)
  | 0x89 => some (DUP 10)
  | 0x8a => some (DUP 11)
  | 0x8b => some (DUP 12)
  | 0x8c => some (DUP 13)
  | 0x8d => some (DUP 14)
  | 0x8e => some (DUP 15)
  | 0x8f => some (DUP 16)
  | 0x90 => some (SWAP 1)
  | 0x91 => some (SWAP 2)
  | 0x92 => some (SWAP 3)
  | 0x93 => some (SWAP 4)
  | 0x94 => some (SWAP 5)
  | 0x95 => some (SWAP 6)
  | 0x96 => some (SWAP 7)
  | 0x97 => some (SWAP 8)
  | 0x98 => some (SWAP 9)
  | 0x99 => some (SWAP 10)
  | 0x9a => some (SWAP 11)
  | 0x9b => some (SWAP 12)
  | 0x9c => some (SWAP 13)
  | 0x9d => some (SWAP 14)
  | 0x9e => some (SWAP 15)
  | 0x9f => some (SWAP 16)
  | 0xf3 => some RETURN
  | 0xfd => some REVERT
  | 0xfe => some INVALID
  | _ => none

/-- Predicate form for dispatch tables that only need to know whether a byte is
    implemented by the current verified opcode surface. -/
def modeledByte (b : Nat) : Prop :=
  (decodeByte? b).isSome

theorem decodeByte?_ADD : decodeByte? 0x01 = some ADD := rfl
theorem decodeByte?_STOP : decodeByte? 0x00 = some STOP := rfl
theorem decodeByte?_EXP : decodeByte? 0x0a = some EXP := rfl
theorem decodeByte?_ADDRESS : decodeByte? 0x30 = some ADDRESS := rfl
theorem decodeByte?_ORIGIN : decodeByte? 0x32 = some ORIGIN := rfl
theorem decodeByte?_CALLER : decodeByte? 0x33 = some CALLER := rfl
theorem decodeByte?_CALLVALUE : decodeByte? 0x34 = some CALLVALUE := rfl
theorem decodeByte?_CALLDATALOAD : decodeByte? 0x35 = some CALLDATALOAD := rfl
theorem decodeByte?_CALLDATASIZE : decodeByte? 0x36 = some CALLDATASIZE := rfl
theorem decodeByte?_CALLDATACOPY : decodeByte? 0x37 = some CALLDATACOPY := rfl
theorem decodeByte?_GASPRICE : decodeByte? 0x3a = some GASPRICE := rfl
theorem decodeByte?_COINBASE : decodeByte? 0x41 = some COINBASE := rfl
theorem decodeByte?_TIMESTAMP : decodeByte? 0x42 = some TIMESTAMP := rfl
theorem decodeByte?_NUMBER : decodeByte? 0x43 = some NUMBER := rfl
theorem decodeByte?_PREVRANDAO : decodeByte? 0x44 = some PREVRANDAO := rfl
theorem decodeByte?_GASLIMIT : decodeByte? 0x45 = some GASLIMIT := rfl
theorem decodeByte?_CHAINID : decodeByte? 0x46 = some CHAINID := rfl
theorem decodeByte?_SELFBALANCE : decodeByte? 0x47 = some SELFBALANCE := rfl
theorem decodeByte?_BASEFEE : decodeByte? 0x48 = some BASEFEE := rfl
theorem decodeByte?_MLOAD : decodeByte? 0x51 = some MLOAD := rfl
theorem decodeByte?_PUSH0 : decodeByte? 0x5f = some PUSH0 := rfl
theorem decodeByte?_PUSH1 : decodeByte? 0x60 = some (PUSH 1) := rfl
theorem decodeByte?_PUSH32 : decodeByte? 0x7f = some (PUSH 32) := rfl
theorem decodeByte?_DUP1 : decodeByte? 0x80 = some (DUP 1) := rfl
theorem decodeByte?_DUP16 : decodeByte? 0x8f = some (DUP 16) := rfl
theorem decodeByte?_SWAP1 : decodeByte? 0x90 = some (SWAP 1) := rfl
theorem decodeByte?_SWAP16 : decodeByte? 0x9f = some (SWAP 16) := rfl
theorem decodeByte?_RETURN : decodeByte? 0xf3 = some RETURN := rfl
theorem decodeByte?_REVERT : decodeByte? 0xfd = some REVERT := rfl
theorem decodeByte?_INVALID : decodeByte? 0xfe = some INVALID := rfl

theorem byte?_roundtrip_STOP :
    byte? STOP = some 0x00 ∧ decodeByte? 0x00 = some STOP := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_ADD :
    byte? ADD = some 0x01 ∧ decodeByte? 0x01 = some ADD := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CALLDATALOAD :
    byte? CALLDATALOAD = some 0x35 ∧ decodeByte? 0x35 = some CALLDATALOAD := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CALLDATASIZE :
    byte? CALLDATASIZE = some 0x36 ∧ decodeByte? 0x36 = some CALLDATASIZE := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CALLDATACOPY :
    byte? CALLDATACOPY = some 0x37 ∧ decodeByte? 0x37 = some CALLDATACOPY := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_PUSH32 :
    byte? (PUSH 32) = some 0x7f ∧ decodeByte? 0x7f = some (PUSH 32) := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_DUP16 :
    byte? (DUP 16) = some 0x8f ∧ decodeByte? 0x8f = some (DUP 16) := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_SWAP16 :
    byte? (SWAP 16) = some 0x9f ∧ decodeByte? 0x9f = some (SWAP 16) := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_RETURN :
    byte? RETURN = some 0xf3 ∧ decodeByte? 0xf3 = some RETURN := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_REVERT :
    byte? REVERT = some 0xfd ∧ decodeByte? 0xfd = some REVERT := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_INVALID :
    byte? INVALID = some 0xfe ∧ decodeByte? 0xfe = some INVALID := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_ADDRESS :
    byte? ADDRESS = some 0x30 ∧ decodeByte? 0x30 = some ADDRESS := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_ORIGIN :
    byte? ORIGIN = some 0x32 ∧ decodeByte? 0x32 = some ORIGIN := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CALLER :
    byte? CALLER = some 0x33 ∧ decodeByte? 0x33 = some CALLER := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CALLVALUE :
    byte? CALLVALUE = some 0x34 ∧ decodeByte? 0x34 = some CALLVALUE := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_GASPRICE :
    byte? GASPRICE = some 0x3a ∧ decodeByte? 0x3a = some GASPRICE := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_COINBASE :
    byte? COINBASE = some 0x41 ∧ decodeByte? 0x41 = some COINBASE := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_TIMESTAMP :
    byte? TIMESTAMP = some 0x42 ∧ decodeByte? 0x42 = some TIMESTAMP := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_NUMBER :
    byte? NUMBER = some 0x43 ∧ decodeByte? 0x43 = some NUMBER := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_PREVRANDAO :
    byte? PREVRANDAO = some 0x44 ∧ decodeByte? 0x44 = some PREVRANDAO := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_GASLIMIT :
    byte? GASLIMIT = some 0x45 ∧ decodeByte? 0x45 = some GASLIMIT := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_CHAINID :
    byte? CHAINID = some 0x46 ∧ decodeByte? 0x46 = some CHAINID := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_SELFBALANCE :
    byte? SELFBALANCE = some 0x47 ∧ decodeByte? 0x47 = some SELFBALANCE := by
  exact ⟨rfl, rfl⟩

theorem byte?_roundtrip_BASEFEE :
    byte? BASEFEE = some 0x48 ∧ decodeByte? 0x48 = some BASEFEE := by
  exact ⟨rfl, rfl⟩

end EvmOpcode

end EvmAsm.Evm64
