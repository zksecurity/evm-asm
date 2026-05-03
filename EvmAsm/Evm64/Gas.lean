/-
  EvmAsm.Evm64.Gas

  Static gas-cost table for the opcode families currently modeled under
  `EvmAsm.Evm64` (GH #117 slice 1).

  The table records Shanghai static/base costs. Dynamic add-ons (EXP byte
  cost, memory expansion, storage cold/warm access, logging data/topic
  costs, etc.) intentionally live outside this first slice.
-/

import EvmAsm.Evm64.LogArgs

namespace EvmAsm.Evm64

/-- EVM opcode identifiers for opcode families that already have an
    implementation or specification subtree in `EvmAsm.Evm64`. Parameterized
    families keep their EVM width/index as data so handler code can share one
    gas theorem across all concrete opcodes in the family. -/
inductive EvmOpcode where
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | MOD
  | EXP
  | SIGNEXTEND
  | ADDRESS
  | ORIGIN
  | CALLER
  | CALLVALUE
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | SHL
  | SHR
  | SAR
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | MSIZE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | GASPRICE
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | PREVRANDAO
  | GASLIMIT
  | CHAINID
  | SELFBALANCE
  | BASEFEE
  | LOG (kind : LogArgs.Kind)
  | RETURN
  | REVERT
  | INVALID
  | PUSH0
  | PUSH (n : Nat)
  | DUP (n : Nat)
  | SWAP (n : Nat)
  deriving DecidableEq, Repr

namespace EvmOpcode

/-- Valid immediate width for PUSH1 through PUSH32. -/
def validPushWidth (n : Nat) : Bool :=
  1 ≤ n && n ≤ 32

/-- Valid stack slot index for DUP1 through DUP16. -/
def validDupIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Valid stack slot index for SWAP1 through SWAP16. -/
def validSwapIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Concrete EVM opcode byte when this identifier denotes one bytecode. Invalid
    parameterized identifiers return `none`, keeping the gas table total while
    making bytecode emission validate widths explicitly. -/
def byte? : EvmOpcode → Option Nat
  | STOP => some 0x00
  | ADD => some 0x01
  | MUL => some 0x02
  | SUB => some 0x03
  | DIV => some 0x04
  | MOD => some 0x06
  | EXP => some 0x0a
  | SIGNEXTEND => some 0x0b
  | ADDRESS => some 0x30
  | ORIGIN => some 0x32
  | CALLER => some 0x33
  | CALLVALUE => some 0x34
  | LT => some 0x10
  | GT => some 0x11
  | SLT => some 0x12
  | SGT => some 0x13
  | EQ => some 0x14
  | ISZERO => some 0x15
  | AND => some 0x16
  | OR => some 0x17
  | XOR => some 0x18
  | NOT => some 0x19
  | BYTE => some 0x1a
  | SHL => some 0x1b
  | SHR => some 0x1c
  | SAR => some 0x1d
  | POP => some 0x50
  | MLOAD => some 0x51
  | MSTORE => some 0x52
  | MSTORE8 => some 0x53
  | MSIZE => some 0x59
  | CALLDATALOAD => some 0x35
  | CALLDATASIZE => some 0x36
  | CALLDATACOPY => some 0x37
  | GASPRICE => some 0x3a
  | COINBASE => some 0x41
  | TIMESTAMP => some 0x42
  | NUMBER => some 0x43
  | PREVRANDAO => some 0x44
  | GASLIMIT => some 0x45
  | CHAINID => some 0x46
  | SELFBALANCE => some 0x47
  | BASEFEE => some 0x48
  | LOG kind => some (0xa0 + LogArgs.topicCount kind)
  | RETURN => some 0xf3
  | REVERT => some 0xfd
  | INVALID => some 0xfe
  | PUSH0 => some 0x5f
  | PUSH n => if validPushWidth n then some (0x5f + n) else none
  | DUP n => if validDupIndex n then some (0x7f + n) else none
  | SWAP n => if validSwapIndex n then some (0x8f + n) else none

/-- Shanghai static/base gas cost. Costs that also have dynamic components
    return only the fixed part charged before the dynamic add-on. -/
def staticGasCost : EvmOpcode → Nat
  | STOP => 0
  | ADD => 3
  | MUL => 5
  | SUB => 3
  | DIV => 5
  | MOD => 5
  | EXP => 10
  | SIGNEXTEND => 5
  | ADDRESS => 2
  | ORIGIN => 2
  | CALLER => 2
  | CALLVALUE => 2
  | LT => 3
  | GT => 3
  | SLT => 3
  | SGT => 3
  | EQ => 3
  | ISZERO => 3
  | AND => 3
  | OR => 3
  | XOR => 3
  | NOT => 3
  | BYTE => 3
  | SHL => 3
  | SHR => 3
  | SAR => 3
  | POP => 2
  | MLOAD => 3
  | MSTORE => 3
  | MSTORE8 => 3
  | MSIZE => 2
  | CALLDATALOAD => 3
  | CALLDATASIZE => 2
  | CALLDATACOPY => 3
  | GASPRICE => 2
  | COINBASE => 2
  | TIMESTAMP => 2
  | NUMBER => 2
  | PREVRANDAO => 2
  | GASLIMIT => 2
  | CHAINID => 2
  | SELFBALANCE => 5
  | BASEFEE => 2
  | LOG _ => 375
  | RETURN => 0
  | REVERT => 0
  | INVALID => 0
  | PUSH0 => 2
  | PUSH _ => 3
  | DUP _ => 3
  | SWAP _ => 3

theorem staticGasCost_PUSH (n : Nat) :
    staticGasCost (PUSH n) = 3 := rfl

theorem staticGasCost_DUP (n : Nat) :
    staticGasCost (DUP n) = 3 := rfl

theorem staticGasCost_SWAP (n : Nat) :
    staticGasCost (SWAP n) = 3 := rfl

theorem byte?_PUSH_of_valid {n : Nat} (h : validPushWidth n = true) :
    byte? (PUSH n) = some (0x5f + n) := by
  simp [byte?, h]

theorem byte?_DUP_of_valid {n : Nat} (h : validDupIndex n = true) :
    byte? (DUP n) = some (0x7f + n) := by
  simp [byte?, h]

theorem byte?_SWAP_of_valid {n : Nat} (h : validSwapIndex n = true) :
    byte? (SWAP n) = some (0x8f + n) := by
  simp [byte?, h]

theorem byte?_PUSH0 : byte? PUSH0 = some 0x5f := rfl

theorem byte?_STOP : byte? STOP = some 0x00 := rfl

theorem byte?_RETURN : byte? RETURN = some 0xf3 := rfl

theorem byte?_REVERT : byte? REVERT = some 0xfd := rfl

theorem byte?_INVALID : byte? INVALID = some 0xfe := rfl

theorem byte?_ADDRESS : byte? ADDRESS = some 0x30 := rfl

theorem byte?_BASEFEE : byte? BASEFEE = some 0x48 := rfl

theorem byte?_LOG (kind : LogArgs.Kind) :
    byte? (LOG kind) = some (0xa0 + LogArgs.topicCount kind) := rfl

theorem byte?_LOG0 : byte? (LOG .log0) = some 0xa0 := rfl

theorem byte?_LOG4 : byte? (LOG .log4) = some 0xa4 := rfl

theorem staticGasCost_stop : staticGasCost STOP = 0 := rfl

theorem staticGasCost_push0 : staticGasCost PUSH0 = 2 := rfl

theorem staticGasCost_msize : staticGasCost MSIZE = 2 := rfl

theorem staticGasCost_calldataLoad : staticGasCost CALLDATALOAD = 3 := rfl

theorem staticGasCost_calldataSize : staticGasCost CALLDATASIZE = 2 := rfl

theorem staticGasCost_calldataCopyBase : staticGasCost CALLDATACOPY = 3 := rfl

theorem staticGasCost_address : staticGasCost ADDRESS = 2 := rfl

theorem staticGasCost_basefee : staticGasCost BASEFEE = 2 := rfl

theorem staticGasCost_selfbalance : staticGasCost SELFBALANCE = 5 := rfl

theorem staticGasCost_LOG (kind : LogArgs.Kind) :
    staticGasCost (LOG kind) = 375 := rfl

theorem staticGasCost_log0Base : staticGasCost (LOG .log0) = 375 := rfl

theorem staticGasCost_log4Base : staticGasCost (LOG .log4) = 375 := rfl

theorem staticGasCost_returnBase : staticGasCost RETURN = 0 := rfl

theorem staticGasCost_revertBase : staticGasCost REVERT = 0 := rfl

theorem staticGasCost_invalidBase : staticGasCost INVALID = 0 := rfl

theorem staticGasCost_expBase : staticGasCost EXP = 10 := rfl

end EvmOpcode

end EvmAsm.Evm64
