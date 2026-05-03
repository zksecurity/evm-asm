/-
  EvmAsm.Evm64.Env.Gas

  Static gas helpers for simple environment opcodes (issues #117 / #103).
-/

import EvmAsm.Evm64.Env.Field
import EvmAsm.Evm64.Gas

namespace EvmAsm.Evm64
namespace Env

namespace SimpleEnvField

/-- EVM opcode table entry for a simple environment field. -/
def opcode : SimpleEnvField → EvmOpcode
  | address => .ADDRESS
  | caller => .CALLER
  | callValue => .CALLVALUE
  | origin => .ORIGIN
  | gasPrice => .GASPRICE
  | coinbase => .COINBASE
  | timestamp => .TIMESTAMP
  | number => .NUMBER
  | prevrandao => .PREVRANDAO
  | gasLimit => .GASLIMIT
  | chainId => .CHAINID
  | baseFee => .BASEFEE
  | selfBalance => .SELFBALANCE

/-- Shanghai static/base gas for the simple environment opcodes. -/
def simpleEnvStaticGasCost : SimpleEnvField → Nat
  | selfBalance => 5
  | _ => 2

theorem opcode_byte (field : SimpleEnvField) :
    EvmOpcode.byte? field.opcode = some field.opcodeByte := by
  cases field <;> rfl

theorem simpleEnvStaticGasCost_eq_staticGasCost (field : SimpleEnvField) :
    simpleEnvStaticGasCost field = EvmOpcode.staticGasCost field.opcode := by
  cases field <;> rfl

theorem simpleEnvStaticGasCost_address :
    simpleEnvStaticGasCost address = 2 := rfl

theorem simpleEnvStaticGasCost_selfBalance :
    simpleEnvStaticGasCost selfBalance = 5 := rfl

theorem simpleEnvStaticGasCost_cases (field : SimpleEnvField) :
    match field with
    | address => simpleEnvStaticGasCost address = 2
    | caller => simpleEnvStaticGasCost caller = 2
    | callValue => simpleEnvStaticGasCost callValue = 2
    | origin => simpleEnvStaticGasCost origin = 2
    | gasPrice => simpleEnvStaticGasCost gasPrice = 2
    | coinbase => simpleEnvStaticGasCost coinbase = 2
    | timestamp => simpleEnvStaticGasCost timestamp = 2
    | number => simpleEnvStaticGasCost number = 2
    | prevrandao => simpleEnvStaticGasCost prevrandao = 2
    | gasLimit => simpleEnvStaticGasCost gasLimit = 2
    | chainId => simpleEnvStaticGasCost chainId = 2
    | baseFee => simpleEnvStaticGasCost baseFee = 2
    | selfBalance => simpleEnvStaticGasCost selfBalance = 5 := by
  cases field <;> rfl

end SimpleEnvField

end Env
end EvmAsm.Evm64
