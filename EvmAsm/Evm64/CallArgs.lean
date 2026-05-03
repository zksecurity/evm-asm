/-
  EvmAsm.Evm64.CallArgs

  Pure stack-argument records for CALL-family opcodes (GH #114).
-/

import EvmAsm.Evm64.Environment

namespace EvmAsm.Evm64

namespace CallArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- CALL stack arguments: gas, target, value, input range, and output range. -/
structure Call where
  gas : EvmWord
  to : EvmWord
  value : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr

/-- STATICCALL stack arguments: no value transfer argument. -/
structure StaticCall where
  gas : EvmWord
  to : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr

/-- DELEGATECALL stack arguments: caller/value context is inherited. -/
structure DelegateCall where
  gas : EvmWord
  to : EvmWord
  input : MemoryRange
  output : MemoryRange
  deriving Repr

/-- Opcode family classifier for stack argument decoding. -/
inductive Kind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr

def argumentCount : Kind → Nat
  | .call => 7
  | .staticcall => 6
  | .delegatecall => 6

def hasValueArgument : Kind → Bool
  | .call => true
  | .staticcall => false
  | .delegatecall => false

def isStatic : Kind → Bool
  | .call => false
  | .staticcall => true
  | .delegatecall => false

def preservesCallerContext : Kind → Bool
  | .call => false
  | .staticcall => false
  | .delegatecall => true

theorem callArgumentCount :
    argumentCount .call = 7 := rfl

theorem staticcallArgumentCount :
    argumentCount .staticcall = 6 := rfl

theorem delegatecallArgumentCount :
    argumentCount .delegatecall = 6 := rfl

theorem callHasValue :
    hasValueArgument .call = true := rfl

theorem staticcallHasNoValue :
    hasValueArgument .staticcall = false := rfl

theorem delegatecallHasNoValue :
    hasValueArgument .delegatecall = false := rfl

theorem staticcallIsStatic :
    isStatic .staticcall = true := rfl

theorem delegatecallPreservesCallerContext :
    preservesCallerContext .delegatecall = true := rfl

end CallArgs

end EvmAsm.Evm64
