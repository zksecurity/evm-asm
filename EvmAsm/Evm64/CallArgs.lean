/-
  EvmAsm.Evm64.CallArgs

  Pure stack-argument records for CALL-family opcodes (GH #114).
-/

import EvmAsm.Evm64.Basic

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

def resultCount (_kind : Kind) : Nat := 1

def memoryRangeCount (_kind : Kind) : Nat := 2

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

theorem resultCount_eq_one (kind : Kind) :
    resultCount kind = 1 := rfl

theorem memoryRangeCount_eq_two (kind : Kind) :
    memoryRangeCount kind = 2 := rfl

theorem argumentCount_eq_six_plus_value (kind : Kind) :
    argumentCount kind = 6 + if hasValueArgument kind then 1 else 0 := by
  cases kind <;> rfl

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

/-! ### Classifier ↔ Kind iffs and pairwise mutual exclusions

Cross-predicate lemmas for the three Kind classifiers
(`hasValueArgument`, `isStatic`, `preservesCallerContext`). Each Kind is
characterised by exactly one of the predicates being `true`; the iffs make
that explicit and the pairwise exclusion lemmas let downstream proofs avoid
re-`cases`-ing on `Kind`. Mirrors the cross-predicate slice on
`TerminatingArgs` (see `EvmAsm.Evm64.TerminatingArgs`). -/

theorem hasValueArgument_iff_call (kind : Kind) :
    hasValueArgument kind = true ↔ kind = .call := by
  cases kind <;> decide

theorem isStatic_iff_staticcall (kind : Kind) :
    isStatic kind = true ↔ kind = .staticcall := by
  cases kind <;> decide

theorem preservesCallerContext_iff_delegatecall (kind : Kind) :
    preservesCallerContext kind = true ↔ kind = .delegatecall := by
  cases kind <;> decide

theorem hasValueArgument_not_isStatic (kind : Kind)
    (h : hasValueArgument kind = true) : isStatic kind = false := by
  cases kind <;> simp_all (config := { decide := true })

theorem hasValueArgument_not_preservesCallerContext (kind : Kind)
    (h : hasValueArgument kind = true) : preservesCallerContext kind = false := by
  cases kind <;> simp_all (config := { decide := true })

theorem isStatic_not_preservesCallerContext (kind : Kind)
    (h : isStatic kind = true) : preservesCallerContext kind = false := by
  cases kind <;> simp_all (config := { decide := true })

end CallArgs

end EvmAsm.Evm64
