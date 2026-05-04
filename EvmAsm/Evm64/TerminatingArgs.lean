/-
  EvmAsm.Evm64.TerminatingArgs

  Pure stack-argument records for RETURN and REVERT (GH #113).

  RETURN and REVERT both pop a memory offset and size from the stack and
  return/revert the corresponding memory slice.  This module factors that
  shared shape into a tiny pure record so future handler specs and the
  interpreter dispatch layer can talk about it without committing to any
  particular EvmState representation.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace TerminatingArgs

/-- Memory slice described by an EVM offset and byte size.  Mirrors
    `LogArgs.MemoryRange` and `CallArgs.MemoryRange` so call sites can
    share helpers in the future without coercing between record types. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- Terminating opcode arity classifier — RETURN vs REVERT. -/
inductive Kind where
  | return_
  | revert_
  deriving DecidableEq, Repr

/-- Stack arguments for RETURN/REVERT: just the data memory range. -/
structure Args where
  data : MemoryRange
  deriving Repr

/-- RETURN and REVERT both pop exactly two stack words (offset, size). -/
def stackArgumentCount (_kind : Kind) : Nat := 2

/-- The data memory range projected from a terminating-args record. -/
def dataRange (args : Args) : MemoryRange :=
  args.data

theorem stackArgumentCount_return : stackArgumentCount .return_ = 2 := rfl
theorem stackArgumentCount_revert : stackArgumentCount .revert_ = 2 := rfl

theorem dataRange_offset (offset size : EvmWord) :
    (dataRange { data := { offset := offset, size := size } }).offset = offset := rfl

theorem dataRange_size (offset size : EvmWord) :
    (dataRange { data := { offset := offset, size := size } }).size = size := rfl

end TerminatingArgs

end EvmAsm.Evm64
