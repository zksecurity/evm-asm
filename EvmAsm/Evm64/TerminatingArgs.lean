/-
  EvmAsm.Evm64.TerminatingArgs

  Pure stack-argument records for frame-terminating opcodes (GH #113).

  Mirrors the LogArgs / CallArgs pattern: a `Kind` classifier covering
  STOP, RETURN, REVERT, INVALID, and SELFDESTRUCT, together with a
  `TerminatingArgs` structure capturing the (offset, size) pair that
  RETURN and REVERT pop off the stack to describe the returned memory
  slice.

  This file is intentionally pure / RISC-V-free: it gives downstream
  spec/program files (under #113) a stable surface to refer to before
  the assembly-level handlers land.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace TerminatingArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- Frame-terminating opcode classifier. -/
inductive Kind where
  | stop
  | return_
  | revert
  | invalid
  | selfdestruct
  deriving DecidableEq, Repr

/-- Stack arguments for RETURN/REVERT: a memory range describing the
returned/reverted byte slice. STOP / INVALID / SELFDESTRUCT carry no
relevant memory range here (SELFDESTRUCT pops a beneficiary address,
modeled separately). -/
structure Args where
  data : MemoryRange
  deriving Repr

/-- RETURN/REVERT pop two stack words (offset, size); STOP / INVALID
pop none; SELFDESTRUCT pops one (the beneficiary address). -/
def stackArgumentCount : Kind → Nat
  | .stop => 0
  | .return_ => 2
  | .revert => 2
  | .invalid => 0
  | .selfdestruct => 1

/-- Whether the opcode reads a memory slice off the stack. -/
def hasMemoryRange : Kind → Bool
  | .stop => false
  | .return_ => true
  | .revert => true
  | .invalid => false
  | .selfdestruct => false

/-- Whether the opcode signals a successful (non-error) termination.
RETURN and STOP succeed; REVERT and INVALID fail; SELFDESTRUCT succeeds
with respect to frame status. -/
def isSuccess : Kind → Bool
  | .stop => true
  | .return_ => true
  | .revert => false
  | .invalid => false
  | .selfdestruct => true

/-- Whether the opcode reverts in-frame state changes. Only REVERT
preserves the caller's pre-call state; INVALID also rolls back but
additionally consumes all gas. -/
def reverts : Kind → Bool
  | .stop => false
  | .return_ => false
  | .revert => true
  | .invalid => true
  | .selfdestruct => false

/-- Convenience builder used by RETURN/REVERT consumers. -/
def returnArgs (offset size : EvmWord) : Args :=
  { data := { offset := offset, size := size } }

/-- Convenience builder used by RETURN/REVERT consumers (REVERT alias). -/
def revertArgs (offset size : EvmWord) : Args :=
  { data := { offset := offset, size := size } }

theorem stackArgumentCountStop :
    stackArgumentCount .stop = 0 := rfl

theorem stackArgumentCountReturn :
    stackArgumentCount .return_ = 2 := rfl

theorem stackArgumentCountRevert :
    stackArgumentCount .revert = 2 := rfl

theorem stackArgumentCountInvalid :
    stackArgumentCount .invalid = 0 := rfl

theorem stackArgumentCountSelfdestruct :
    stackArgumentCount .selfdestruct = 1 := rfl

theorem hasMemoryRangeReturn :
    hasMemoryRange .return_ = true := rfl

theorem hasMemoryRangeRevert :
    hasMemoryRange .revert = true := rfl

theorem hasMemoryRangeStop :
    hasMemoryRange .stop = false := rfl

theorem hasMemoryRangeInvalid :
    hasMemoryRange .invalid = false := rfl

theorem hasMemoryRangeSelfdestruct :
    hasMemoryRange .selfdestruct = false := rfl

theorem isSuccessReturn : isSuccess .return_ = true := rfl
theorem isSuccessStop : isSuccess .stop = true := rfl
theorem isSuccessRevert : isSuccess .revert = false := rfl
theorem isSuccessInvalid : isSuccess .invalid = false := rfl
theorem isSuccessSelfdestruct : isSuccess .selfdestruct = true := rfl

theorem revertsRevert : reverts .revert = true := rfl
theorem revertsInvalid : reverts .invalid = true := rfl
theorem revertsReturn : reverts .return_ = false := rfl
theorem revertsStop : reverts .stop = false := rfl
theorem revertsSelfdestruct : reverts .selfdestruct = false := rfl

theorem returnArgs_offset (offset size : EvmWord) :
    (returnArgs offset size).data.offset = offset := rfl

theorem returnArgs_size (offset size : EvmWord) :
    (returnArgs offset size).data.size = size := rfl

theorem revertArgs_offset (offset size : EvmWord) :
    (revertArgs offset size).data.offset = offset := rfl

theorem revertArgs_size (offset size : EvmWord) :
    (revertArgs offset size).data.size = size := rfl

theorem stackArgumentCount_eq_two_of_hasMemoryRange (kind : Kind) :
    hasMemoryRange kind = true → stackArgumentCount kind = 2 := by
  cases kind <;> simp [hasMemoryRange, stackArgumentCount]

end TerminatingArgs

end EvmAsm.Evm64
