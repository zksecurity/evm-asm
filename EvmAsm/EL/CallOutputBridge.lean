/-
  EvmAsm.EL.CallOutputBridge

  Generic CALL-family result/output bridge for GH #114.
-/

import EvmAsm.Evm64.CallArgs
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace CallOutputBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallResult := EvmAsm.EL.CallResult
abbrev Word256 := EvmAsm.EL.Word256

/-- EVM stack result flag for CALL-family opcodes: success pushes 1; revert
    and failure push 0. This mirrors `generic_call` in execution-specs. -/
def callResultSuccessFlag (result : CallResult) : Word256 :=
  match result.status with
  | .success => 1
  | .revert => 0
  | .failure => 0

/-- Output bytes copied back to caller memory, capped by the caller-provided
    output memory range size. -/
def copiedOutputForRange (result : CallResult) (range : MemoryRange) : List Byte :=
  (MessageCallExecution.propagatedOutput result).take range.size.toNat

theorem callResultSuccessFlag_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callResultSuccessFlag
        { status := .success, state := state, output := output, gasRemaining := gasRemaining } =
      1 := rfl

theorem callResultSuccessFlag_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callResultSuccessFlag
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining } =
      0 := rfl

theorem callResultSuccessFlag_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) :
    callResultSuccessFlag
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining } =
      0 := rfl

theorem callResultSuccessFlag_eq_one_iff (result : CallResult) :
    callResultSuccessFlag result = 1 ↔ result.status = .success := by
  cases result with
  | mk status state output gasRemaining =>
      cases status <;> simp [callResultSuccessFlag]

theorem copiedOutputForRange_success
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) (range : MemoryRange) :
    copiedOutputForRange
        { status := .success, state := state, output := output, gasRemaining := gasRemaining }
        range =
      output.take range.size.toNat := rfl

theorem copiedOutputForRange_revert
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) (range : MemoryRange) :
    copiedOutputForRange
        { status := .revert, state := state, output := output, gasRemaining := gasRemaining }
        range =
      output.take range.size.toNat := rfl

theorem copiedOutputForRange_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat) (range : MemoryRange) :
    copiedOutputForRange
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        range =
      [] := by
  simp [copiedOutputForRange, MessageCallExecution.propagatedOutput]

theorem copiedOutputForRange_length_eq_min (result : CallResult) (range : MemoryRange) :
    (copiedOutputForRange result range).length =
      Nat.min (MessageCallExecution.propagatedOutput result).length range.size.toNat := by
  rw [copiedOutputForRange, List.length_take]
  rw [Nat.min_comm]

theorem copiedOutputForRange_length_le_range (result : CallResult) (range : MemoryRange) :
    (copiedOutputForRange result range).length ≤ range.size.toNat := by
  rw [copiedOutputForRange_length_eq_min]
  exact Nat.min_le_right _ _

theorem copiedOutputForRange_length_le_output (result : CallResult) (range : MemoryRange) :
    (copiedOutputForRange result range).length ≤
      (MessageCallExecution.propagatedOutput result).length := by
  rw [copiedOutputForRange_length_eq_min]
  exact Nat.min_le_left _ _

end CallOutputBridge

end EvmAsm.EL
