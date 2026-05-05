/-
  EvmAsm.EL.CallOutputMemory

  Destination-address bridge for CALL-family returned bytes (GH #114).
-/

import Mathlib.Data.List.GetD
import EvmAsm.EL.CallOutputBridge

namespace EvmAsm.EL

namespace CallOutputMemory

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallResult := EvmAsm.EL.CallResult
abbrev Byte := EvmAsm.EL.Byte

/-- First caller-memory byte written by a CALL-family output copy. -/
def outputStart (range : MemoryRange) : Nat :=
  range.offset.toNat

/-- One-past-the-end caller-memory byte for a CALL-family output copy. -/
def outputEnd (range : MemoryRange) : Nat :=
  outputStart range + range.size.toNat

/-- Destination-relative index for a concrete caller-memory byte address. -/
def outputWriteIndex (range : MemoryRange) (addr : Nat) : Nat :=
  addr - outputStart range

/-- Prop-valued range predicate for addresses written by CALL-family output
    copying. -/
def writesOutputAddress (range : MemoryRange) (addr : Nat) : Prop :=
  outputStart range ≤ addr ∧ addr < outputEnd range

instance (range : MemoryRange) (addr : Nat) :
    Decidable (writesOutputAddress range addr) := by
  unfold writesOutputAddress
  infer_instance

/-- Byte copied back to caller memory at `addr`, or zero outside the output
    range. Distinctive token: CallOutputMemory.callOutputByteAt #114. -/
def callOutputByteAt (result : CallResult) (range : MemoryRange) (addr : Nat) : Byte :=
  if _ : writesOutputAddress range addr then
    (CallOutputBridge.copiedOutputForRange result range).getD
      (outputWriteIndex range addr) 0
  else
    0

theorem outputStart_eq (range : MemoryRange) :
    outputStart range = range.offset.toNat := rfl

theorem outputEnd_eq (range : MemoryRange) :
    outputEnd range = range.offset.toNat + range.size.toNat := rfl

theorem outputWriteIndex_eq (range : MemoryRange) (addr : Nat) :
    outputWriteIndex range addr = addr - range.offset.toNat := rfl

theorem writesOutputAddress_iff (range : MemoryRange) (addr : Nat) :
    writesOutputAddress range addr ↔
      range.offset.toNat ≤ addr ∧ addr < range.offset.toNat + range.size.toNat := by
  rfl

theorem writesOutputAddress_at_output_add
    {result : CallResult} {range : MemoryRange} {i : Nat}
    (h : i < (CallOutputBridge.copiedOutputForRange result range).length) :
    writesOutputAddress range (outputStart range + i) := by
  have h_le := CallOutputBridge.copiedOutputForRange_length_le_range result range
  unfold writesOutputAddress outputEnd outputStart
  omega

theorem outputWriteIndex_at_output_add (range : MemoryRange) (i : Nat) :
    outputWriteIndex range (outputStart range + i) = i := by
  unfold outputWriteIndex
  omega

theorem callOutputByteAt_outside
    {result : CallResult} {range : MemoryRange} {addr : Nat}
    (h : ¬ writesOutputAddress range addr) :
    callOutputByteAt result range addr = 0 := by
  rw [callOutputByteAt]
  rw [dif_neg h]

theorem callOutputByteAt_at_output_add
    {result : CallResult} {range : MemoryRange} {i : Nat}
    (h : i < (CallOutputBridge.copiedOutputForRange result range).length) :
    callOutputByteAt result range (outputStart range + i) =
      (CallOutputBridge.copiedOutputForRange result range)[i]'h := by
  rw [callOutputByteAt]
  rw [dif_pos (writesOutputAddress_at_output_add h)]
  rw [outputWriteIndex_at_output_add]
  exact List.getD_eq_getElem
    (l := CallOutputBridge.copiedOutputForRange result range) (d := 0) h

theorem callOutputByteAt_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (range : MemoryRange) (addr : Nat) :
    callOutputByteAt
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        range addr = 0 := by
  by_cases h : writesOutputAddress range addr
  · rw [callOutputByteAt, dif_pos h]
    simp [CallOutputBridge.copiedOutputForRange_failure]
  · exact callOutputByteAt_outside h

@[simp] theorem callOutputByteAt_zero_size
    (result : CallResult) (offset : EvmAsm.Evm64.EvmWord) (addr : Nat) :
    callOutputByteAt result { offset := offset, size := 0 } addr = 0 := by
  apply callOutputByteAt_outside
  intro h
  unfold writesOutputAddress outputEnd outputStart at h
  simp at h
  omega

end CallOutputMemory

end EvmAsm.EL
