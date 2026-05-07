/-
  EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec

  Sibling-frame variants of the per-quarter stack specs in
  `EvmAsm/Evm64/MLoad/UnalignedStackSpec.lean`. Each wrapper takes an
  arbitrary `pcFree` assertion `F` and frames it on both pre and post.

  These are the prerequisite for the four-quarter compose slice toward
  the topmost `evm_mload_stack_spec_within` (evm-asm-75z1x / evm-asm-lrhou /
  GH #53 follow-up): the compose helper
  `evm_mload_combined_one_limb_sequence_stack_spec_within`
  (`EvmAsm/Evm64/MLoad/StackSpec.lean`) chains four quarter triples whose
  intermediate `Pi` are abstract. To plug the concrete q0..q3 specs from
  `UnalignedStackSpec.lean` into that helper, each quarter's pre/post must
  thread the *other three* quarters' byte-window cells (as future-frame
  for not-yet-loaded quarters; as already-loaded cells for past quarters).
  The generic `F` parameter lets the compose slice instantiate `F` with
  exactly the sibling-cell sep_conj it needs at each step.

  Direct MLOAD analog of `EvmAsm/Evm64/MStore/UnalignedFramedStackSpec.lean`
  (evm-asm-81sv2 / PR #3139).

  Distinctive token: evm_mload_unaligned_one_limb_q*_stack_spec_within_framed
  sibling-quarter cells #53.
-/

import EvmAsm.Evm64.MLoad.StackSpec
import EvmAsm.Evm64.MLoad.UnalignedStackSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
Sibling-framed MLOAD prologue stack spec: `mload_prologue_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

This is the prologue counterpart to the q0..q3 sibling-framed lemmas below.
The full unaligned MLOAD compose slice uses it to preserve the byte-window and
destination-cell frame while the initial stack offset is loaded and the
absolute memory address is computed.

Distinctive token: mload_prologue_stack_spec_within_framed sibling-quarter
cells #53.
-/
theorem mload_prologue_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  have core := mload_prologue_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base
    h_off_ne_x0 h_addr_ne_x0
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q0 stack spec: `evm_mload_unaligned_one_limb_q0_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Used by the compose slice `evm_mload_unaligned_full_stack_spec_within`
(evm-asm-75z1x) to thread the not-yet-loaded q1/q2/q3 byte-window cells
through q0's triple.

Distinctive token: evm_mload_unaligned_one_limb_q0_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q0_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 23 (base + 8) (base + 100)
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ mloadPackedLimbFromDwordPair loVal hiVal start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q0_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q1 stack spec: `evm_mload_unaligned_one_limb_q1_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q1_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q1_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 23 (base + 100) (base + 192)
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal1 hiVal1 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q1_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old
    loAddr1 hiAddr1 loVal1 hiVal1 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q2 stack spec: `evm_mload_unaligned_one_limb_q2_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q2_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q2_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 23 (base + 192) (base + 284)
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal2 hiVal2 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q2_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old q1Old
    loAddr2 hiAddr2 loVal2 hiVal2 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q3 stack spec: `evm_mload_unaligned_one_limb_q3_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q3_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q3_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old q2Old : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 23 (base + 284) (base + 376)
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal3 hiVal3 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q3_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old q1Old q2Old
    loAddr3 hiAddr3 loVal3 hiVal3 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

end EvmAsm.Evm64
