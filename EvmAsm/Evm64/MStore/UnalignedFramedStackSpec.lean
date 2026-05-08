/-
  EvmAsm.Evm64.MStore.UnalignedFramedStackSpec

  Sibling-frame variants of the per-quarter stack specs in
  `EvmAsm/Evm64/MStore/UnalignedStackSpec.lean`. Each wrapper takes an
  arbitrary `pcFree` assertion `F` and frames it on both pre and post.

  These are the prerequisite for the four-quarter compose slice toward the
  topmost `evm_mstore_stack_spec_within` (evm-asm-f159q / evm-asm-ln8t5 /
  GH #53 follow-up): the compose helper
  `evm_mstore_combined_one_limb_sequence_stack_spec_within`
  (`EvmAsm/Evm64/MStore/StackSpec.lean`) chains four quarter triples whose
  intermediate `Pi` are abstract. To plug the concrete q0..q3 specs from
  `UnalignedStackSpec.lean` into that helper, each quarter's pre/post must
  thread the *other three* quarters' byte-window cells (as future-frame for
  not-yet-stored quarters; as already-stored cells for past quarters). The
  generic `F` parameter lets the compose slice instantiate `F` with
  exactly the sibling-cell sep_conj it needs at each step.

  Distinctive token: evm_mstore_unaligned_one_limb_q*_stack_spec_within_framed
  sibling-quarter cells #53.
-/

import EvmAsm.Evm64.MStore.StackSpec
import EvmAsm.Evm64.MStore.UnalignedStackSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
Sibling-framed MSTORE prologue stack spec: `mstore_prologue_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

This is the prologue counterpart to the q0..q3 sibling-framed lemmas below.
The full unaligned MSTORE compose slice uses it to preserve the byte-window and
source-limb frame while the initial stack offset is loaded and the absolute
memory address is computed.

Distinctive token: mstore_prologue_stack_spec_within_framed sibling-quarter
cells #53.
-/
theorem mstore_prologue_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  have core := mstore_prologue_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base
    h_off_ne_x0 h_addr_ne_x0
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
EVM-code transport of `mstore_prologue_stack_spec_within_framed`.

Later full-stack unaligned MSTORE composition can use this theorem directly at
the public `evm_mstore_code` boundary instead of carrying an extra stack-code
transport step.

Distinctive token: evm_mstore_prologue_stack_spec_within_framed #53.
-/
theorem evm_mstore_prologue_stack_spec_within_framed
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 8)
    (mstore_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)

/--
Framed version of `evm_mstore_combined_one_limb_sequence_stack_spec_within`.

This wrapper preserves an arbitrary `pcFree` frame across the whole prologue
plus four-quarter byte-window write sequence, which is useful once the concrete
q0..q3 lemmas have been composed into a single MSTORE sequence triple.

Distinctive token:
evm_mstore_combined_one_limb_sequence_stack_spec_within_framed #53.
-/
theorem evm_mstore_combined_one_limb_sequence_stack_spec_within_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreOneLimbCode addrReg byteReg accReg
          32 24 25 26 27 28 29 30 31 (base + 8))
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreOneLimbCode addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23 (base + 76)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mstore_combined_one_limb_sequence_stack_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h0 h1 h2 h3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Threaded-frame variant of `evm_mstore_combined_one_limb_sequence_stack_spec_within`.

Unlike the whole-sequence frame wrapper above, this theorem starts q0 from the
prologue postcondition already combined with `F`. That matches the concrete
q0..q3 sibling-framed MSTORE lemmas below, where the frame carries the other
window cells through each quarter.

Distinctive token:
evm_mstore_combined_one_limb_sequence_stack_spec_within_threaded_frame #53.
-/
theorem evm_mstore_combined_one_limb_sequence_stack_spec_within_threaded_frame
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreOneLimbCode addrReg byteReg accReg
          32 24 25 26 27 28 29 30 31 (base + 8))
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreOneLimbCode addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23 (base + 76)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 280)
    (cpsTripleWithin_seq_same_cr
      (mstore_prologue_stack_spec_within_framed
        offReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase base F hF
        h_off_ne_x0 h_addr_ne_x0)
      (cpsTripleWithin_extend_code
        (h := mstore_one_limb_sequence_spec_within
          addrReg byteReg accReg base h0 h1 h2 h3)
        (hmono := mstoreStackCode_four_limbs_sub
          offReg byteReg accReg addrReg memBaseReg base)))

/--
Sibling-framed q0 stack spec: `evm_mstore_unaligned_one_limb_q0_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Used by the compose slice `evm_mstore_unaligned_full_stack_spec_within`
(evm-asm-f159q) to thread the not-yet-stored q1/q2/q3 byte-window cells
through q0's triple.

Distinctive token: evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q0_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q1 stack spec: `evm_mstore_unaligned_one_limb_q1_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 17 (base + 76) (base + 144)
      (mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q1_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q2 stack spec: `evm_mstore_unaligned_one_limb_q2_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 17 (base + 144) (base + 212)
      (mstoreOneLimbCode addrReg byteReg accReg
        48 8 9 10 11 12 13 14 15 (base + 144))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q2_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Sibling-framed q3 stack spec: `evm_mstore_unaligned_one_limb_q3_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 17 (base + 212) (base + 280)
      (mstoreOneLimbCode addrReg byteReg accReg
        56 0 1 2 3 4 5 6 7 (base + 212))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q3_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

end EvmAsm.Evm64
