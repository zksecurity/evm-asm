/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

  Boundary-block sequence helpers for the corrected two-MUL saved-bit EXP
  code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- EXP prologue followed by the pointer-advance block, lifted to the
    two-MUL saved-bit EXP+MUL code bundle. This lands at the iteration-body
    entry with the EVM stack pointer advanced by one operand window. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
        (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
       (.x12 ↦ᵣ evmSp))
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
        (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        evmWordIs sp (1 : EvmWord)) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) := by
  have hPrologue :=
    exp_prologue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPrologueFramed :=
    cpsTripleWithin_frameR (.x12 ↦ᵣ evmSp) (by pcFree) hPrologue
  have hPointer :=
    exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      evmSp squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPointerFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord))
      (by pcFree)
      hPointer
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp)
      hPrologueFramed hPointerFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Stack-operand framed view of the two-MUL saved-bit EXP prologue followed
    by pointer advance. This preserves the visible EVM operand windows and
    caller-saved scratch ownership while the accumulator is initialized to one
    and `x12` advances to the loop-facing pointer. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_operand_frame_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let operandFrame : Assertion :=
      evmWordIs evmSp baseWord ** evmWordIs (evmSp + 32) exponentWord **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
         (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
        (.x12 ↦ᵣ evmSp)) ** operandFrame)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
         (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
         evmWordIs sp (1 : EvmWord)) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) ** operandFrame) := by
  intro operandFrame
  have hBase :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR operandFrame (by
    dsimp [operandFrame]
    pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Pointer-restore followed by the EXP epilogue in the two-MUL saved-bit
    EXP+MUL code bundle. This packages the loop-exit boundary from
    `base + 264` through the final stack-facing writeback at `base + 304`. -/
theorem exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  let epilogueFrame : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)
  have hRestore :=
    exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      (evmSp + signExtend12 (64 : BitVec 12))
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hRestoreFramed := cpsTripleWithin_frameR epilogueFrame (by
    dsimp [epilogueFrame]
    pcFree) hRestore
  have hPtr : (evmSp + signExtend12 (64 : BitVec 12)) +
      signExtend12 ((-64) : BitVec 12) = evmSp := by
    have hNeg64 :
        signExtend12 ((-64) : BitVec 12) =
          (18446744073709551552 : Word) := by decide
    rw [signExtend12_64, hNeg64]
    bv_decide
  have hRestoreFramed' :
      cpsTripleWithin 1 (base + 264) (base + 268)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) ** epilogueFrame)
        ((.x12 ↦ᵣ evmSp) ** epilogueFrame) := by
    rw [hPtr] at hRestoreFramed
    exact hRestoreFramed
  have hEpilogue :=
    exp_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp [epilogueFrame] at hp ⊢
        xperm_hyp hp)
      hRestoreFramed' hEpilogue
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [epilogueFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => hp)
    hSeq

end EvmAsm.Evm64.Exp.Compose
