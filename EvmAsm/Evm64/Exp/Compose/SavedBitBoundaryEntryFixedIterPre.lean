/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryFixedIterPre

  Named first-iteration precondition for the fixed saved-bit EXP loop entry.
  The fixed prologue advances x12 past the two EXP operands, so the first
  iteration sees the first two `rest` words at the advanced stack pointer.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Canonical fixed-loop first-iteration precondition after the prologue.
    The first two words below the EXP operands become the `d`/`e` limb groups
    at the advanced iteration stack pointer `evmSp + 64`. -/
@[irreducible]
def expTwoMulFixedFirstIterPre
    (sp evmSp v10 v18 vOld v7 v11 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) : Assertion :=
  expTwoMulFixedIterPre
    (exponentWord.getLimbN 3)
    ((0 : Word) + signExtend12 (64 : BitVec 12))
    (256 : Word)
    v10 v18
    (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN 2)
    sp (evmSp + signExtend12 (64 : BitVec 12))
    (1 : Word) vOld
    ((1 : EvmWord).getLimbN 0)
    ((1 : EvmWord).getLimbN 1)
    ((1 : EvmWord).getLimbN 2)
    ((1 : EvmWord).getLimbN 3)
    (dWord.getLimbN 0) (dWord.getLimbN 1)
    (dWord.getLimbN 2) (dWord.getLimbN 3)
    (eWord.getLimbN 0) (eWord.getLimbN 1)
    (eWord.getLimbN 2) (eWord.getLimbN 3)
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    v7 v11

theorem expTwoMulFixedFirstIterPre_unfold
    {sp evmSp v10 v18 vOld v7 v11 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} :
    expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
        baseWord exponentWord dWord eWord =
      expTwoMulFixedIterPre
        (exponentWord.getLimbN 3)
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (256 : Word)
        v10 v18
        (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (1 : Word) vOld
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (dWord.getLimbN 0) (dWord.getLimbN 1)
        (dWord.getLimbN 2) (dWord.getLimbN 3)
        (eWord.getLimbN 0) (eWord.getLimbN 1)
        (eWord.getLimbN 2) (eWord.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        v7 v11 := by
  delta expTwoMulFixedFirstIterPre
  rfl

/-- Folded-memory view of `expTwoMulFixedFirstIterPre`. This matches the
    `evmWordIs` vocabulary used by the fixed entry-post stack unfold. -/
theorem expTwoMulFixedFirstIterPre_unfold_words
    {sp evmSp v10 v18 vOld v7 v11 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} :
    expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
        baseWord exponentWord dWord eWord =
      (((((.x19 ↦ᵣ exponentWord.getLimbN 3) **
        (.x6 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        (.x5 ↦ᵣ (1 : Word)) **
        evmWordIs sp (1 : EvmWord) **
        evmWordIs (evmSp + 64) dWord **
        evmWordIs (evmSp + 96) eWord **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ (256 : Word))) ** evmWordIs evmSp baseWord) **
        (expTwoMulFixedIterPointerFrame
          (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2))) := by
  rw [expTwoMulFixedFirstIterPre_unfold, expTwoMulFixedIterPre_unfold,
    expTwoMulIterBaseFrame_unfold]
  unfold evmWordIs
  simp only [signExtend12_0, signExtend12_56, signExtend12_64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (56 : Word) + signExtend12 (-8 : BitVec 12) =
      signExtend12 (-8 : BitVec 12) + 56 from by bv_omega,
    show (signExtend12 (-8 : BitVec 12) + 56 : Word) = 48 from by decide,
    show (64 : Word) + 18446744073709551552 = 0 from by decide,
    show (64 : Word) + 18446744073709551560 = 8 from by decide,
    show (64 : Word) + 18446744073709551568 = 16 from by decide,
    show (64 : Word) + 18446744073709551576 = 24 from by decide,
    show (64 : Word) + 8 = 72 from by decide,
    show (64 : Word) + 16 = 80 from by decide,
    show (64 : Word) + 24 = 88 from by decide,
    show (96 : Word) + 8 = 104 from by decide,
    show (96 : Word) + 16 = 112 from by decide,
    show (96 : Word) + 24 = 120 from by decide,
    BitVec.add_assoc]
  funext ps
  apply propext
  constructor <;> intro h <;> sep_perm h

/-- First fixed-iteration precondition with the caller-scratch registers left as
    ownership atoms. This is the direct shape produced by the fixed entry post;
    a later bridge can choose concrete values for `x10`, `x7`, and `x11`. -/
@[irreducible]
def expTwoMulFixedFirstIterPreOwned
    (sp evmSp v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) : Assertion :=
  (((((.x19 ↦ᵣ exponentWord.getLimbN 3) **
    (.x6 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    regOwn .x10 ** (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
    (.x5 ↦ᵣ (1 : Word)) **
    evmWordIs sp (1 : EvmWord) **
    evmWordIs (evmSp + 64) dWord **
    evmWordIs (evmSp + 96) eWord **
    regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld)) **
    (.x9 ↦ᵣ (256 : Word))) ** evmWordIs evmSp baseWord) **
    (expTwoMulFixedIterPointerFrame
      (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
      (exponentWord.getLimbN 2)))

theorem expTwoMulFixedFirstIterPreOwned_unfold
    {sp evmSp v18 vOld : Word}
    {baseWord exponentWord dWord eWord : EvmWord} :
    expTwoMulFixedFirstIterPreOwned sp evmSp v18 vOld
        baseWord exponentWord dWord eWord =
      (((((.x19 ↦ᵣ exponentWord.getLimbN 3) **
        (.x6 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        regOwn .x10 ** (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        (.x5 ↦ᵣ (1 : Word)) **
        evmWordIs sp (1 : EvmWord) **
        evmWordIs (evmSp + 64) dWord **
        evmWordIs (evmSp + 96) eWord **
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ (256 : Word))) ** evmWordIs evmSp baseWord) **
        (expTwoMulFixedIterPointerFrame
          (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2))) := by
  delta expTwoMulFixedFirstIterPreOwned
  rfl

theorem expTwoMulFixedFirstIterPreOwned_pcFree
    {sp evmSp v18 vOld : Word}
    {baseWord exponentWord dWord eWord : EvmWord} :
    (expTwoMulFixedFirstIterPreOwned sp evmSp v18 vOld
      baseWord exponentWord dWord eWord).pcFree := by
  rw [expTwoMulFixedFirstIterPreOwned_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedFirstIterPreOwned
    (sp evmSp v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) :
    Assertion.PCFree
      (expTwoMulFixedFirstIterPreOwned sp evmSp v18 vOld
        baseWord exponentWord dWord eWord) :=
  ⟨expTwoMulFixedFirstIterPreOwned_pcFree⟩

abbrev expTwoMulFixedFirstIterScratchOwn : Assertion :=
  regOwn .x10 ** (regOwn .x7 ** regOwn .x11)

abbrev expTwoMulFixedFirstIterScratchIs
    (v10 v7 v11 : Word) : Assertion :=
  (.x10 ↦ᵣ v10) ** ((.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11))

theorem expTwoMulFixedFirstIterScratchOwn_choose_frame
    {frame : Assertion} {ps : PartialState}
    (h : (expTwoMulFixedFirstIterScratchOwn ** frame) ps) :
    ∃ v10 v7 v11,
      (expTwoMulFixedFirstIterScratchIs v10 v7 v11 ** frame) ps := by
  have h_front :
      (regOwn .x10 ** (regOwn .x7 ** (regOwn .x11 ** frame))) ps := by
    unfold expTwoMulFixedFirstIterScratchOwn at h
    sep_perm h
  obtain ⟨v10, h_v10_chain⟩ := sepConj_choose_regOwn h_front
  obtain ⟨ps_v10, ps_rest1, h_disjoint_v10, h_union_v10, h_v10, h_rest1⟩ :=
    h_v10_chain
  obtain ⟨v7, h_v7_chain⟩ := sepConj_choose_regOwn h_rest1
  obtain ⟨ps_v7, ps_rest2, h_disjoint_v7, h_union_v7, h_v7, h_rest2⟩ :=
    h_v7_chain
  obtain ⟨v11, h_v11_chain⟩ := sepConj_choose_regOwn h_rest2
  obtain ⟨ps_v11, ps_rest3, h_disjoint_v11, h_union_v11, h_v11, h_rest3⟩ :=
    h_v11_chain
  refine ⟨v10, v7, v11, ?_⟩
  have h_chosen :
      ((.x10 ↦ᵣ v10) ** ((.x7 ↦ᵣ v7) ** ((.x11 ↦ᵣ v11) ** frame))) ps := by
    refine ⟨ps_v10, ps_rest1, h_disjoint_v10, h_union_v10, h_v10, ?_⟩
    refine ⟨ps_v7, ps_rest2, h_disjoint_v7, h_union_v7, h_v7, ?_⟩
    exact ⟨ps_v11, ps_rest3, h_disjoint_v11, h_union_v11, h_v11, h_rest3⟩
  unfold expTwoMulFixedFirstIterScratchIs
  sep_perm h_chosen

theorem expTwoMulFixedFirstIterPreOwned_choose_frame
    {sp evmSp v18 vOld : Word}
    {baseWord exponentWord dWord eWord : EvmWord} {frame : Assertion}
    {ps : PartialState}
    (h : (expTwoMulFixedFirstIterPreOwned sp evmSp v18 vOld
      baseWord exponentWord dWord eWord ** frame) ps) :
    ∃ v10 v7 v11,
      (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
        baseWord exponentWord dWord eWord ** frame) ps := by
  rw [expTwoMulFixedFirstIterPreOwned_unfold] at h
  let restFrame : Assertion :=
    frame **
    expTwoMulFixedIterPointerFrame
      (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
      (exponentWord.getLimbN 2) **
    evmWordIs sp (1 : EvmWord) **
    evmWordIs evmSp baseWord **
    evmWordIs (evmSp + 64) dWord **
    evmWordIs (evmSp + 96) eWord **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x1 ↦ᵣ vOld) **
    (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ v18) **
    (.x19 ↦ᵣ exponentWord.getLimbN 3) **
    (.x2 ↦ᵣ sp) **
    (.x5 ↦ᵣ (1 : Word)) **
    (.x6 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x9 ↦ᵣ (256 : Word))
  have h_front : (expTwoMulFixedFirstIterScratchOwn ** restFrame) ps := by
    unfold expTwoMulFixedFirstIterScratchOwn
    dsimp [restFrame]
    sep_perm h
  obtain ⟨v10, v7, v11, h_scratch⟩ :=
    expTwoMulFixedFirstIterScratchOwn_choose_frame h_front
  refine ⟨v10, v7, v11, ?_⟩
  rw [expTwoMulFixedFirstIterPre_unfold_words]
  unfold expTwoMulFixedFirstIterScratchIs at h_scratch
  dsimp [restFrame] at h_scratch
  sep_perm h_scratch

/-- Residual resources from the fixed entry post after the first fixed-iteration
    precondition consumes the accumulator, base word, the first two rest words,
    and the live exponent cursor cell at `evmSp + 48`. -/
@[irreducible]
def expTwoMulFixedFirstIterEntryResidual
    (evmSp : Word) (exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  ((evmSp + 32) ↦ₘ exponentWord.getLimbN 0) **
  ((evmSp + 40) ↦ₘ exponentWord.getLimbN 1) **
  ((evmSp + 56) ↦ₘ exponentWord.getLimbN 3) **
  evmStackIs (evmSp + 128) rest **
  regOwn .x6

theorem expTwoMulFixedFirstIterEntryResidual_unfold
    {evmSp : Word} {exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest =
      (((evmSp + 32) ↦ₘ exponentWord.getLimbN 0) **
       ((evmSp + 40) ↦ₘ exponentWord.getLimbN 1) **
       ((evmSp + 56) ↦ₘ exponentWord.getLimbN 3) **
       evmStackIs (evmSp + 128) rest **
       regOwn .x6) := by
  delta expTwoMulFixedFirstIterEntryResidual
  rfl

theorem expTwoMulFixedFirstIterEntryResidual_pcFree
    {evmSp : Word} {exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest).pcFree := by
  rw [expTwoMulFixedFirstIterEntryResidual_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedFirstIterEntryResidual
    (evmSp : Word) (exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) :=
  ⟨expTwoMulFixedFirstIterEntryResidual_pcFree⟩

/-- Direct fixed-entry bridge into the owned-scratch first-iteration shape plus
    the explicitly named residual frame. -/
theorem expTwoMulLoopEntryPostFixed_to_firstIterPreOwned_frame
    {sp evmSp vOld v18 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expTwoMulLoopEntryPostFixed sp evmSp vOld v18
      baseWord exponentWord (dWord :: eWord :: rest) ps) :
    (expTwoMulFixedFirstIterPreOwned sp evmSp v18 vOld
      baseWord exponentWord dWord eWord **
     expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps := by
  rw [expTwoMulLoopEntryPostFixed_unfold_rest2_offsets] at h
  rw [expTwoMulFixedFirstIterPreOwned_unfold,
    expTwoMulFixedFirstIterEntryResidual_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  unfold evmWordIs at h ⊢
  simp only [signExtend12_0, signExtend12_56, signExtend12_64,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (56 : Word) + signExtend12 (-8 : BitVec 12) =
      signExtend12 (-8 : BitVec 12) + 56 from by bv_omega,
    show (signExtend12 (-8 : BitVec 12) + 56 : Word) = 48 from by decide,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (64 : Word) + 8 = 72 from by decide,
    show (64 : Word) + 16 = 80 from by decide,
    show (64 : Word) + 24 = 88 from by decide,
    show (96 : Word) + 8 = 104 from by decide,
    show (96 : Word) + 16 = 112 from by decide,
    show (96 : Word) + 24 = 120 from by decide,
    BitVec.add_assoc] at h ⊢
  sep_perm h

theorem expTwoMulLoopEntryPostFixed_to_firstIterPre_frame
    {sp evmSp vOld v18 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expTwoMulLoopEntryPostFixed sp evmSp vOld v18
      baseWord exponentWord (dWord :: eWord :: rest) ps) :
    ∃ v10 v7 v11,
      (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
        baseWord exponentWord dWord eWord **
       expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps := by
  exact expTwoMulFixedFirstIterPreOwned_choose_frame
    (expTwoMulLoopEntryPostFixed_to_firstIterPreOwned_frame h)

theorem expTwoMulFixedFirstIterPre_pcFree
    {sp evmSp v10 v18 vOld v7 v11 : Word}
    {baseWord exponentWord dWord eWord : EvmWord} :
    (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
      baseWord exponentWord dWord eWord).pcFree := by
  rw [expTwoMulFixedFirstIterPre_unfold]
  exact expTwoMulFixedIterPre_pcFree

instance pcFreeInst_expTwoMulFixedFirstIterPre
    (sp evmSp v10 v18 vOld v7 v11 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) :
    Assertion.PCFree
      (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
        baseWord exponentWord dWord eWord) :=
  ⟨expTwoMulFixedFirstIterPre_pcFree⟩

end EvmAsm.Evm64.Exp.Compose
