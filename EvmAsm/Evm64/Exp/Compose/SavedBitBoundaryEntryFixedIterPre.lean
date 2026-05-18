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
  simp only [signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56, signExtend12_64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (56 : Word) + signExtend12 (-8 : BitVec 12) =
      signExtend12 (-8 : BitVec 12) + 56 from by bv_omega,
    show (64 : Word) + 32 = 96 from by decide,
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
