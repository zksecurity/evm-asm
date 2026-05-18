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
