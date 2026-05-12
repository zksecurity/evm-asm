/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn

  Register-ownership wrappers for the SDIV result sign-fix block. The DIV
  callable post exposes sign-fix scratch registers as `regOwn`; this file
  starts packaging the standard `resultSignFix_spec_in_sdivCode` behind that
  shape one register at a time.
-/

import EvmAsm.Evm64.SDiv.Compose.Base

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Result sign-fix precondition with `x10` hidden behind ownership. -/
@[irreducible]
def resultSignFixPreOwnX10 (sp sign valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
    (.x7 ↦ᵣ valueOld)) ** (.x11 ↦ᵣ carryOld)) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) ** regOwn .x10

theorem resultSignFixPreOwnX10_unfold
    {sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPreOwnX10 sp sign valueOld carryOld limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
        (.x7 ↦ᵣ valueOld)) ** (.x11 ↦ᵣ carryOld)) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) ** regOwn .x10) := by
  delta resultSignFixPreOwnX10
  rfl

/-- SDIV result sign-fix spec that consumes owned `x10` instead of requiring
    a concrete old mask value. -/
theorem resultSignFix_regOwn_x10_spec_in_sdivCode
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      (resultSignFixPreOwnX10 sp sign valueOld carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10_unfold]
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro maskOld
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPre_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_spec_in_sdivCode sp sign maskOld valueOld carryOld
      limb0 limb1 limb2 limb3 base)

/-- Result sign-fix precondition with `x10` and `x7` hidden behind ownership. -/
@[irreducible]
def resultSignFixPreOwnX10X7 (sp sign carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
    (.x11 ↦ᵣ carryOld)) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
    regOwn .x10) ** regOwn .x7

theorem resultSignFixPreOwnX10X7_unfold
    {sp sign carryOld limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
        (.x11 ↦ᵣ carryOld)) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
        regOwn .x10) ** regOwn .x7) := by
  delta resultSignFixPreOwnX10X7
  rfl

/-- SDIV result sign-fix spec that consumes owned `x10` and `x7`, leaving
    only the old `x11` carry value concrete. -/
theorem resultSignFix_regOwn_x10_x7_spec_in_sdivCode
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      (resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnX10X7_unfold]
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro valueOld
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_spec_in_sdivCode sp sign valueOld carryOld
      limb0 limb1 limb2 limb3 base)

/-- Result sign-fix precondition with all scratch registers hidden behind
    ownership. -/
@[irreducible]
def resultSignFixPreOwnScratch (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
    regOwn .x10) ** regOwn .x7) ** regOwn .x11

theorem resultSignFixPreOwnScratch_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x8 ↦ᵣ sign)) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
        regOwn .x10) ** regOwn .x7) ** regOwn .x11) := by
  delta resultSignFixPreOwnScratch
  rfl

/-- SDIV result sign-fix spec that consumes owned `x10`, `x7`, and `x11`. -/
theorem resultSignFix_regOwn_scratch_spec_in_sdivCode
    (sp sign limb0 limb1 limb2 limb3 : Word) (base : Word) :
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPreOwnScratch_unfold]
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro carryOld
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [resultSignFixPreOwnX10X7_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_x7_spec_in_sdivCode sp sign carryOld
      limb0 limb1 limb2 limb3 base)

end EvmAsm.Evm64.SDiv.Compose
