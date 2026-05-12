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

end EvmAsm.Evm64.SDiv.Compose
