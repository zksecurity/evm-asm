/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnPre

  Named preconditions for result sign-fix specs that hide scratch registers
  behind ownership.
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

end EvmAsm.Evm64.SDiv.Compose
