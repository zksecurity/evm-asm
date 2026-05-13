/-
  EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix

  SDIV wrapper base spec for the result sign-fixup block.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsSequence

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Precondition for the SDIV result sign-fixup (conditional 2's-complement
    negation) block. The unsigned DIV callable returns with `x12` advanced
    to the quotient cell, so this block operates on offsets `0…24` from the
    live stack pointer. Wrapped `@[irreducible]` so downstream proofs do not
    re-unfold the sepConj atoms at each use site. -/
@[irreducible]
def resultSignFixPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem resultSignFixPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta resultSignFixPre
  rfl

/-- Postcondition for the SDIV result sign-fixup block: mirrors
    `divisorAbsPost` but with the sign register `x8`. Wrapped
    `@[irreducible]` to hide the let chain from downstream proofs. -/
@[irreducible]
def resultSignFixPost (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)

theorem resultSignFixPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)) := by
  delta resultSignFixPost
  rfl

theorem resultSignFix_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      (resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPre_unfold, resultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose
