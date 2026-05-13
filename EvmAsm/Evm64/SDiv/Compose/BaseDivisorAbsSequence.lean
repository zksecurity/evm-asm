/-
  EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsSequence

  SDIV wrapper base spec for the divisor absolute-value block.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence

namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV divisor-abs (conditional 2's-complement
    negation) block. Mirrors `dividendAbsPre` but with the sign in `x9`
    and limb memory cells at the `+32 … +56` divisor slots. Wrapped
    `@[irreducible]` so downstream proofs do not re-unfold the sepConj
    atoms at each use site. -/
@[irreducible]
def divisorAbsPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
  ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
  ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
  ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limb3)

theorem divisorAbsPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
       ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limb3)) := by
  delta divisorAbsPre
  rfl

/-- Postcondition for the SDIV divisor-abs block: mirrors
    `dividendAbsPost` but with the sign register `x9` and the divisor
    memory slots `+32 … +56`. Wrapped `@[irreducible]` to hide the let
    chain from downstream proofs. -/
@[irreducible]
def divisorAbsPost (sp sign limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
  ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
  ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
  ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ sum3)

theorem divisorAbsPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
       ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ sum3)) := by
  delta divisorAbsPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
