/-
  EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence

  SDIV wrapper composition through the dividend absolute-value block.
-/

import EvmAsm.Evm64.SDiv.Compose.DividendAbsPre

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Postcondition for the SDIV dividend-abs block: each limb is XORed
    with `mask = -sign` and the ripple-carry add of `sign` is propagated
    through the four limbs. Wrapped `@[irreducible]` to hide the let
    chain from downstream proofs. -/
@[irreducible]
def dividendAbsPost (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
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

theorem dividendAbsPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    dividendAbsPost sp sign limb0 limb1 limb2 limb3 =
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
  delta dividendAbsPost
  rfl

theorem dividendAbs_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCode base)
      (dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (dividendAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [dividendAbsPre_unfold, dividendAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact cpsTripleWithin_extend_code hmono hSpec

/-- Precondition for the SDIV save-ra + dividend/divisor signs +
    dividendAbs prefix. Takes only the bare wrapper inputs; the
    `sp`-relative dividend/divisor memory addresses are computed
    internally so the let-chain that previously lived in the theorem
    signature stays hidden inside this `@[irreducible]` def. -/
@[irreducible]
def saveRaSignsThenDividendAbsPre
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word) : Assertion :=
  let mem0 := sp + signExtend12 (0 : BitVec 12)
  let mem1 := sp + signExtend12 (8 : BitVec 12)
  let mem2 := sp + signExtend12 (16 : BitVec 12)
  let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
     ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
    ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
   (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
     (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
    ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))

theorem saveRaSignsThenDividendAbsPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
        maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop =
      (let mem0 := sp + signExtend12 (0 : BitVec 12)
       let mem1 := sp + signExtend12 (8 : BitVec 12)
       let mem2 := sp + signExtend12 (16 : BitVec 12)
       let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
          ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
         ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))) := by
  delta saveRaSignsThenDividendAbsPre
  rfl

/-- Postcondition for the SDIV save-ra/signs/dividendAbs prefix. Takes
    only the bare wrapper inputs; the sign/mask/sum/carry let-chain
    (~12 derived values) is computed internally so the theorem signature
    stays flat. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaSignsThenDividendAbsPost
    (vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word) : Assertion :=
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + signExtend12 (0 : BitVec 12)
  let mem1 := sp + signExtend12 (8 : BitVec 12)
  let mem2 := sp + signExtend12 (16 : BitVec 12)
  let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (dividendTop ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
    ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
   ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
    (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))

theorem saveRaSignsThenDividendAbsPost_unfold
    {vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPost vRa sp divisorTop limb0 limb1 limb2 dividendTop =
      (let sign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let mem0 := sp + signExtend12 (0 : BitVec 12)
       let mem1 := sp + signExtend12 (8 : BitVec 12)
       let mem2 := sp + signExtend12 (16 : BitVec 12)
       let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (dividendTop ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
         ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
         (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))) := by
  delta saveRaSignsThenDividendAbsPost
  rfl

theorem saveRa_signs_then_dividendAbs_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCode base)
      (saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        divisorTop maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop)
      (saveRaSignsThenDividendAbsPost vRa sp divisorTop
        limb0 limb1 limb2 dividendTop) := by
  rw [saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold]
  -- Re-introduce the let-chain locally so the existing composition proof
  -- (which references these derived names) keeps working unchanged.
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + signExtend12 (0 : BitVec 12)
  let mem1 := sp + signExtend12 (8 : BitVec 12)
  let mem2 := sp + signExtend12 (16 : BitVec 12)
  let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := dividendTop ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let extra : Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
      ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
       ((.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : cpsTripleWithin 5 base (base + dividendAbsOff)
      (sdivCode base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc,
      saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold] using
      (cpsTripleWithin_frameR
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
        (by pcFree)
        (saveRa_dividendSign_then_divisorSign_spec_in_sdivCode
          vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop
          base))
  have hAbs : cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (sdivCode base) absPre post := by
    have hSpec := dividendAbs_spec_in_sdivCode
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    rw [dividendAbsPre_unfold, dividendAbsPost_unfold] at hSpec
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        hSpec
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose
