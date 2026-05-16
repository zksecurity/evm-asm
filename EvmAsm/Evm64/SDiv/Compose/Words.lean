/-
  EvmAsm.Evm64.SDiv.Compose.Words

  Pure word-level helpers shared by SDIV div-call composition files.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64.SDiv.Compose

/-- Absolute-value word produced by the SDIV dividend sign/absolute-value
    prefix, packaged as a named expression so downstream callable-composition
    proofs do not duplicate the expanded `fromLimbs` term. -/
def sdivAbsDividendWord
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) : EvmWord :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let dividendMask := (0 : Word) - dividendSign
  let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
  let dividendCarry0 :=
    if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
  let dividendCarry1 :=
    if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
  let dividendCarry2 :=
    if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => dividendSum0 | 1 => dividendSum1 | 2 => dividendSum2 | 3 => dividendSum3

/-- Absolute-value word produced by the SDIV divisor sign/absolute-value
    prefix, paired with `sdivAbsDividendWord` for downstream composition
    statements that consume `divModStackDispatchPre`. -/
def sdivAbsDivisorWord
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmWord :=
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => divisorSum0 | 1 => divisorSum1 | 2 => divisorSum2 | 3 => divisorSum3

/-- Word produced by conditionally negating the unsigned quotient limbs by the
    SDIV result sign. This names the memory-result word of the result-sign
    fixup block before connecting it to the semantic `EvmWord.sdiv` result. -/
def sdivResultSignFixedWord
    (dividendTop divisorTop limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let mask := (0 : Word) - resultSign
  let sum0 := (limb0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => sum0 | 1 => sum1 | 2 => sum2 | 3 => sum3

/-- The SDIV result sign is the XOR of two top-bit extractions, hence it is a
    Boolean word. This keeps later result-sign-fix zero-quotient rewrites from
    reasoning about arbitrary 64-bit masks. -/
theorem sdivResultSign_bool (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 ∨ resultSign = 1 := by
  dsimp
  bv_decide


/-- The SDIV result sign is zero exactly when the operand sign bits match. -/
theorem sdivResultSign_eq_zero_iff
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 ↔
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat := by
  dsimp
  bv_decide

/-- The SDIV result sign is one exactly when the operand sign bits differ. -/
theorem sdivResultSign_eq_one_iff
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 1 ↔
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat := by
  dsimp
  bv_decide


/-- Conditional negation by the SDIV result sign leaves the zero quotient
    limbs equal to zero. The carries may be used internally by the sign-fix
    block, but the four memory-result limbs remain zero. -/
theorem sdivResultSign_fixZeroLimbs
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum0 = 0 ∧ sum1 = 0 ∧ sum2 = 0 ∧ sum3 = 0 := by
  dsimp
  bv_decide

/-- Top output limb of result-sign-fix is zero when the unsigned quotient is
    zero. -/
theorem sdivResultSign_fixZeroLimb3
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum3 = 0 := by
  have h := sdivResultSign_fixZeroLimbs dividendTop divisorTop
  simpa using h.2.2.2

/-- Word-shaped variant of `sdivResultSign_fixZeroLimb3`, matching callers that
    have already rewritten a quotient word to `0 : EvmWord` but not yet
    simplified its `getLimbN` projections. -/
theorem sdivResultSign_fixZeroWordLimb3
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := (((0 : EvmWord).getLimbN 0) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := (((0 : EvmWord).getLimbN 1) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := (((0 : EvmWord).getLimbN 2) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := (((0 : EvmWord).getLimbN 3) ^^^ mask) + carry2
    sum3 = 0 := by
  rw [EvmWord.getLimbN_zero 0, EvmWord.getLimbN_zero 1,
    EvmWord.getLimbN_zero 2, EvmWord.getLimbN_zero 3]
  exact sdivResultSign_fixZeroLimb3 dividendTop divisorTop

/-- If the dividend sign bit is zero, the dividend absolute-value word is just
    the original four-limb word. -/
theorem sdivAbsDividendWord_of_sign_zero
    (limb0 limb1 limb2 top : Word)
    (hSign : top >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => top := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs
  rw [hSign]
  bv_decide

/-- Four concrete `getLimbN` projections assemble back to their source word. -/
theorem sdivWord_from_getLimbN (v : EvmWord) :
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) =
      v := by
  unfold EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Word-shaped variant of `sdivAbsDividendWord_of_sign_zero`: if the dividend
    sign bit is zero, the SDIV absolute-value helper returns the dividend word. -/
theorem sdivAbsDividendWord_eq_word_of_sign_zero
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = dividend := by
  rw [sdivAbsDividendWord_of_sign_zero _ _ _ _ hSign]
  exact sdivWord_from_getLimbN dividend

/-- If the dividend sign bit is one, the SDIV absolute-value helper returns the
    two's-complement negation of the dividend word. -/
theorem sdivAbsDividendWord_eq_neg_word_of_sign_one
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = -dividend := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs
  rw [hSign]
  unfold EvmWord.getLimbN EvmWord.getLimb at hSign ⊢
  simp only [Neg.neg]
  bv_decide

/-- If the divisor sign bit is zero, the divisor absolute-value word is just the
    original four-limb word. -/
theorem sdivAbsDivisorWord_of_sign_zero
    (limb0 limb1 limb2 top : Word)
    (hSign : top >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => top := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  rw [hSign]
  bv_decide

/-- Word-shaped variant of `sdivAbsDivisorWord_of_sign_zero`: if the divisor
    sign bit is zero, the SDIV absolute-value helper returns the divisor word. -/
theorem sdivAbsDivisorWord_eq_word_of_sign_zero
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = divisor := by
  rw [sdivAbsDivisorWord_of_sign_zero _ _ _ _ hSign]
  exact sdivWord_from_getLimbN divisor

/-- If the divisor sign bit is one, the SDIV absolute-value helper returns the
    two's-complement negation of the divisor word. -/
theorem sdivAbsDivisorWord_eq_neg_word_of_sign_one
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = -divisor := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  rw [hSign]
  unfold EvmWord.getLimbN EvmWord.getLimb at hSign ⊢
  simp only [Neg.neg]
  bv_decide

/-- If the SDIV result sign is zero, the result-sign-fix word is just the
    unsigned quotient word assembled from its four limbs. -/
theorem sdivResultSignFixedWord_of_result_sign_zero
    (dividendTop divisorTop limb0 limb1 limb2 limb3 : Word)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (0 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop limb0 limb1 limb2 limb3 =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => limb3 := by
  unfold sdivResultSignFixedWord EvmWord.fromLimbs
  rw [hSign]
  bv_decide

/-- Word-shaped variant of `sdivResultSignFixedWord_of_result_sign_zero`: if
    the result sign is zero, the result-sign-fix helper leaves the quotient word
    unchanged. -/
theorem sdivResultSignFixedWord_eq_word_of_result_sign_zero
    (dividendTop divisorTop : Word) (quotient : EvmWord)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (0 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop
      (quotient.getLimbN 0) (quotient.getLimbN 1)
      (quotient.getLimbN 2) (quotient.getLimbN 3) = quotient := by
  rw [sdivResultSignFixedWord_of_result_sign_zero _ _ _ _ _ _ hSign]
  exact sdivWord_from_getLimbN quotient

/-- If the SDIV result sign is one, the result-sign-fix helper returns the
    two's-complement negation of the quotient word. -/
theorem sdivResultSignFixedWord_eq_neg_word_of_result_sign_one
    (dividendTop divisorTop : Word) (quotient : EvmWord)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (1 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop
      (quotient.getLimbN 0) (quotient.getLimbN 1)
      (quotient.getLimbN 2) (quotient.getLimbN 3) = -quotient := by
  unfold sdivResultSignFixedWord EvmWord.fromLimbs
  rw [hSign]
  unfold EvmWord.getLimbN EvmWord.getLimb
  simp only [Neg.neg]
  bv_decide

/-- The SDIV divisor absolute-value word is zero when all divisor limbs are
    zero. This discharges the internal bzero-branch hypothesis for the
    caller-visible zero-divisor stack case. -/
theorem sdivAbsDivisorWord_zero :
    sdivAbsDivisorWord 0 0 0 0 = 0 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  bv_decide

/-- The SDIV divisor absolute-value word is zero exactly for the zero
    divisor. This lets stack-level branch proofs switch between the
    caller-visible divisor and the unsigned-DIV dispatch divisor. -/
theorem sdivAbsDivisorWord_eq_zero_iff
    (divisor : EvmWord) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) = 0 ↔
      divisor = 0 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Nonzero caller-visible divisors stay nonzero after the SDIV absolute-value
    normalization used by the unsigned-DIV dispatch. -/
theorem sdivAbsDivisorWord_ne_zero_of_ne_zero
    {divisor : EvmWord} (h_ne : divisor ≠ 0) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((sdivAbsDivisorWord_eq_zero_iff divisor).mp h_abs_zero)

/-- The SDIV divisor absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation, depending on the
    caller-visible sign bit. -/
theorem sdivAbsDivisorWord_sign_split
    (divisor : EvmWord) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      if divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        divisor
      else
        ~~~divisor + 1 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Nonnegative SDIV divisors are unchanged by absolute-value normalization. -/
theorem sdivAbsDivisorWord_zero_sign
    {divisor : EvmWord}
    (h_sign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      divisor := by
  rw [sdivAbsDivisorWord_sign_split, if_pos h_sign]

/-- Negative SDIV divisors normalize to their two's-complement negation. -/
theorem sdivAbsDivisorWord_one_sign
    {divisor : EvmWord}
    (h_sign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      ~~~divisor + 1 := by
  have h_not_zero :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
    rw [h_sign]
    decide
  rw [sdivAbsDivisorWord_sign_split, if_neg h_not_zero]

/-- Nonnegative raw-limb SDIV divisors are unchanged by absolute-value
    normalization. -/
theorem sdivAbsDivisorWord_zero_limb_sign
    {divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (h_sign : divisorTop >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => divisorLimb0
        | 1 => divisorLimb1
        | 2 => divisorLimb2
        | 3 => divisorTop := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  rw [h_sign]
  bv_decide

/-- Negative raw-limb SDIV divisors normalize to their two's-complement
    negation. -/
theorem sdivAbsDivisorWord_one_limb_sign
    {divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (h_sign : divisorTop >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => divisorLimb0
        | 1 => divisorLimb1
        | 2 => divisorLimb2
        | 3 => divisorTop) + 1 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  rw [h_sign]
  bv_decide

/-- Raw-limb SDIV divisor absolute-value normalization split by the
    caller-visible sign bit. -/
theorem sdivAbsDivisorWord_limb_sign_split
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      if divisorTop >>> (63 : BitVec 6).toNat = 0 then
        EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => divisorLimb0
          | 1 => divisorLimb1
          | 2 => divisorLimb2
          | 3 => divisorTop
      else
        ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => divisorLimb0
          | 1 => divisorLimb1
          | 2 => divisorLimb2
          | 3 => divisorTop) + 1 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  bv_decide

/-- The SDIV dividend absolute-value word is zero exactly for the zero
    dividend. This mirrors the divisor bridge for semantic stack views that
    reason about wrapper-normalized operands. -/
theorem sdivAbsDividendWord_eq_zero_iff
    (dividend : EvmWord) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) = 0 ↔
      dividend = 0 := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Nonzero caller-visible dividends stay nonzero after the SDIV
    absolute-value normalization. -/
theorem sdivAbsDividendWord_ne_zero_of_ne_zero
    {dividend : EvmWord} (h_ne : dividend ≠ 0) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((sdivAbsDividendWord_eq_zero_iff dividend).mp h_abs_zero)

/-- The SDIV dividend absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation, depending on the
    caller-visible sign bit. -/
theorem sdivAbsDividendWord_sign_split
    (dividend : EvmWord) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      if dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        dividend
      else
        ~~~dividend + 1 := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Nonnegative SDIV dividends are unchanged by absolute-value normalization. -/
theorem sdivAbsDividendWord_zero_sign
    {dividend : EvmWord}
    (h_sign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      dividend := by
  rw [sdivAbsDividendWord_sign_split, if_pos h_sign]

/-- Negative SDIV dividends normalize to their two's-complement negation. -/
theorem sdivAbsDividendWord_one_sign
    {dividend : EvmWord}
    (h_sign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      ~~~dividend + 1 := by
  have h_not_zero :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
    rw [h_sign]
    decide
  rw [sdivAbsDividendWord_sign_split, if_neg h_not_zero]

/-- Nonnegative raw-limb SDIV dividends are unchanged by absolute-value
    normalization. -/
theorem sdivAbsDividendWord_zero_limb_sign
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word}
    (h_sign : dividendTop >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => dividendLimb0
        | 1 => dividendLimb1
        | 2 => dividendLimb2
        | 3 => dividendTop := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs
  rw [h_sign]
  bv_decide

/-- Negative raw-limb SDIV dividends normalize to their two's-complement
    negation. -/
theorem sdivAbsDividendWord_one_limb_sign
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word}
    (h_sign : dividendTop >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => dividendLimb0
        | 1 => dividendLimb1
        | 2 => dividendLimb2
        | 3 => dividendTop) + 1 := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs
  rw [h_sign]
  bv_decide

/-- Raw-limb SDIV dividend absolute-value normalization split by the
    caller-visible sign bit. -/
theorem sdivAbsDividendWord_limb_sign_split
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      if dividendTop >>> (63 : BitVec 6).toNat = 0 then
        EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => dividendLimb0
          | 1 => dividendLimb1
          | 2 => dividendLimb2
          | 3 => dividendTop
      else
        ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => dividendLimb0
          | 1 => dividendLimb1
          | 2 => dividendLimb2
          | 3 => dividendTop) + 1 := by
  unfold sdivAbsDividendWord EvmWord.fromLimbs
  bv_decide

/-- Word produced by conditionally negating four quotient limbs with the SDIV
    result sign. This names the post-result-sign-fix `fromLimbs` term so
    stack-level views can fold the four memory atoms into one `evmWordIs`. -/
def sdivSignFixedWord
    (sign limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => sum0 | 1 => sum1 | 2 => sum2 | 3 => sum3

/-- If the SDIV result sign is zero, result-sign fixup leaves the quotient
    word unchanged. -/
theorem sdivSignFixedWord_zero_sign (word : EvmWord) :
    sdivSignFixedWord 0
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      word := by
  have hzero : (0 : Word) - (0 : Word) = 0 := by decide
  have hxor : ∀ x : Word, x ^^^ (0 : Word) = x := fun x => by bv_decide
  have hult0 : ∀ x : Word, BitVec.ult x (0 : Word) = false := fun x => by bv_decide
  have hbool : ¬(false = true) := by decide
  have hadd0 : ∀ x : Word, x + 0 = x := fun x => by bv_decide
  unfold sdivSignFixedWord
  simp only [hzero, hxor, hult0, if_neg hbool, hadd0]
  exact sdivWord_from_getLimbN word

/-- Conditional result-sign fixup maps a zero quotient to the zero word. -/
theorem sdivSignFixedWord_zero_quotient
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign 0 0 0 0 = 0 := by
  dsimp
  unfold sdivSignFixedWord EvmWord.fromLimbs
  bv_decide

/-- If the SDIV result sign is one, result-sign fixup computes two's-complement
    negation of the quotient word. -/
theorem sdivSignFixedWord_one_sign (word : EvmWord) :
    sdivSignFixedWord 1
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      ~~~word + 1 := by
  unfold sdivSignFixedWord EvmWord.fromLimbs EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- Boolean result signs reduce result-sign fixup to either the original
    quotient word or its explicit two's-complement negation. -/
theorem sdivSignFixedWord_bool_sign
    (sign : Word) (h_sign : sign = 0 ∨ sign = 1) (word : EvmWord) :
    sdivSignFixedWord sign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if sign = 0 then word else ~~~word + 1 := by
  obtain h_zero | h_one := h_sign
  · rw [h_zero, sdivSignFixedWord_zero_sign]
    simp
  · rw [h_one, sdivSignFixedWord_one_sign]
    simp

/-- Specialized boolean-sign split for the SDIV result sign derived from the
    operand top limbs. -/
theorem sdivSignFixedWord_result_sign
    (dividendTop divisorTop : Word) (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if resultSign = 0 then word else ~~~word + 1 := by
  dsimp
  exact sdivSignFixedWord_bool_sign
    ((dividendTop >>> 63) ^^^ (divisorTop >>> 63))
    (sdivResultSign_bool dividendTop divisorTop) word

/-- Same operand signs make SDIV result-sign fixup leave the unsigned
    quotient word unchanged. -/
theorem sdivSignFixedWord_same_sign
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat)
    (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      word := by
  dsimp at h_sign ⊢
  have h_result :
      (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 0 := by
    bv_decide
  rw [h_result]
  exact sdivSignFixedWord_zero_sign word

/-- Opposite operand signs make SDIV result-sign fixup compute the
    two's-complement negation of the unsigned quotient word. -/
theorem sdivSignFixedWord_opposite_sign
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat)
    (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      ~~~word + 1 := by
  dsimp at h_sign ⊢
  have h_result :
      (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 1 := by
    bv_decide
  rw [h_result]
  exact sdivSignFixedWord_one_sign word

/-- SDIV result-sign fixup split directly by equality of the operand sign
    bits. This is the caller-facing branch condition used by the final stack
    spec. -/
theorem sdivSignFixedWord_sign_bits
    (dividendTop divisorTop : Word) (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if dividendTop >>> (63 : BitVec 6).toNat =
          divisorTop >>> (63 : BitVec 6).toNat then
        word
      else
        ~~~word + 1 := by
  by_cases h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat
  · rw [if_pos h_sign]
    exact sdivSignFixedWord_same_sign h_sign word
  · rw [if_neg h_sign]
    exact sdivSignFixedWord_opposite_sign h_sign word

/-- Equal SDIV operand sign bits make the result sign zero. -/
theorem sdivResultSign_zero_of_eq
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 := by
  dsimp
  bv_decide

/-- Distinct SDIV operand sign bits make the result sign one. -/
theorem sdivResultSign_one_of_ne
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 1 := by
  dsimp
  bv_decide

end EvmAsm.Evm64.SDiv.Compose
