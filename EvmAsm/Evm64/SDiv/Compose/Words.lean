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

/-- The SDIV divisor absolute-value word is zero when all divisor limbs are
    zero. This discharges the internal bzero-branch hypothesis for the
    caller-visible zero-divisor stack case. -/
theorem sdivAbsDivisorWord_zero :
    sdivAbsDivisorWord 0 0 0 0 = 0 := by
  unfold sdivAbsDivisorWord EvmWord.fromLimbs
  bv_decide

end EvmAsm.Evm64.SDiv.Compose
