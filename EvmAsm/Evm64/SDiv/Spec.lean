/-
  EvmAsm.Evm64.SDiv.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_sdiv`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). The
  actual `evm_sdiv_stack_spec_within` theorem lands in slice
  evm-asm-01uh and is composed from the verified shared bridge with
  the boundary blocks.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchZeroDivisor
import EvmAsm.Evm64.SDiv.Compose.DivCallExactReturnHandoff
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SDiv.Compose

/-- Nonnegative/nonnegative exact-path SDIV result bridge.

    When both input signs are zero, the assembly absolute-value helpers leave
    both operands unchanged and the result-sign-fix helper leaves the unsigned
    quotient unchanged. In that case `EvmWord.div` and `EvmWord.sdiv` agree. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Negative/negative exact-path SDIV result bridge.

    When both input signs are one, the assembly absolute-value helpers produce
    `-dividend` and `-divisor`; the result sign is zero, so the result-sign-fix
    helper leaves the unsigned quotient unchanged. This is the `true,true`
    branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Nonnegative/negative exact-path SDIV result bridge.

    When only the divisor is negative, the assembly divisor absolute-value
    helper produces `-divisor` and result-sign-fix negates the unsigned
    quotient. This is the `false,true` branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (1 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Top-level zero-divisor SDIV stack bridge with the concrete semantic
    zero-result stack shape.

    This is the caller-visible zero-divisor path through the full `sdivCode`,
    specialized to the EVM rule `SDIV x 0 = 0`. The remaining saved-register
    and DIV scratch frame stays explicit for the final all-case
    `evm_sdiv_stack_spec_within`. -/
theorem evm_sdiv_zero_divisor_result_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: (0 : EvmWord) :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorSign := (0 : Word) >>> (63 : BitVec 6).toNat
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^ divisorSign
       let mask := (0 : Word) - resultSign
       let sum0 := ((0 : Word) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((0 : Word) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((0 : Word) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((0 : Word) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) :=
  saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_spec_in_sdivCode
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase

/-- Top-level zero-divisor SDIV stack bridge.

    This is the caller-visible zero-divisor path through the full `sdivCode`:
    the wrapper normalizes signs, calls the unsigned DIV zero-divisor branch,
    applies result-sign fixup, returns to the saved caller address, and exposes
    the post stack using the executable `sdivHandler` view. The remaining
    saved-register and DIV scratch frame stays explicit for the final all-case
    `evm_sdiv_stack_spec_within`. -/
theorem evm_sdiv_zero_divisor_handler_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: (0 : EvmWord) :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorSign := (0 : Word) >>> (63 : BitVec 6).toNat
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^ divisorSign
       let mask := (0 : Word) - resultSign
       let sum0 := ((0 : Word) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((0 : Word) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((0 : Word) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((0 : Word) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32)
          ((ArithmeticHandlers.sdivHandler
            { state with stack := dividend :: (0 : EvmWord) :: rest }).stack)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) :=
  saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_handler_stack_spec_in_sdivCode
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 state dividend rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase

/-- Top-level exact-callable SDIV stack-tail bridge.

    This is the caller-visible exact path through `sdivCode`, parameterized
    by the unsigned DIV no-NOP proof that discharges the branch-specific
    callable obligation. It preserves the untouched stack tail at `sp+64`
    while exposing the post-DIV/sign-fix return post used by the final
    all-case stack theorem. -/
theorem evm_sdiv_exact_return_stack_tail_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       evmStackIs (sp + 64) rest) :=
  saveRa_signs_abs_signXor_then_divCall_exact_then_return_stack_tail_from_handoff_spec_in_sdivCode
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend divisor rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack

/-- Top-level exact-callable SDIV result-stack bridge.

    This folds the exact return path's result-sign-fix memory output into
    `evmStackIs (sp + 32)`. The result word is the named result-sign-fixed
    quotient word; the final bridge from that word to `EvmWord.sdiv dividend
    divisor` remains a separate pure semantic step. -/
theorem evm_sdiv_exact_return_result_stack_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultWord :=
         sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let divisorSign := divisor.getLimbN 3 >>> (63 : BitVec 6).toNat
       let mask := (0 : Word) - resultSign
       let sum0 := ((quotientWord.getLimbN 0) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((quotientWord.getLimbN 1) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((quotientWord.getLimbN 2) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((quotientWord.getLimbN 3) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
      rw [saveRaDivCallCallableReturnPost_unfold] at hp
      dsimp only at hp ⊢
      rw [resultSignFixPost_sdivResultSign_word
        (sp + 32) (dividend.getLimbN 3) (divisor.getLimbN 3)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 0)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 1)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 2)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 3)] at hp
      rw [evmStackIs_cons]
      rw [show (sp + 32 + 32 : Word) = sp + 64 by bv_decide]
      xperm_hyp hp)
    (evm_sdiv_exact_return_stack_tail_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- Exact-callable SDIV handler-stack bridge, parameterized by the remaining
    pure result-word equality.

    The assembly side has already produced the named sign-fixed quotient
    word. This theorem isolates the final semantic obligation as
    `hResult`, then exposes the executable `sdivHandler` stack view. -/
theorem evm_sdiv_exact_return_handler_stack_of_result_eq_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))))
    (hResult :
      let dividendAbsWord :=
        sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
          (dividend.getLimbN 2) (dividend.getLimbN 3)
      let divisorAbsWord :=
        sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
          (divisor.getLimbN 2) (divisor.getLimbN 3)
      let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
      sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
        (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
        (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
        EvmWord.sdiv dividend divisor) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let divisorSign := divisor.getLimbN 3 >>> (63 : BitVec 6).toNat
       let mask := (0 : Word) - resultSign
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let sum0 := ((quotientWord.getLimbN 0) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((quotientWord.getLimbN 1) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((quotientWord.getLimbN 2) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((quotientWord.getLimbN 3) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32)
          ((ArithmeticHandlers.sdivHandler
            { state with stack := dividend :: divisor :: rest }).stack)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [hResult] at hp
      simpa using hp)
    (evm_sdiv_exact_return_result_stack_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

-- Placeholder: full all-case `evm_sdiv_stack_spec_within` lands in slice 4
-- (evm-asm-01uh). The signed-division correctness lemma
-- `EvmWord.sdiv_correct` is added in slice 3 (evm-asm-kvs4).

end EvmAsm.Evm64
