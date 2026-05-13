/-
  EvmAsm.Evm64.SDiv.Compose.DivCallDispatch

  Defines the post-shape directly consumed by
  `evm_div_callable_spec_in_sdivCode`: the `divModStackDispatchPre` bundle
  (the dispatcher's pre, which the callable consumes) paired with the
  SDIV-wrapper-private sign frame (`.x8 = resultSign`, `.x9 = divisorSign`,
  `.x18 = vRa + signExtend12 0`). Infrastructure-only — the proof that
  `saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode`'s
  post equals this shape is a separate sub-slice (evm-asm-2long).

  Slice 4 micro evm-asm-mnva9. Authored by @pirapira; implemented by
  Hermes-bot (claude-c1).
-/

import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.Bridges
import EvmAsm.Evm64.SDiv.Compose.BzeroPost
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.SDiv.Compose.DispatchViews
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SDiv.Compose.SignFrame
import EvmAsm.Evm64.SDiv.Compose.Words
namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Prefix through the SDIV `divCall`, weakened to the exact dispatch-ready
    postcondition consumed by `evm_div_callable_spec_in_sdivCode`. -/
theorem saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    cpsTripleWithin 49 base
      ((base + divCallOff) + signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    rw [saveRaSignsAbsSignXorThenDivCallPost_unfold] at hq
    rw [saveRaDivCallDispatchReadyPost_unfold]
    dsimp only at hq ⊢
    rw [sdivDivCallSignFrame_unfold]
    rw [divModStackDispatchPre_unfold_explicit_sdiv]
    simp [sdivAbsDividendWord, sdivAbsDivisorWord, EvmWord.getLimbN,
      EvmWord.getLimb_fromLimbs] at hq ⊢
    xperm_hyp hq) hPrefix

/-- Sequence the SDIV wrapper prefix with any callable proof that consumes the
    exact dispatch-ready post. This isolates the SDIV-specific target-PC
    alignment; a later slice can supply the stronger callable proof for this
    exact `x1` handoff shape. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCode
    {nSteps : Nat} {callPost : Assertion}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base callableExit : Word)
    (hCallable :
      cpsTripleWithin nSteps (base + wrapperEndOff) callableExit (sdivCode base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        callPost) :
    cpsTripleWithin (49 + nSteps) base callableExit (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      callPost := by
  have hPrefixRaw :=
    saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  have hPrefix : cpsTripleWithin 49 base (base + wrapperEndOff) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
    rw [← divCall_target_eq_wrapperEndOff base]
    exact hPrefixRaw
  exact cpsTripleWithin_seq_same_cr hPrefix hCallable

/-- SDIV wrapper prefix followed by the zero-divisor branch of the unsigned DIV
    callable, stopping at the result-sign-fixup entry. The hypothesis `hbz`
    is over the already-normalized divisor word produced by the SDIV absolute
    value prefix. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_callable_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (49 + (EvmAsm.Evm64.unifiedDivBound + 1))
      base (base + resultSignFixOff) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
        (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
       ((.x8 ↦ᵣ ((dividendTop >>> (63 : BitVec 6).toNat) ^^^
          (divisorTop >>> (63 : BitVec 6).toNat))) **
        (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
        (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))))) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^ divisorSign
  let signFrame : Assertion :=
    ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
      (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))))
  have hCallableRaw :=
    EvmAsm.Evm64.evm_div_callable_bzero_preserving_x1_spec
      sp (base + wrapperEndOff) ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by simpa [divisorAbsWord] using hbz)
  have hCallableCode :=
    cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_sub_sdivCode (base := base)) hCallableRaw
  have hCallableFramed :=
    cpsTripleWithin_frameR signFrame (by
      dsimp [signFrame]
      pcFree) hCallableCode
  have hCallableFramedExit :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCode base)
        (EvmAsm.Evm64.divModStackDispatchPre sp dividendAbsWord divisorAbsWord
          ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrame)
        ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrame) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  have hCallable :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCode base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrame) := by
    exact cpsTripleWithin_weaken (fun h hp => by
      rw [saveRaDivCallDispatchReadyPost_unfold] at hp
      dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
        divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
        divisorSum3, divisorCarry3, resultSign, signFrame] at hp ⊢
      rw [sdivDivCallSignFrame_unfold] at hp
      exact hp) (fun h hp => by
      dsimp [signFrame] at hp ⊢
      exact hp) hCallableFramedExit
  have hSeq :=
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff) hCallable
  simpa [dividendAbsWord, divisorAbsWord, divisorSign, resultSign, signFrame] using hSeq

/-- SDIV wrapper prefix followed by the zero-divisor unsigned-DIV callable,
    using the named postcondition consumed by later composition slices. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_callable_named_post_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (49 + (EvmAsm.Evm64.unifiedDivBound + 1))
      base (base + resultSignFixOff) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  have h :=
    saveRa_signs_abs_signXor_then_divCall_bzero_callable_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz
  rw [saveRaDivCallBzeroCallablePost_unfold]
  exact h

/-- SDIV zero-divisor path through the final result sign-fix block. The
    unsigned DIV callable has already produced a zero quotient at the current
    stack top, so this composes the named callable post with
    `resultSignFix_regOwn_scratch_spec_in_sdivCode`. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_resultSignFix_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin ((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_bzero_callable_named_post_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz
  have hFramePc :
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord).pcFree := by
    rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
      EvmAsm.Evm64.divScratchOwnCall_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hFix :=
    cpsTripleWithin_frameR
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord)
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_sdivCode
        (sp + 32) resultSign 0 0 0 0 base)
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch hbz] at hp
      exact hp)
    hPrefix hFix

/-- SDIV zero-divisor path through the saved-RA return instruction. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (((vRa + signExtend12 (0 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
       (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_bzero_then_resultSignFix_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz
  have hRetFramePc :
      (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord).pcFree := by
    rw [resultSignFixPost_unfold, saveRaDivCallBzeroSavedRaRetFrame_unfold,
      EvmAsm.Evm64.divScratchOwnCall_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hRetFramed :=
    cpsTripleWithin_frameR
      (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_sdivCode
        (vRa + signExtend12 (0 : BitVec 12)) base)
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + signExtend12 (0 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (sdivCode base)
        ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
          saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord))
        ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
         (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
          saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
    rw [hFall]
    exact hRetFramed
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [saveRaDivCallBzeroResultSignFixFrame_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

/-- Normalized return-target view of the SDIV zero-divisor path. This hides
    the two `signExtend12 0` artifacts introduced by the saved-RA move and
    the final `JALR`, leaving downstream callers with the ordinary masked
    saved return address. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_normalized_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ vRa) **
       (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  have hExit :
      (((vRa + signExtend12 (0 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [signExtend12_0]
    bv_decide
  rw [← hExit]
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      simp only [signExtend12_0] at hp ⊢
      have hRa : (vRa + (0 : Word)) = vRa := by bv_decide
      rw [hRa] at hp
      exact hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

/-- Zero-divisor SDIV path through return, with the result stack word exposed
    as the concrete zero EVM word after result-sign fixup. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
         evmWordIs (sp + 32) (0 : EvmWord)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [resultSignFixPost_sdivResultSign_zero_word (sp + 32) dividendTop divisorTop] at hp
      exact hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_normalized_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

/-- Framed variant of the SDIV zero-divisor return path that preserves the
    untouched stack tail below the two consumed operands. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_rest_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       evmStackIs (sp + 64) rest)
      ((let dividendAbsWord :=
          sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        let resultSign :=
          (dividendTop >>> (63 : BitVec 6).toNat) ^^^
            (divisorTop >>> (63 : BitVec 6).toNat)
        let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
          evmWordIs (sp + 32) (0 : EvmWord)) **
         saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) **
       evmStackIs (sp + 64) rest) := by
  exact cpsTripleWithin_frameR (evmStackIs (sp + 64) rest) pcFree_evmStackIs
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

/-- Stack-shaped postcondition for the SDIV zero-divisor return path: the
    produced zero result is folded together with the untouched tail stack. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_stack_zero_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       evmStackIs (sp + 64) rest)
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      dsimp only at hp ⊢
      rw [evmStackIs_cons]
      rw [show (sp + 32 + 32 : Word) = sp + 64 by bv_addr]
      xperm_hyp hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_rest_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 rest base hbase hbz)

/-- Stack-entry view of the zero-divisor SDIV return path. The operands are
    supplied as EVM words in the caller-visible stack, while the scratch and
    saved-register frame remains explicit for later top-level packaging. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz :
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
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
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  exact cpsTripleWithin_weaken (fun h hp => by
      let scratchFrame : Assertion :=
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      have h_old :
          ((saveRaSignsAbsSignXorThenDivCallPre
              vRa vSavedOld sp sDividendOld sDivisorOld
              dividendMaskOld dividendValueOld dividendCarryOld
              (dividend.getLimbN 0) (dividend.getLimbN 1)
              (dividend.getLimbN 2) (dividend.getLimbN 3)
              (divisor.getLimbN 0) (divisor.getLimbN 1)
              (divisor.getLimbN 2) (divisor.getLimbN 3) **
            evmStackIs (sp + 64) rest) ** scratchFrame) h := by
        rw [saveRaSignsAbsSignXorThenDivCallPre_stack_pair_rest]
        dsimp [scratchFrame]
        exact hp
      dsimp [scratchFrame] at h_old
      xperm_hyp h_old) (fun _ hp => hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_stack_zero_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 rest base hbase hbz)

/-- Caller-visible zero-divisor specialization of the SDIV bzero stack-entry
    path. The internal absolute-divisor-zero proof is discharged from
    `(0 : EvmWord).getLimbN k = 0`, leaving the precondition in ordinary
    stack shape. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
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
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  have hbz :
      sdivAbsDivisorWord ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
        ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3) = 0 := by
    simpa only [EvmWord.getLimbN_zero] using sdivAbsDivisorWord_zero
  simpa only [EvmWord.getLimbN_zero] using
    (saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend (0 : EvmWord) rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

end EvmAsm.Evm64.SDiv.Compose
