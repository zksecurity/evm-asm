/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFree

  PC-free instances for named SDIV div-call postcondition bundles.  Kept
  separate from `DivCallDispatch.lean`, which is at the Compose line cap.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

abbrev sdivAbsSign (top : Word) : Word :=
  top >>> (63 : BitVec 6).toNat

abbrev sdivAbsMask (top : Word) : Word :=
  (0 : Word) - sdivAbsSign top

abbrev sdivAbsSum0 (limb0 top : Word) : Word :=
  (limb0 ^^^ sdivAbsMask top) + sdivAbsSign top

abbrev sdivAbsCarry0 (limb0 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum0 limb0 top) (sdivAbsSign top) then (1 : Word) else 0

abbrev sdivAbsSum1 (limb0 limb1 top : Word) : Word :=
  (limb1 ^^^ sdivAbsMask top) + sdivAbsCarry0 limb0 top

abbrev sdivAbsCarry1 (limb0 limb1 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum1 limb0 limb1 top) (sdivAbsCarry0 limb0 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum2 (limb0 limb1 limb2 top : Word) : Word :=
  (limb2 ^^^ sdivAbsMask top) + sdivAbsCarry1 limb0 limb1 top

abbrev sdivAbsCarry2 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum2 limb0 limb1 limb2 top)
      (sdivAbsCarry1 limb0 limb1 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum3 (limb0 limb1 limb2 top : Word) : Word :=
  (top ^^^ sdivAbsMask top) + sdivAbsCarry2 limb0 limb1 limb2 top

abbrev sdivAbsCarry3 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum3 limb0 limb1 limb2 top)
      (sdivAbsCarry2 limb0 limb1 limb2 top) then
    (1 : Word)
  else
    0

theorem sdivAbsDividendWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem sdivAbsDivisorWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem divModStackDispatchPre_pcFree
    {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    (EvmAsm.Evm64.divModStackDispatchPre sp a b
      v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
  rw [EvmAsm.Evm64.divModStackDispatchPre_unfold,
    EvmAsm.Evm64.divScratchValuesCall_unfold]
  pcFree

instance pcFreeInst_divModStackDispatchPre
    (sp : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) :
    Assertion.PCFree
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) :=
  ⟨divModStackDispatchPre_pcFree⟩

theorem divStackDispatchPostNoX1_pcFree {sp : Word} {a b : EvmWord} :
    (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b).pcFree := by
  rw [EvmAsm.Evm64.divStackDispatchPostNoX1_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_divStackDispatchPostNoX1
    (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b) :=
  ⟨divStackDispatchPostNoX1_pcFree⟩

/-- Variant of the preserving-`x1` unsigned-DIV callable wrapper whose no-NOP
    body proof already has the exact caller return address in the dispatch
    precondition. This avoids tying SDIV's exact handoff to
    `DivStackSpecCase.x1`, whose nonzero constructors use the dispatcher-local
    scratch value `0` instead of the wrapper return address. -/
theorem evm_div_callable_preserving_x1_exact_pre_spec_in_sdivCode
    (sp base raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCode base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStackCallDiv :=
    cpsTripleWithin_extend_code
      (hmono := EvmAsm.Evm64.divCode_noNop_sub_div_callable_code)
      hStack
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_sub_sdivCode (base := base))
      hStackCallDiv
  have hRetDiv :=
    cpsTripleWithin_extend_code
      (hmono := EvmAsm.Evm64.evm_div_callable_code_ret_sub
        (base := base + wrapperEndOff))
      (ret_spec_within' ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff) raVal)
  have hRet :=
    cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_sub_sdivCode (base := base))
      hRetDiv
  have hRetFramed :=
    cpsTripleWithin_frameL
      (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b)
      (divStackDispatchPostNoX1_pcFree (sp := sp) (a := a) (b := b))
      hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

/-- Frame the exact-pre preserving-`x1` unsigned-DIV callable wrapper by an
    arbitrary PC-free assertion. This is the shape needed once SDIV has a
    no-NOP proof for the exact dispatch-ready post, including the private sign
    frame. -/
theorem evm_div_callable_preserving_x1_exact_pre_framed_spec_in_sdivCode
    {F : Assertion} [Assertion.PCFree F]
    (sp base raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCode base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_preserving_x1_exact_pre_spec_in_sdivCode
        sp base raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- Frame the preserving-`x1` unsigned-DIV callable wrapper by an arbitrary
    PC-free assertion. SDIV uses this for the private sign frame carried across
    the exact callable handoff. -/
theorem evm_div_callable_preserving_x1_framed_spec_in_sdivCode
    {F : Assertion} [Assertion.PCFree F]
    (sp base raVal : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : EvmAsm.Evm64.DivStackSpecCase (base + wrapperEndOff) a b)
    (hStack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCode base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_preserving_x1_spec_in_sdivCode
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

/-- The named zero-divisor callable handoff from the SDIV dispatch-ready
    bundle to the zero-divisor callable post. This isolates the callable
    proof currently needed by the larger result-sign-fix composition. -/
theorem saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCode
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCode base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
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
  have hStack :=
    EvmAsm.Evm64.evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
      sp (base + wrapperEndOff) dividendAbsWord divisorAbsWord
      ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by simpa [divisorAbsWord] using hbz)
  have hCallableFramed :=
    evm_div_callable_preserving_x1_framed_spec_in_sdivCode
      (F := signFrame) sp base ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (EvmAsm.Evm64.DivStackSpecCase.bzero ((base + divCallOff) + 4) v2
        (by simpa [divisorAbsWord] using hbz))
      hStack
  have hCallableExit :
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
  exact cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, signFrame] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallBzeroCallablePost_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign, signFrame] at hp ⊢
    exact hp) hCallableExit

/-- SDIV wrapper prefix followed by the zero-divisor unsigned-DIV callable,
    using the sidecar dispatch-ready handoff above. This mirrors the named
    callable-post theorem in `DivCallDispatch.lean` without adding proof bulk
    to that capped file. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_callable_named_post_from_handoff_spec_in_sdivCode
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
  exact
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff)
      (saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCode
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hbz)

/-- Zero-divisor SDIV path through result-sign-fix and the saved-RA return,
    specialized from the sidecar bzero callable handoff. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_normalized_named_post_from_handoff_spec_in_sdivCode
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
      (saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  exact
    saveRa_signs_abs_signXor_then_divCall_then_return_normalized_named_post_of_callable_post_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
      (saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCode
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hbz)

theorem saveRaDivCallBzeroCallablePost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallBzeroCallablePost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallBzeroCallablePost_unfold]
  dsimp
  rw [EvmAsm.Evm64.divStackDispatchPostNoX1_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallBzeroCallablePost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    Assertion.PCFree
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallBzeroCallablePost_pcFree⟩

theorem saveRaDivCallBzeroResultSignFixFrame_pcFree
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    (saveRaDivCallBzeroResultSignFixFrame
      vRa sp base divisorSign dividendAbsWord).pcFree := by
  rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallBzeroResultSignFixFrame
    (vRa sp base divisorSign : Word) (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord) :=
  ⟨saveRaDivCallBzeroResultSignFixFrame_pcFree⟩

theorem saveRaDivCallBzeroSavedRaRetFrame_pcFree
    {sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    (saveRaDivCallBzeroSavedRaRetFrame
      sp base divisorSign dividendAbsWord).pcFree := by
  rw [saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallBzeroSavedRaRetFrame
    (sp base divisorSign : Word) (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (saveRaDivCallBzeroSavedRaRetFrame
        sp base divisorSign dividendAbsWord) :=
  ⟨saveRaDivCallBzeroSavedRaRetFrame_pcFree⟩

theorem resultSignFixPost_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPost sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPost_unfold]
  dsimp
  pcFree

instance pcFreeInst_resultSignFixPost
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    Assertion.PCFree (resultSignFixPost sp sign limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPost_pcFree⟩

theorem resultSignFixPreOwnX10_pcFree
    {sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnX10
      sp sign valueOld carryOld limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnX10_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnX10
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) :
    Assertion.PCFree
      (resultSignFixPreOwnX10
        sp sign valueOld carryOld limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnX10_pcFree⟩

theorem resultSignFixPreOwnX10X7_pcFree
    {sp sign carryOld limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnX10X7
      sp sign carryOld limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnX10X7_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnX10X7
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) :
    Assertion.PCFree
      (resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnX10X7_pcFree⟩

theorem resultSignFixPreOwnScratch_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnScratch_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnScratch
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    Assertion.PCFree (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnScratch_pcFree⟩

theorem resultSignFixPost_bzeroResultSignFixFrame_pcFree
    {vRa sp base divisorSign sign limb0 limb1 limb2 limb3 : Word}
    {dividendAbsWord : EvmWord} :
    (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
      saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord).pcFree := by
  pcFree

instance pcFreeInst_resultSignFixPost_bzeroResultSignFixFrame
    (vRa sp base divisorSign sign limb0 limb1 limb2 limb3 : Word)
    (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
        saveRaDivCallBzeroResultSignFixFrame
          vRa sp base divisorSign dividendAbsWord) :=
  ⟨resultSignFixPost_bzeroResultSignFixFrame_pcFree⟩

theorem resultSignFixPost_savedRaRetFrame_pcFree
    {sp base divisorSign sign limb0 limb1 limb2 limb3 : Word}
    {dividendAbsWord : EvmWord} :
    (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
      saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord).pcFree := by
  pcFree

instance pcFreeInst_resultSignFixPost_savedRaRetFrame
    (sp base divisorSign sign limb0 limb1 limb2 limb3 : Word)
    (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord) :=
  ⟨resultSignFixPost_savedRaRetFrame_pcFree⟩

end EvmAsm.Evm64.SDiv.Compose
