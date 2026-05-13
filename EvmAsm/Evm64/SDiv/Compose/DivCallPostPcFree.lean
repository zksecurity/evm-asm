/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFree

  PC-free instances for named SDIV div-call postcondition bundles.  Kept
  separate from `DivCallDispatch.lean`, which is at the Compose line cap.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallBzeroCallableHandoff

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Exact SDIV path through result-sign-fix, specialized from the sidecar
    exact callable handoff and stopping before the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_resultSignFix_named_post_from_handoff_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    cpsTripleWithin ((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallResultSignFixPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  exact
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
      (saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCode
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hStack)

/-- Exact SDIV path through result-sign-fix and the saved-RA return,
    specialized from the sidecar exact callable handoff. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
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
      (saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCode
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hStack)

/-- Zero-divisor SDIV path through result-sign-fix, specialized from the
    sidecar bzero callable handoff and stopping before the saved-RA return. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_resultSignFix_named_post_from_handoff_spec_in_sdivCode
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
      (saveRaDivCallResultSignFixPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  exact
    saveRa_signs_abs_signXor_then_divCall_then_resultSignFix_named_post_of_callable_post_spec_in_sdivCode
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
