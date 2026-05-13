/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoff

  Exact-`x1` callable handoff from the SDIV div-call dispatch-ready bundle.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Generic exact-`x1` callable handoff from the SDIV dispatch-ready bundle.
    The branch-specific obligation is the `divCode_noNop` proof `hStack`,
    whose precondition already carries SDIV's exact return address in `x1`. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCode
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
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
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  have hCallableFramed :=
    evm_div_callable_preserving_x1_exact_pre_framed_spec_in_sdivCode
      (F := saveRaDivCallSignFrame vRa resultSign divisorSign)
      sp base ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact hStack)
  have hCallableExit :
      cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCode base)
        (EvmAsm.Evm64.divModStackDispatchPre sp dividendAbsWord divisorAbsWord
          ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          saveRaDivCallSignFrame vRa resultSign divisorSign)
        ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          saveRaDivCallSignFrame vRa resultSign divisorSign) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  exact cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallBzeroCallablePost_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      saveRaDivCallSignFrame, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

end EvmAsm.Evm64.SDiv.Compose
