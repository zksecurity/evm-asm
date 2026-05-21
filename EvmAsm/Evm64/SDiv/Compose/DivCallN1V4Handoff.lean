/-
  EvmAsm.Evm64.SDiv.Compose.DivCallN1V4Handoff

  N1/v4-shaped exact handoff wrappers for the SDIV div-call path.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoff

namespace EvmAsm.Evm64.SDiv.Compose

/-- Exact SDIV div-call handoff specialized to the v4 scratch frame shape
    produced by the N1 call/max/max/max no-NOP DIV path. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4Scratch_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem scratchOut : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) := by
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_frame_transform_spec_in_sdivCodeV4
      (FPre := ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (FPost := ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 (EvmAsm.Rv64.signExtend12 4095 : Word)
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      hbase hStack

end EvmAsm.Evm64.SDiv.Compose
