/-
  EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable

  Generic framed preserving-`x1` unsigned-DIV callable wrapper used by the
  SDIV div-call sidecar proofs.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallCallable

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- Frame the preserving-`x1` unsigned-DIV callable wrapper by an arbitrary
    PC-free assertion. SDIV uses this for the private sign frame carried across
    the exact callable handoff. -/
theorem evm_div_callable_preserving_x1_framed_spec_in_sdivCode
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base raVal : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : EvmAsm.Evm64.DivStackSpecCase (base + wrapperEndOff) a b)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCode base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_preserving_x1_spec_in_sdivCode
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

end EvmAsm.Evm64.SDiv.Compose
