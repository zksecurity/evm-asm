/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactCallable

  Exact-`x1` unsigned-DIV callable wrappers used by the SDIV div-call
  postcondition sidecar proofs.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFreeBasics

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

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

end EvmAsm.Evm64.SDiv.Compose
