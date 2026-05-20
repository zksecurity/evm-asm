/-
  EvmAsm.Evm64.DivMod.CallableBzeroV4

  Split v4 zero-divisor callable wrappers for DIV.
-/

import EvmAsm.Evm64.DivMod.CallableV4Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 generic concrete callable DIV wrapper for no-NOP body proofs that
    preserve exact caller-framed `x1`/`x9`. -/
theorem evm_div_callable_v4_spec_from_noNop_concrete_preserving_x1_x9
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  let retFrame : Assertion :=
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_div_callable_code_v4) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (retFrame ** (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [divConcretePostNoX1Frame_unfold] at hp
      dsimp [retFrame] at hp ⊢
      xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL retFrame
      (by
        dsimp [retFrame]
        rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
    rw [divConcretePostNoX1Frame_unfold]
    dsimp [retFrame] at hp ⊢
    xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

/-- v4 zero-divisor DIV callable wrapper in the concrete post shape used by
    SDIV branch handoffs before weakening to the public callable postcondition. -/
theorem evm_div_callable_bzero_v4_concrete_preserving_x1_spec
    (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact
    evm_div_callable_v4_spec_from_noNop_concrete_preserving_x1_x9
      sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (evm_div_bzero_stack_spec_within_dispatch_noNop_v4_concrete_callable_uni
        sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

/-- v4 zero-divisor DIV callable wrapper that preserves exact `x1` for return
    and exact `x9` as caller-framed state. -/
theorem evm_div_callable_bzero_v4_preserving_x1_spec (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (divConcretePostNoX1_weaken_callable_frame sp a b)
    (evm_div_callable_bzero_v4_concrete_preserving_x1_spec
      sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

/-- Framed variant of `evm_div_callable_bzero_v4_preserving_x1_spec`. -/
theorem evm_div_callable_bzero_v4_preserving_x1_framed_spec
    {F : Assertion} [Assertion.PCFree F] (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_bzero_v4_preserving_x1_spec
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

end EvmAsm.Evm64
