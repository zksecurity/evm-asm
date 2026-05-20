import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Legacy LP64-callable DIV wrapper pinned to the original one-correction
    `divK_div128` subroutine. This gives existing v1 no-NOP specs a stable
    target when the default callable name migrates to v4. -/
def evm_div_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

/-- Legacy LP64-callable MOD wrapper pinned to the original one-correction
    `divK_div128` subroutine. -/
def evm_mod_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

/-- Legacy v1 CodeReq layout for `evm_div_callable_v1`. -/
abbrev evm_div_callable_code_v1 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

/-- Legacy v1 CodeReq layout for `evm_mod_callable_v1`. -/
abbrev evm_mod_callable_code_v1 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

theorem evm_div_callable_v1_eq_current :
    evm_div_callable_v1 = evm_div_callable := by
  rfl

theorem evm_mod_callable_v1_eq_current :
    evm_mod_callable_v1 = evm_mod_callable := by
  rfl

theorem evm_div_callable_code_v1_eq_current (base : Word) :
    evm_div_callable_code_v1 base = evm_div_callable_code base := by
  rfl

theorem evm_mod_callable_code_v1_eq_current (base : Word) :
    evm_mod_callable_code_v1 base = evm_mod_callable_code base := by
  rfl

theorem divCode_noNop_sub_div_callable_code_v1 {base : Word} :
    ∀ a i, (divCode_noNop base) a = some i →
           (evm_div_callable_code_v1 base) a = some i := by
  simpa [evm_div_callable_code_v1_eq_current]
    using divCode_noNop_sub_div_callable_code (base := base)

theorem modCode_noNop_sub_mod_callable_code_v1 {base : Word} :
    ∀ a i, (modCode_noNop base) a = some i →
           (evm_mod_callable_code_v1 base) a = some i := by
  simpa [evm_mod_callable_code_v1_eq_current]
    using modCode_noNop_sub_mod_callable_code (base := base)

theorem evm_div_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_div_callable_code_v1 base) a = some i := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_code_ret_sub (base := base)

theorem evm_mod_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v1 base) a = some i := by
  simpa [evm_mod_callable_code_v1_eq_current]
    using evm_mod_callable_code_ret_sub (base := base)

theorem evm_div_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_spec_from_noNop
      sp base raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

theorem evm_div_callable_v1_spec_from_branch_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_spec_from_branch_noNop
      sp base raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch

theorem evm_div_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_spec_from_noNop_preserving_x1
      sp base raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_spec_from_noNop_branch_return_x1
      sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) ** F) := by
  simpa [evm_div_callable_code_v1_eq_current]
    using evm_div_callable_spec_from_noNop_branch_return_x1_framed
      (F := F) sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

theorem evm_mod_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  simpa [evm_mod_callable_code_v1_eq_current]
    using evm_mod_callable_spec_from_noNop_preserving_x1
      sp base raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

theorem evm_mod_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (modStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  simpa [evm_mod_callable_code_v1_eq_current]
    using evm_mod_callable_spec_from_noNop
      sp base raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack

end EvmAsm.Evm64
