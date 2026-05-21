import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmAsm.Rv64.CodeReq in
theorem evm_div_callable_code_v4_eq_ofProg (base : Word) :
    evm_div_callable_code_v4 base = CodeReq.ofProg base evm_div_callable_v4 := by
  unfold evm_div_callable_code_v4 evm_div_callable_v4 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_div_epilogue 24).length) =
        base + zeroPathOff by rw [divK_divEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

private theorem callable_b0_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_div_v4 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_div_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
      (evm_div_callable_code_v4 b) a = some i := by
  unfold evm_div_callable_code_v4; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

theorem evm_div_callable_code_v4_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_div_callable_code_v4 base) a = some i := by
  intro a i h
  apply callable_b12_div_v4
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem sharedDivModCodeNoNop_v4_sub_div_callable_code_v4 {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop_v4 base) a = some i →
           (evm_div_callable_code_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_div_v4
    (CodeReq.union_split_mono callable_b1_div_v4
    (CodeReq.union_split_mono callable_b2_div_v4
    (CodeReq.union_split_mono callable_b3_div_v4
    (CodeReq.union_split_mono callable_b4_div_v4
    (CodeReq.union_split_mono callable_b5_div_v4
    (CodeReq.union_split_mono callable_b6_div_v4
    (CodeReq.union_split_mono callable_b7_div_v4
    (CodeReq.union_split_mono callable_b8_div_v4
    (CodeReq.union_split_mono callable_b9_div_v4
    (CodeReq.union_split_mono callable_b11_div_v4
    (CodeReq.union_split_mono callable_b13_div_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

theorem evm_div_callable_v4_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPost sp a b).pcFree := by
    rw [divStackDispatchPost_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_div_callable_code_v4) hStack
  have hStackFramed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPost sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackFramed hRetFramed

theorem evm_div_callable_v4_spec_from_noNop_framed
    {F : Assertion} [Assertion.PCFree F] (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      ((divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal)) ** F)
      ((divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_spec_from_noNop
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

theorem evm_div_callable_v4_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_div_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v4_spec_from_noNop_preserving_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_spec_from_noNop_preserving_x1
        sp base raVal a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

/-- Generic concrete callable DIV wrapper for v4 no-NOP body proofs that
    preserve exact caller-framed `x1`/`x9` and expose the concrete scratch and
    register values needed by SDIV branch handoffs. -/
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

/-- Generic v4 callable DIV wrapper for no-NOP body proofs that already use
    the callable-ready precondition and preserve exact caller-framed `x1`/`x9`. -/
theorem evm_div_callable_v4_spec_from_noNop_preserving_x1_x9
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
        ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_div_callable_code_v4) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val))
      (by
        rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

theorem evm_div_callable_v4_spec_from_noNop_preserving_x1_x9_framed
    {F : Assertion} [Assertion.PCFree F]
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
        ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
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
      (evm_div_callable_v4_spec_from_noNop_preserving_x1_x9
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

theorem evm_div_callable_v4_spec_from_noNop_branch_return_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_div_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) branch.returnX1)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v4_spec_from_noNop_branch_return_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_spec_from_noNop_branch_return_x1
        sp base a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

end EvmAsm.Evm64
