import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmAsm.Rv64.CodeReq in
theorem evm_mod_callable_code_v4_eq_ofProg (base : Word) :
    evm_mod_callable_code_v4 base = CodeReq.ofProg base evm_mod_callable_v4 := by
  unfold evm_mod_callable_code_v4 evm_mod_callable_v4 cc_ret_code
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
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_mod_epilogue 24).length) =
        base + zeroPathOff by rw [divK_modEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

private theorem callable_b0_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_mod_v4 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod_v4 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
      (evm_mod_callable_code_v4 b) a = some i := by
  unfold evm_mod_callable_code_v4; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

theorem evm_mod_callable_code_v4_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v4 base) a = some i := by
  intro a i h
  apply callable_b12_mod_v4
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4 {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop_v4 base) a = some i →
           (evm_mod_callable_code_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v4
    (CodeReq.union_split_mono callable_b1_mod_v4
    (CodeReq.union_split_mono callable_b2_mod_v4
    (CodeReq.union_split_mono callable_b3_mod_v4
    (CodeReq.union_split_mono callable_b4_mod_v4
    (CodeReq.union_split_mono callable_b5_mod_v4
    (CodeReq.union_split_mono callable_b6_mod_v4
    (CodeReq.union_split_mono callable_b7_mod_v4
    (CodeReq.union_split_mono callable_b8_mod_v4
    (CodeReq.union_split_mono callable_b9_mod_v4
    (CodeReq.union_split_mono callable_b11_mod_v4
    (CodeReq.union_split_mono callable_b13_mod_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

theorem evm_mod_callable_v4_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v4 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPostNoX1 sp a b).pcFree := by
    rw [modStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_mod_callable_code_v4) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v4_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

end EvmAsm.Evm64
