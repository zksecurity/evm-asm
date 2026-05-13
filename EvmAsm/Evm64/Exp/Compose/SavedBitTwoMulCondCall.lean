/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCondCall

  Conditional-multiply call adapters for the two-MUL-offset saved-bit EXP
  composition.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkip

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Taken conditional-multiply block followed by the loop-back counter update
    under the two-MUL-offset saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    let rest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
       (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word)))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest))] := by
  intro rw rest
  have hCond :=
    exp_cond_mul_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hbase hmt hd
  have hCondFramed :=
    cpsTripleWithin_frameR
      ((.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hCond
  have hcondExit : ((base + 152 : Word) + 104) = base + 256 := by bv_omega
  rw [hcondExit] at hCondFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base mulTarget
    loopTarget hback
  have hLoopFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hLoop
  have hSeq :
      cpsBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ loopTarget _ (base + 264) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed hLoopFramed
  have hSeqN := cpsBranchWithin_as_cpsNBranchWithin hSeq
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeqN

/-- Variant of the conditional-multiply path that consumes owned caller-saved
    call scratch in the precondition. The data words stay in the concrete
    limb form expected by the base theorem; only the overwritten registers and
    memory cells are existentially owned. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_call_scratch_owned_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3
      e0 e1 e2 e3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    let rest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (preCore **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest))] := by
  intro rw rest preCore
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x6)
    (P := preCore ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v6
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x7)
    (P := preCore ** (.x6 ↦ᵣ v6) ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v7
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x10)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v10
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x11)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v11
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      memOwn (evmSp + 8) ** memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d0
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 8)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d1
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 16)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d2
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 24)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** ((evmSp + 16) ↦ₘ d2))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d3
  have hConcrete :=
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base loopTarget hbase hmt hd hback
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [preCore] at hp ⊢
      have hSp0 : (sp + signExtend12 0#12 : Word) = sp := by
        unfold signExtend12; bv_decide
      have hSp8 : (sp + signExtend12 8#12 : Word) = sp + 8 := by
        unfold signExtend12; bv_decide
      have hSp16 : (sp + signExtend12 16#12 : Word) = sp + 16 := by
        unfold signExtend12; bv_decide
      have hSp24 : (sp + signExtend12 24#12 : Word) = sp + 24 := by
        unfold signExtend12; bv_decide
      have hEvm0 : (evmSp + signExtend12 0#12 : Word) = evmSp := by
        unfold signExtend12; bv_decide
      have hEvm8 : (evmSp + signExtend12 8#12 : Word) = evmSp + 8#64 := by
        unfold signExtend12; bv_decide
      have hEvm16 : (evmSp + signExtend12 16#12 : Word) = evmSp + 16#64 := by
        unfold signExtend12; bv_decide
      have hEvm24 : (evmSp + signExtend12 24#12 : Word) = evmSp + 24#64 := by
        unfold signExtend12; bv_decide
      have hEvm32 : (evmSp + signExtend12 32#12 : Word) = evmSp + 32 := by
        unfold signExtend12; bv_decide
      have hEvm40 : (evmSp + signExtend12 40#12 : Word) = evmSp + 40 := by
        unfold signExtend12; bv_decide
      have hEvm48 : (evmSp + signExtend12 48#12 : Word) = evmSp + 48 := by
        unfold signExtend12; bv_decide
      have hEvm56 : (evmSp + signExtend12 56#12 : Word) = evmSp + 56 := by
        unfold signExtend12; bv_decide
      rw [hSp0, hSp8, hSp16, hSp24, hEvm32, hEvm40, hEvm48, hEvm56] at hp ⊢
      rw [hEvm0, hEvm8, hEvm16, hEvm24]
      xperm_hyp hp)
    hConcrete

/-- Assertion-level bridge from the folded-word precondition produced by the
    two-MUL saved-bit prefix to the concrete-limb precondition consumed by the
    conditional-multiply adapter. Keeping this as a pure assertion implication
    avoids comparing the full generated CPS theorem type while still isolating
    the `evmWordIs` unfolding and address normalization needed by the next
    composition slice. -/
theorem exp_cond_mul_folded_pre_to_call_scratch_owned_pre
    (sp evmSp iterCount vOld a0 a1 a2 a3 : Word) (r : EvmWord) :
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let foldedPre : Assertion :=
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
        evmWordIs sp r ** evmWordIs (evmSp + 32) r **
        baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
        (.x0 ↦ᵣ (0 : Word))) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    let concretePre : Assertion :=
      let preCore : Assertion :=
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r.getLimbN 0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r.getLimbN 1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r.getLimbN 2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r.getLimbN 3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r.getLimbN 0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r.getLimbN 1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r.getLimbN 2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r.getLimbN 3) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
      preCore **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24)
    ∀ h, foldedPre h → concretePre h := by
  intro baseFrame foldedPre concretePre h hp
  dsimp [foldedPre, concretePre, baseFrame] at hp ⊢
  unfold evmWordIs at hp
  have hSrc8 : (evmSp + 32#64 + 8 : Word) = evmSp + 40#64 := by bv_omega
  have hSrc16 : (evmSp + 32#64 + 16 : Word) = evmSp + 48#64 := by bv_omega
  have hSrc24 : (evmSp + 32#64 + 24 : Word) = evmSp + 56#64 := by bv_omega
  rw [hSrc8, hSrc16, hSrc24] at hp
  have hSp0 : (sp + signExtend12 0#12 : Word) = sp := by
    unfold signExtend12; bv_decide
  have hSp8 : (sp + signExtend12 8#12 : Word) = sp + 8 := by
    unfold signExtend12; bv_decide
  have hSp16 : (sp + signExtend12 16#12 : Word) = sp + 16 := by
    unfold signExtend12; bv_decide
  have hSp24 : (sp + signExtend12 24#12 : Word) = sp + 24 := by
    unfold signExtend12; bv_decide
  have hEvm32 : (evmSp + signExtend12 32#12 : Word) = evmSp + 32#64 := by
    unfold signExtend12; bv_decide
  have hEvm40 : (evmSp + signExtend12 40#12 : Word) = evmSp + 40#64 := by
    unfold signExtend12; bv_decide
  have hEvm48 : (evmSp + signExtend12 48#12 : Word) = evmSp + 48#64 := by
    unfold signExtend12; bv_decide
  have hEvm56 : (evmSp + signExtend12 56#12 : Word) = evmSp + 56#64 := by
    unfold signExtend12; bv_decide
  rw [hSp0, hSp8, hSp16, hSp24, hEvm32, hEvm40, hEvm48, hEvm56]
  xperm_hyp hp

/-- Folded-word variant of the two-MUL conditional-multiply path adapter.
    The precondition consumes the current result from `sp` and the second
    multiplicand from `evmSp + 32` as `evmWordIs`, then delegates to the
    concrete-limb owned-scratch adapter via
    `exp_cond_mul_folded_pre_to_call_scratch_owned_pre`. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_folded_owned_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget : Word) (r : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let rest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let foldedPre : Assertion :=
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
        evmWordIs sp r ** evmWordIs (evmSp + 32) r **
        baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
        (.x0 ↦ᵣ (0 : Word))) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      foldedPre
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest))] := by
  intro rw baseFrame rest foldedPre
  let concretePre : Assertion :=
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
      (.x0 ↦ᵣ (0 : Word))
    preCore **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24)
  have hConcrete :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        concretePre
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)),
          (base + 264,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest))] := by
    dsimp [concretePre, baseFrame, rest]
    simpa [expTwoMulCondRwFromLimbs, expTwoMulIterW,
      expResultWord_getLimbN_self r] using
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_call_scratch_owned_spec_within
      iterCount sp evmSp (r.getLimbN 3) vOld
      (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
      a0 a1 a2 a3
      (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
      mulTarget squaringMulOff condMulOff skipOff backOff
      base loopTarget hbase hmt hd hback
  refine cpsNBranchWithin_weaken_pre ?_ hConcrete
  intro h hp
  dsimp [foldedPre] at hp
  simpa [concretePre, baseFrame] using
    exp_cond_mul_folded_pre_to_call_scratch_owned_pre
      sp evmSp iterCount vOld a0 a1 a2 a3 r h hp


end EvmAsm.Evm64.Exp.Compose
