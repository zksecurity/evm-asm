/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond

  Two-MUL-offset saved-bit EXP conditional-multiply path composition.
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
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    let rw := r * aw
    let iterCountNew := iterCount + signExtend12 ((-1 : BitVec 12))
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
          (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew ≠ 0⌝) ** rest)),
        (base + 264,
          (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew = 0⌝) ** rest))] := by
  intro r aw rw iterCountNew rest
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
        dsimp [rest, r, aw, rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed hLoopFramed
  have hSeqN := cpsBranchWithin_as_cpsNBranchWithin hSeq
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeqN

end EvmAsm.Evm64.Exp.Compose
