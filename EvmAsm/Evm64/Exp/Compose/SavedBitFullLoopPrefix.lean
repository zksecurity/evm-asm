/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopPrefix

  Full-loop code-bundle helpers for the corrected MSB-first saved-bit EXP
  layout.  These mirror the `FullLoop.lean` EXP+MUL lifts, but target
  `evmExpMsbSavedBitCode` so the single-iteration composition can keep the
  tested bit live in `x18` across the unconditional squaring call.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- MSB bit-test block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_msb_bit_test_evm_exp_msb_saved_bit_spec_within
      e c v10 mulOff skipOff backOff base)

/-- MSB bit-test block lifted to the two-MUL-offset saved-bit EXP+MUL bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) := by
  have h := EvmAsm.Evm64.exp_msb_bit_test_block_spec_within e c v10 (base + 28)
  rw [expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i hi =>
      evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_bit_test_sub a i hi)))

/-- Save-bit block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (bit v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_save_bit_evm_exp_msb_saved_bit_spec_within
      bit v18 mulOff skipOff backOff base)

/-- Save-bit block lifted to the two-MUL-offset saved-bit EXP+MUL bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (bit v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_save_bit_block_spec_within bit v18 (base + 40)
  rw [expTopSavedBitSaveNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i hi => by
      have hentry : (base + 40 : Word) = (base + 28) + 12 := by bv_omega
      rw [hentry] at hi
      exact evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_save_bit_sub a i hi)))

/-- Prefix of one corrected EXP iteration: extract the current MSB into `x10`
    and save the same bit in callee-saved `x18` before the squaring call. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit := exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    e c v10 mulOff skipOff backOff base mulTarget
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave := exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    bit v18 mulOff skipOff backOff base mulTarget
  have hSaveFramed :=
    cpsTripleWithin_frameL
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))))
      (by pcFree) hSave
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Two-MUL-offset prefix of one corrected EXP iteration: extract the current
    MSB into `x10` and save the same bit in `x18` before the squaring call. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit := exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 squaringMulOff condMulOff skipOff backOff base mulTarget
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave := exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    bit v18 squaringMulOff condMulOff skipOff backOff base mulTarget
  have hSaveFramed :=
    cpsTripleWithin_frameL
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))))
      (by pcFree) hSave
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the corrected
    saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base mulTarget target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_spec_within
      mulOff skipOff backOff v18 base target htarget)

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the two-MUL-offset
    saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base mulTarget target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x18 .x0 skipOff v18 (0 : Word)
    (base + 148)
  rw [htarget] at h
  rw [expTopSavedBitCondMulBeqNextPc] at h
  exact cpsBranchWithin_extend_code
    (h := h)
    (hmono := fun a i hi => by
      have hentry : (base + 148 : Word) = (base + 28) + 120 := by bv_omega
      rw [hentry] at hi
      exact evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub a i
            (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
              ((base + 28) + 120) condMulOff skipOff a i hi))))

/-- Saved-bit loop-back block lifted directly to the corrected EXP+MUL code
    bundle. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 256) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 256)
    target htarget
  rw [expTopSavedBitLoopBackNextPc] at h
  simpa [expIterCountNew] using
    (cpsBranchWithin_extend_code (h := h)
      (hmono := fun a i hi =>
        evmExpMsbSavedBitWithMulCode_exp_sub a i
          (evmExpMsbSavedBitCode_iter_loop_back_sub a i hi)))

end EvmAsm.Evm64.Exp.Compose
