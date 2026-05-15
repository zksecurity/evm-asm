/-
  EvmAsm.Evm64.Exp.Compose.TopIterSubs

  Iteration sub-block inclusion lemmas for the top-level EXP code bundles.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBase
import EvmAsm.Evm64.Exp.Compose.EvmExpCode

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTopIterSquaringAddr (base : Word) :
    (base + 40 : Word) = base + 28 + 12 := by
  bv_omega

theorem expTopIterCondMulAddr (base : Word) :
    (base + 144 : Word) = base + 28 + 116 := by
  bv_omega

theorem expTopIterSavedBitSquaringAddr (base : Word) :
    (base + 44 : Word) = base + 28 + 16 := by
  bv_omega

theorem expTopIterSavedBitCondMulAddr (base : Word) :
    (base + 148 : Word) = base + 28 + 120 := by
  bv_omega

theorem expTopIterSavedBitLoopBackAddr (base : Word) :
    (base + 256 : Word) = base + 28 + 228 := by
  bv_omega

theorem expTopIterLoopBackAddr (base : Word) :
    (base + 252 : Word) = base + 28 + 224 := by
  bv_omega

/-- Bit-test sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_bit_test_sub a i h)

/-- Squaring-call sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 40) mulOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSquaringAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_squaring_sub a i h)

/-- Conditional-multiply sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 144) mulOff skipOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterCondMulAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_cond_mul_sub a i h)

/-- MSB bit-test sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_bit_test_sub a i h)

/-- Save-bit sub-block directly included in the corrected saved-bit top-level
    EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_save_bit_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_save_bit_sub a i h)

/-- Squaring-call sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 44) mulOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSavedBitSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_squaring_sub a i h)

/-- Saved-bit conditional-multiply sub-block directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 148) mulOff skipOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSavedBitCondMulAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_cond_mul_sub a i h)

/-- Saved-bit loop-back sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_loop_back_sub a i h)

theorem evmExpMsbSavedBitTwoMulCode_iter_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitTwoMulCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitTwoMulCode_loop_back_sub a i h)

/-- Saved-bit conditional-multiply BEQ skip-gate directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_cond_mul_beq_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.singleton (base + 148) (.BEQ .x18 .x0 skipOff))
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
      (base + 148) mulOff skipOff a i h)

/-- Loop-back sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 252)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [expTopIterLoopBackAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_loop_back_sub a i h)

end EvmAsm.Evm64.Exp.Compose
