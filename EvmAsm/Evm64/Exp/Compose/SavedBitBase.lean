/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBase

  Shared composition infrastructure for the corrected MSB-first saved-bit EXP
  layout.  This stays separate from `Compose/Base.lean` to keep the common
  composition foundation under the file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.Base

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

theorem exp_msb_bit_test_block_len :
    (EvmAsm.Evm64.exp_msb_bit_test_block).length = 3 := by
  exact EvmAsm.Evm64.exp_msb_bit_test_block_length

theorem exp_save_bit_block_len : (EvmAsm.Evm64.exp_save_bit_block).length = 1 := by
  exact EvmAsm.Evm64.exp_save_bit_block_length

theorem exp_cond_mul_call_with_saved_bit_skip_block_len
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      mulOff skipOff).length = 27 := by
  exact EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length
    mulOff skipOff

theorem exp_iter_body_full_msb_saved_bit_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      mulOff skipOff backOff).length = 59 := by
  exact EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_length
    mulOff skipOff backOff

theorem exp_iter_body_full_msb_saved_bit_two_mul_len
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 59 := by
  exact EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_length
    squaringMulOff condMulOff skipOff backOff

theorem evm_exp_msb_saved_bit_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff).length = 76 := by
  exact EvmAsm.Evm64.evm_exp_msb_saved_bit_length mulOff skipOff backOff

theorem evm_exp_msb_saved_bit_two_mul_len
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 76 := by
  exact EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_length
    squaringMulOff condMulOff skipOff backOff

/-- CodeReq decomposition for the corrected EXP square-and-multiply
    iteration: MSB bit-test, save bit, squaring call, saved-bit conditional
    multiply call, and trailing loop back-edge. -/
abbrev expIterBodyFullMsbSavedBitCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block,
    CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 16) mulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff,
    CodeReq.ofProg (base + 228) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
          mulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h12 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_msb_bit_test_block).length) = base + 12 := by
    rw [EvmAsm.Evm64.exp_msb_bit_test_block_length]
    rfl
  rw [h12]
  rw [CodeReq.ofProg_append]
  have h16 :
      (base + 12 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_save_bit_block).length) = base + 16 := by
    rw [EvmAsm.Evm64.exp_save_bit_block_length]
    bv_addr
  rw [h16]
  rw [CodeReq.ofProg_append]
  have h120 :
      (base + 16 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block mulOff).length) =
        base + 120 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h120]
  rw [CodeReq.ofProg_append]
  have h228 :
      (base + 120 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          mulOff skipOff).length) = base + 228 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h228]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 16) mulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 120) mulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block 0
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_msb_bit_test_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_save_bit_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 3
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_save_bit_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 16) mulOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 16)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff) 4
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_squaring_call_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 120)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff) 30
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len,
        exp_cond_mul_call_with_saved_bit_skip_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 228)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 57
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_loop_back_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (exp_squaring_call_block_code (base + 16) mulOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) := by
  exact ⟨expIterBodyFullMsbSavedBitCode_bit_test_sub,
    expIterBodyFullMsbSavedBitCode_save_bit_sub,
    expIterBodyFullMsbSavedBitCode_squaring_sub,
    expIterBodyFullMsbSavedBitCode_cond_mul_sub,
    expIterBodyFullMsbSavedBitCode_loop_back_sub⟩

/-- CodeReq decomposition for the corrected saved-bit iteration with separate
    MUL-call offsets at the squaring and conditional-multiply JAL sites. -/
abbrev expIterBodyFullMsbSavedBitTwoMulCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block,
    CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 16) squaringMulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) condMulOff skipOff,
    CodeReq.ofProg (base + 228) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitTwoMulCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h12 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_msb_bit_test_block).length) = base + 12 := by
    rw [EvmAsm.Evm64.exp_msb_bit_test_block_length]
    rfl
  rw [h12]
  rw [CodeReq.ofProg_append]
  have h16 :
      (base + 12 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_save_bit_block).length) = base + 16 := by
    rw [EvmAsm.Evm64.exp_save_bit_block_length]
    bv_addr
  rw [h16]
  rw [CodeReq.ofProg_append]
  have h120 :
      (base + 16 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff).length) =
        base + 120 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h120]
  rw [CodeReq.ofProg_append]
  have h228 :
      (base + 120 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          condMulOff skipOff).length) = base + 228 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h228]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 16) squaringMulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 120) condMulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitTwoMulCode_bit_test_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block 0
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_msb_bit_test_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_save_bit_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 3
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_save_bit_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_squaring_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 16) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 16)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff) 4
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_squaring_call_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 120)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      condMulOff skipOff) 30
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_cond_mul_call_with_saved_bit_skip_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 228)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 57
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_loop_back_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

/-- Top-level CodeReq decomposition for the corrected MSB-first saved-bit EXP
    opcode program. -/
abbrev evmExpMsbSavedBitCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_loop_pointer_advance,
    expIterBodyFullMsbSavedBitCode (base + 28) mulOff skipOff backOff,
    CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_loop_pointer_restore,
    CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue
  ]

theorem evmExpMsbSavedBitCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    evmExpMsbSavedBitCode base mulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff) := by
  unfold evmExpMsbSavedBitCode
  unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h24 :
      base + BitVec.ofNat 64 (4 * (EvmAsm.Evm64.exp_prologue).length) =
        base + 24 := by
    rw [EvmAsm.Evm64.exp_prologue_length]
    rfl
  rw [h24]
  rw [CodeReq.ofProg_append]
  have h28 :
      (base + 24 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_advance).length) = base + 28 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_advance_length]
    bv_addr
  rw [h28]
  rw [CodeReq.ofProg_append]
  have h264 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
          mulOff skipOff backOff).length) = base + 264 := by
    rw [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_length]
    bv_addr
  rw [h264]
  rw [CodeReq.ofProg_append]
  have h268 :
      (base + 264 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_restore).length) = base + 268 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_restore_length]
    bv_addr
  rw [h268]
  rw [← expIterBodyFullMsbSavedBitCode_eq_ofProg
    (base + 28) mulOff skipOff backOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

/-- Top-level CodeReq decomposition for the corrected saved-bit EXP opcode
    with independent MUL-call offsets at the two JAL sites. -/
abbrev evmExpMsbSavedBitTwoMulCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_loop_pointer_advance,
    expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff,
    CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_loop_pointer_restore,
    CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue
  ]

theorem evmExpMsbSavedBitTwoMulCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff) := by
  unfold evmExpMsbSavedBitTwoMulCode
  unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h24 :
      base + BitVec.ofNat 64 (4 * (EvmAsm.Evm64.exp_prologue).length) =
        base + 24 := by
    rw [EvmAsm.Evm64.exp_prologue_length]
    rfl
  rw [h24]
  rw [CodeReq.ofProg_append]
  have h28 :
      (base + 24 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_advance).length) = base + 28 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_advance_length]
    bv_addr
  rw [h28]
  rw [CodeReq.ofProg_append]
  have h264 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff).length) = base + 264 := by
    rw [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_length]
    bv_addr
  rw [h264]
  rw [CodeReq.ofProg_append]
  have h268 :
      (base + 264 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_pointer_restore).length) = base + 268 := by
    rw [EvmAsm.Evm64.exp_loop_pointer_restore_length]
    bv_addr
  rw [h268]
  rw [← expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg
    (base + 28) squaringMulOff condMulOff skipOff backOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

/-- CodeReq decomposition for the canonical two-MUL saved-bit EXP program.
    The branch offsets are fixed by `evm_exp_msb_saved_bit_two_mul_canonical`;
    the two external MUL call offsets remain caller supplied. -/
abbrev evmExpMsbSavedBitTwoMulCanonicalCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21) : CodeReq :=
  evmExpMsbSavedBitTwoMulCode base squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff

theorem evmExpMsbSavedBitTwoMulCanonicalCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) :
    evmExpMsbSavedBitTwoMulCanonicalCode base squaringMulOff condMulOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical
          squaringMulOff condMulOff) := by
  rw [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_canonical_eq]
  exact evmExpMsbSavedBitTwoMulCode_eq_ofProg base squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff

theorem evmExpMsbSavedBitTwoMulCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg,
    expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff) 7
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len,
        exp_iter_body_full_msb_saved_bit_two_mul_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_prologue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulCode_pointer_advance_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 6
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_loop_pointer_advance_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_pointer_restore_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 264)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 66
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_loop_pointer_restore_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_epilogue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 268)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 67
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len, exp_epilogue_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_two_mul_len]
      norm_num)

theorem evmExpMsbSavedBitTwoMulCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitTwoMulCode_prologue_sub,
    evmExpMsbSavedBitTwoMulCode_pointer_advance_sub,
    evmExpMsbSavedBitTwoMulCode_iter_body_sub,
    evmExpMsbSavedBitTwoMulCode_pointer_restore_sub,
    evmExpMsbSavedBitTwoMulCode_epilogue_sub⟩

theorem evmExpMsbSavedBitTwoMulCanonicalCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_iter_body_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_prologue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_prologue_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_pointer_advance_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_pointer_advance_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_pointer_restore_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_pointer_restore_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_epilogue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i :=
  evmExpMsbSavedBitTwoMulCode_epilogue_sub

theorem evmExpMsbSavedBitTwoMulCanonicalCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitTwoMulCanonicalCode_prologue_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_pointer_advance_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_iter_body_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_pointer_restore_sub,
    evmExpMsbSavedBitTwoMulCanonicalCode_epilogue_sub⟩

theorem evmExpMsbSavedBitCode_prologue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitCode_pointer_advance_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 6
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_loop_pointer_advance_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_iter_body_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullMsbSavedBitCode (base + 28)
      mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg,
    expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff) 7
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len,
        exp_iter_body_full_msb_saved_bit_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_pointer_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 264)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 66
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_loop_pointer_restore_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_epilogue_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  rw [evmExpMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 268)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 67
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [evm_exp_msb_saved_bit_len, exp_epilogue_len]
      omega)
    (by
      simp only [evm_exp_msb_saved_bit_len]
      norm_num)

theorem evmExpMsbSavedBitCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitCode (base + 28)
      mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨evmExpMsbSavedBitCode_prologue_sub,
    evmExpMsbSavedBitCode_pointer_advance_sub,
    evmExpMsbSavedBitCode_iter_body_sub,
    evmExpMsbSavedBitCode_pointer_restore_sub,
    evmExpMsbSavedBitCode_epilogue_sub⟩

end EvmAsm.Evm64.Exp.Compose
