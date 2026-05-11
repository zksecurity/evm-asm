/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

  Small top-level EXP code-bundle specs split out of `Compose/Base.lean` to
  keep the base composition module under the Compose file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Pointer advance lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_advance_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_advance_spec_within vOld (base + 24)
  have hnext : ((base + 24 : Word) + 4) = base + 28 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_advance_sub)

/-- Pointer restore lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 260) (base + 264)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_restore_spec_within vOld (base + 260)
  have hnext : ((base + 260 : Word) + 4) = base + 264 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_restore_sub)

/-- EXP prologue lifted to the top-level EXP code bundle. -/
theorem exp_prologue_evm_exp_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) := by
  have h := EvmAsm.Evm64.exp_prologue_word_spec_within
    sp cOld tOld m0 m1 m2 m3 base
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_prologue_sub)

/-- EXP epilogue lifted to the top-level EXP code bundle. -/
theorem exp_epilogue_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 264) (base + 300)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := EvmAsm.Evm64.exp_epilogue_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 264)
  have hnext : ((base + 264 : Word) + 36) = base + 300 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_epilogue_sub)

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
  have haddr : (base + 40 : Word) = base + 28 + 12 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_squaring_sub a i h)

/-- Conditional-multiply sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 144) mulOff skipOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 144 : Word) = base + 28 + 116 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_cond_mul_sub a i h)

/-- Loop-back sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 252)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 252 : Word) = base + 28 + 224 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_loop_back_sub a i h)

/-- Bit-test block lifted to the top-level EXP code bundle. -/
theorem exp_bit_test_evm_exp_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_bit_test_block_spec_within e c v10 (base + 28)
  have hnext : ((base + 28 : Word) + 12) = base + 40 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_bit_test_sub)

/-- Loop-back block lifted to the top-level EXP code bundle. -/
theorem exp_loop_back_evm_exp_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    let cNew := c + signExtend12 ((-1 : BitVec 12))
    cpsBranchWithin 2 (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew ≠ 0⌝)
      (base + 260) ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 252) target htarget
  have hnext : ((base + 252 : Word) + 8) = base + 260 := by bv_omega
  rw [hnext] at h
  exact cpsBranchWithin_extend_code (h := h) (hmono := evmExpCode_iter_loop_back_sub)

/-- Squaring-call factor-1 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_squaring_marshal_factor1_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_loop_marshal_factor1) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_marshal_factor1_sub a i h)

/-- Squaring-call factor-2 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_squaring_marshal_result_to_factor2_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 72)
      EvmAsm.Evm64.exp_loop_marshal_result_to_factor2) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 72 : Word) = base + 40 + 32 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_marshal_result_to_factor2_sub a i h)

/-- Squaring-call JAL sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_squaring_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 104)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 104 : Word) = base + 40 + 64 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_square_sub a i h)

/-- Squaring-call unmarshal sub-block directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_squaring_un_marshal_and_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 108)
      EvmAsm.Evm64.exp_loop_un_marshal_and_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 108 : Word) = base + 40 + 68 := by bv_omega
  rw [haddr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_un_marshal_and_restore_sub a i h)

/-- Conditional-multiply factor-1 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_cond_mul_marshal_factor1_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 148) EvmAsm.Evm64.exp_loop_marshal_factor1) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have hcall := exp_cond_mul_call_block_code_marshal_factor1_sub
    (base + 148) mulOff a i h
  have hskip : (base + 148 : Word) = base + 144 + 4 := by bv_omega
  rw [hskip] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply factor-2 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_cond_mul_marshal_a_to_factor2_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 180)
      EvmAsm.Evm64.exp_loop_marshal_a_to_factor2) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 180 : Word) = base + 148 + 32 := by bv_omega
  rw [haddr] at h
  have hcall := exp_cond_mul_call_block_code_marshal_a_to_factor2_sub
    (base + 148) mulOff a i h
  have hskip : (base + 148 : Word) = base + 144 + 4 := by bv_omega
  rw [hskip] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply JAL sub-block directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_cond_mul_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 212)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 212 : Word) = base + 148 + 64 := by bv_omega
  rw [haddr] at h
  have hcall := exp_cond_mul_call_block_code_square_sub (base + 148) mulOff a i h
  have hskip : (base + 148 : Word) = base + 144 + 4 := by bv_omega
  rw [hskip] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply unmarshal sub-block directly included in the top-level
    EXP code bundle. -/
theorem evmExpCode_cond_mul_un_marshal_and_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 216)
      EvmAsm.Evm64.exp_loop_un_marshal_and_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have haddr : (base + 216 : Word) = base + 148 + 68 := by bv_omega
  rw [haddr] at h
  have hcall := exp_cond_mul_call_block_code_un_marshal_and_restore_sub
    (base + 148) mulOff a i h
  have hskip : (base + 148 : Word) = base + 144 + 4 := by bv_omega
  rw [hskip] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply BEQ skip gate directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_cond_mul_beq_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.singleton (base + 144) (.BEQ .x10 .x0 skipOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_beq_sub
      (base + 144) mulOff skipOff a i h)

/-- Squaring-call JAL spec lifted to the top-level EXP code bundle. -/
theorem exp_squaring_square_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 104) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 108)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 104)
  rw [hmul] at h
  have hret : ((base + 104 : Word) + 4) = base + 108 := by bv_omega
  rw [hret] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_squaring_square_sub)

/-- Conditional-multiply JAL spec lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_square_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 212) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 216)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 212)
  rw [hmul] at h
  have hret : ((base + 212 : Word) + 4) = base + 216 := by bv_omega
  rw [hret] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_cond_mul_square_sub)

/-- Squaring-call marshal prefix and JAL lifted to the top-level EXP code bundle. -/
theorem exp_squaring_marshal_pair_then_square_evm_exp_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 17 (base + 40) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) **
       (.x1 ↦ᵣ (base + 108))) := by
  have h := EvmAsm.Evm64.exp_loop_squaring_marshal_pair_then_square_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff (base + 40)
  have htarget : (((base + 40) + 64 : Word) + signExtend21 mulOff) = mulTarget := by
    rw [show ((base + 40 : Word) + 64) = base + 104 by bv_omega]
    exact hmul
  rw [htarget] at h
  have hret : ((base + 40 : Word) + 68) = base + 108 := by bv_omega
  rw [hret] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_squaring_sub)

/-- Squaring-call unmarshal word spec lifted to the top-level EXP code bundle. -/
theorem exp_squaring_un_marshal_word_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 : Word) (w : EvmWord)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) w)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  have h := EvmAsm.Evm64.exp_loop_un_marshal_and_restore_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 (base + 108) w
  have hnext : ((base + 108 : Word) + 36) = base + 144 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_squaring_un_marshal_and_restore_sub)

/-- Conditional-multiply marshal pair lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_marshal_pair_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 16 (base + 148) (base + 212)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  have h := EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_spec_within
    sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 (base + 148)
  have hnext : ((base + 148 : Word) + 64) = base + 212 := by bv_omega
  rw [hnext] at h
  have hmono :
      ∀ addr instr, EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code
          (base + 148) addr = some instr →
        (evmExpCode base mulOff skipOff backOff) addr = some instr := by
    intro addr instr hcode
    unfold EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code at hcode
    exact CodeReq.union_sub
      (evmExpCode_cond_mul_marshal_factor1_sub (base := base)
        (mulOff := mulOff) (skipOff := skipOff) (backOff := backOff))
      (fun a i hfactor2 => by
        have haddr : ((base + 148 : Word) + 32) = base + 180 := by bv_omega
        rw [haddr] at hfactor2
        exact evmExpCode_cond_mul_marshal_a_to_factor2_sub
          (base := base) (mulOff := mulOff) (skipOff := skipOff)
          (backOff := backOff) a i hfactor2)
      addr instr hcode
  exact cpsTripleWithin_extend_code (h := h) (hmono := hmono)

/-- Conditional-multiply marshal prefix and JAL lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_marshal_pair_then_square_evm_exp_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 17 (base + 148) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x1 ↦ᵣ (base + 216))) := by
  have hpair := exp_cond_mul_marshal_pair_evm_exp_spec_within
    sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    mulOff skipOff backOff base
  have hpairFramed := cpsTripleWithin_frameR (.x1 ↦ᵣ vOld) (by pcFree) hpair
  have hjal := exp_cond_mul_square_evm_exp_spec_within
    mulOff skipOff backOff vOld base mulTarget hmul
  have hjalFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      (by pcFree) hjal
  have hseq : cpsTripleWithin (16 + 1) (base + 148) mulTarget
      (evmExpCode base mulOff skipOff backOff) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hpairFramed hjalFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

/-- Conditional-multiply unmarshal word spec lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_un_marshal_word_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 : Word) (w : EvmWord)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 216) (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) w)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  have h := EvmAsm.Evm64.exp_loop_un_marshal_and_restore_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 (base + 216) w
  have hnext : ((base + 216 : Word) + 36) = base + 252 := by bv_omega
  rw [hnext] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_un_marshal_and_restore_sub)

/-- Conditional-multiply skip gate and call prefix lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_call_with_skip_evm_exp_spec_within
    (sp evmSp tOld vOld v10 r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base skipTarget mulTarget : Word)
    (hskip : ((base + 144) + signExtend13 skipOff : Word) = skipTarget)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    let callPre :=
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld))
    let callPost :=
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x1 ↦ᵣ (base + 216)))
    cpsBranchWithin 18 (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      (callPre ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)))
      skipTarget (callPre ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝)
      mulTarget (callPost ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) := by
  dsimp only
  let callPre :=
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld))
  let callPost :=
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x1 ↦ᵣ (base + 216)))
  have hbeq := beq_spec_within .x10 .x0 skipOff v10 (0 : Word) (base + 144)
  rw [hskip] at hbeq
  have hnext : ((base + 144 : Word) + 4) = base + 148 := by bv_omega
  rw [hnext] at hbeq
  have hbeqFramed := cpsBranchWithin_frameR callPre (by pcFree) hbeq
  have hbeqExt : cpsBranchWithin 1 (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))) ** callPre)
      skipTarget (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝) ** callPre)
      (base + 148) (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) ** callPre) :=
    cpsBranchWithin_extend_code (h := hbeqFramed) (hmono := by
      intro a i hcode
      exact evmExpCode_cond_mul_beq_sub
        (base := base) (mulOff := mulOff) (skipOff := skipOff)
        (backOff := backOff) a i hcode)
  have hcall := exp_cond_mul_marshal_pair_then_square_evm_exp_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    mulOff skipOff backOff base mulTarget hmul
  change cpsTripleWithin 17 (base + 148) mulTarget
      (evmExpCode base mulOff skipOff backOff) callPre callPost at hcall
  have hcallFramed :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝)
      (by pcFree) hcall
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := hbeqExt)
    (hperm := fun _ hp => by xperm_hyp hp)
    (h2 := hcallFramed)
    (ht1 := fun _ hp => hp)
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64.Exp.Compose
