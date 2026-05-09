/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

  Small top-level EXP code-bundle specs split out of `Compose/Base.lean` to
  keep the base composition module under the Compose file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.Base

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

end EvmAsm.Evm64.Exp.Compose
