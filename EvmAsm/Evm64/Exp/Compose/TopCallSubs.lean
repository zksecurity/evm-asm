/-
  EvmAsm.Evm64.Exp.Compose.TopCallSubs

  Squaring and conditional-multiply call sub-block inclusion lemmas for the
  top-level EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.TopLoopControl

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

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

end EvmAsm.Evm64.Exp.Compose
