/-
  EvmAsm.Evm64.Exp.Compose.TopLoopControl

  Loop-control block specs lifted to the top-level EXP code bundles.
-/

import EvmAsm.Evm64.Exp.Compose.TopIterSubs

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

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
  rw [expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_bit_test_sub)

/-- MSB bit-test block lifted to the corrected saved-bit top-level EXP code
    bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) := by
  have h := EvmAsm.Evm64.exp_msb_bit_test_block_spec_within e c v10 (base + 28)
  rw [expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_iter_bit_test_sub)

/-- Save-bit block lifted to the corrected saved-bit top-level EXP code
    bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_spec_within
    (bit v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_save_bit_block_spec_within bit v18 (base + 40)
  rw [expTopSavedBitSaveNextPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_iter_save_bit_sub)

/-- Loop-back block lifted to the top-level EXP code bundle. -/
theorem exp_loop_back_evm_exp_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 260)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 252) target htarget
  rw [expTopLoopBackNextPc] at h
  simpa [expIterCountNew] using
    (cpsBranchWithin_extend_code (h := h) (hmono := evmExpCode_iter_loop_back_sub))

end EvmAsm.Evm64.Exp.Compose
