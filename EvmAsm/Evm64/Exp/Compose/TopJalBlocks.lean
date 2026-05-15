/-
  EvmAsm.Evm64.Exp.Compose.TopJalBlocks

  JAL specs lifted to the top-level EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.TopCallSubs
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

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
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringSquareReturnPc] at h
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
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulSquareReturnPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_cond_mul_square_sub)

end EvmAsm.Evm64.Exp.Compose
