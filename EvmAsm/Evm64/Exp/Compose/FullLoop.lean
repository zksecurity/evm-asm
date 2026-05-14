/-
  EvmAsm.Evm64.Exp.Compose.FullLoop

  Small full-loop prep helpers for EXP.  The static EXP body contains JALs to
  the out-of-line `mul_callable`, so full-loop composition needs a code bundle
  that contains both the top-level EXP program and the callable multiply body.
-/

import EvmAsm.Evm64.Exp.Compose.WithMulCode
import EvmAsm.Evm64.Exp.Compose.LoopControlBlocks
import EvmAsm.Evm64.Exp.Compose.SquaringMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.SquaringCallPath
import EvmAsm.Evm64.Exp.Compose.CondMulCallPath
import EvmAsm.Evm64.Exp.Compose.SquaringCallBlock
import EvmAsm.Evm64.Exp.Compose.CondMulCallBlock
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Bit-test block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_bit_test_evm_exp_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_bit_test_evm_exp_spec_within e c v10 mulOff skipOff backOff base)

/-- Loop-back block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_loop_back_evm_exp_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 252)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 260)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) :=
  cpsBranchWithin_extend_evmExpWithMulCode
    (exp_loop_back_evm_exp_spec_within c mulOff skipOff backOff base target htarget)

/-- Squaring-call JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 104) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 108)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)

/-- Conditional-multiply JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_cond_mul_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 212) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 216)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)

/-- Squaring-call factor-1 marshal lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_marshal_factor1_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 40) (base + 72)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_marshal_factor1_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Squaring-call factor-2 marshal lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_marshal_result_to_factor2_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 72) (base + 104)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_marshal_result_to_factor2_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Squaring-call un-marshal-and-restore lifted to the full-loop EXP+MUL code
    bundle. -/
theorem exp_squaring_un_marshal_and_restore_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_un_marshal_and_restore_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Conditional-multiply factor-1 marshal lifted to the full-loop EXP+MUL
    code bundle. -/
theorem exp_cond_mul_marshal_factor1_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 148) (base + 180)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_marshal_factor1_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Conditional-multiply factor-2 marshal (from EVM-stack base slot) lifted
    to the full-loop EXP+MUL code bundle. -/
theorem exp_cond_mul_marshal_a_to_factor2_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 180) (base + 212)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_marshal_a_to_factor2_evm_exp_spec_within
      mulOff skipOff backOff evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 base)

/-- Conditional-multiply un-marshal-and-restore lifted to the full-loop
    EXP+MUL code bundle. -/
theorem exp_cond_mul_un_marshal_and_restore_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 216) (base + 252)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_un_marshal_and_restore_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Conditional-multiply BEQ skip-gate lifted to the full-loop EXP+MUL code
    bundle. -/
theorem exp_cond_mul_beq_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 : Word) (base mulTarget target : Word)
    (htarget : (base + 144 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 144)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝)
      (base + 148) ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) :=
  cpsBranchWithin_extend_evmExpWithMulCode
    (exp_cond_mul_beq_evm_exp_spec_within
      mulOff skipOff backOff v10 base target htarget)

/-- Cond-mul-side full call-block (`marshal_pair + JAL + mul_callable +
    un_marshal_and_restore`, 90 instrs) lifted from the disjoint-union
    code into the full-loop `evmExpWithMulCode` bundle. Instantiates
    `EvmAsm.Evm64.exp_cond_mul_call_block_spec_within` at offset
    `base + 148` (the cond-mul call sub-block entry after the leading
    BEQ skip-gate at `base + 144`). -/
theorem exp_cond_mul_call_block_evm_exp_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 148) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let rw := expCondMulRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 148) ((base + 148) + 104)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 148) + 68))) := by
  intro rw
  have hbase' : (base + 148 : Word) &&& 1 = 0 := by bv_decide
  -- Sub-sub: exp_cond_mul_call_block_code (base+148) ⊆ evmExpCode base
  -- via the with-skip block at base+144.
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 148) mulOff a = some i →
      evmExpCode base mulOff skipOff backOff a = some i := by
    intro a i h
    have hskip : (base + 148 : Word) = base + 144 + 4 := by bv_omega
    rw [hskip] at h
    exact evmExpCode_iter_cond_mul_sub a i
      (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
        (base + 144) mulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 148) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 148) mulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 148) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpWithMulCode_exp_sub a i (hCondSub a i h))
      (fun a i h => evmExpWithMulCode_mul_sub hd a i h)) hbase_spec


end EvmAsm.Evm64.Exp.Compose
