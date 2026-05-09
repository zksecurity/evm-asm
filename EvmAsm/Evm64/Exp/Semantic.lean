/-
  EvmAsm.Evm64.Exp.Semantic

  Stack-level semantic scaffolding for EXP.  The final
  `evm_exp_stack_spec_within` proof will live here once the full-loop
  composition is connected to `EvmWord.exp`.
-/

import EvmAsm.Evm64.Exp.Args
import EvmAsm.Evm64.Exp.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.Exp.Compose

/-- Semantic-facing stack wrapper for the proven boundary case where the
    exponent is zero.  The full EXP loop spec will generalize this to arbitrary
    exponents; this wrapper keeps the zero-exponent stack shape in the semantic
    leaf. -/
theorem evm_exp_zero_exponent_stack_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ (256 : Word)) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp (baseWord :: EvmWord.exp baseWord 0 :: rest)) := by
  exact exp_boundary_result_exp_zero_full_post_stack_shape_clean_regs_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 base baseWord exponentWord rest

/-- Semantic-facing zero-exponent wrapper phrased through the pure EXP stack
    argument bridge. -/
theorem evm_exp_zero_exponent_args_stack_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmStackIs evmSp (baseWord :: (0 : EvmWord) :: rest))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ (256 : Word)) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp
         (baseWord ::
          ExpArgs.expResultFromArgs (ExpArgs.expArgs baseWord 0) :: rest)) := by
  simpa [ExpArgs.expResultFromArgs, ExpArgs.expArgs] using
    evm_exp_zero_exponent_stack_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 base baseWord (0 : EvmWord) rest

/-- EXP edge case required by GH #92: `0^0 = 1`. -/
example : EvmWord.exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  exact EvmWord.exp_zero_zero

/-- EXP edge case required by GH #92: `x^1 = x`. -/
example (x : EvmWord) : EvmWord.exp x 1 = x := by
  exact EvmWord.exp_one_right x

/-- EXP edge case required by GH #92: `2^256 = 0 mod 2^256`. -/
example : EvmWord.exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  exact EvmWord.exp_two_256

end EvmAsm.Evm64
