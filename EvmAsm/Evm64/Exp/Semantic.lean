/-
  EvmAsm.Evm64.Exp.Semantic

  Stack-level semantic scaffolding for EXP.  The final
  `evm_exp_stack_spec_within` proof will live here once the full-loop
  composition is connected to `EvmWord.exp`.
-/

import EvmAsm.Evm64.Exp.Spec

namespace EvmAsm.Evm64

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
