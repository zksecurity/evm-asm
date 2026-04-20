/-
  EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

  Toward Knuth's TAOCP Vol 2 §4.3.1 Theorem B for the n=4 max-trial
  call path: `div128Quot u_top u3 b3'` overestimates the true quotient
  `⌊val256(a) / val256(b)⌋` by at most 2.

  This is the major remaining math gap for call-trial DIV/MOD stack
  specs (the real shift > 0 runtime path, after max-trial under
  `hshift_nz` was shown vacuous in `MaxTrialVacuity.lean`).

  See `memory/project_knuth_theorem_b_plan.md` for the 6-PR breakdown.

  Currently contains:
  - `val256_div_scale_invariant` (Step 0).
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Scale invariance of integer division on val256: multiplying both operands
    by `2^s` doesn't change the quotient. Entry point for lifting normalized
    val256 computations back to un-normalized quotients.

    Trivial from `Nat.mul_div_mul_right`. -/
theorem val256_div_scale_invariant
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (s : Nat) :
    (val256 a0 a1 a2 a3 * 2^s) / (val256 b0 b1 b2 b3 * 2^s) =
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  have hpos : 0 < (2 : Nat)^s := by positivity
  rw [Nat.mul_div_mul_right _ _ hpos]

end EvmAsm.Evm64
