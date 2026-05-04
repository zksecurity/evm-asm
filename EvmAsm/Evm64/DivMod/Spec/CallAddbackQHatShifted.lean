/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackQHatShifted

  Phase-3 shifted-domain qHat sub-lemmas extracted from
  `Spec.CallAddback` (#1078 sub-slice). These three theorems convert
  the v2 borrow flag into shifted-domain bounds on `qHat`:

  - `qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2` —
    `qHat * val256(b_shifted) > val256(a_shifted)`, derived directly
    from the contrapositive of `c3_un_zero_of_qHat_mul_le`.
  - `qHat_gt_q_true_shifted_under_runtime_v2` — divisor form of the
    above via `Nat.div_lt_iff_lt_mul`.
  - `qHat_lower_shifted_under_runtime_v2` — `+1`-form of the divisor
    bound, suitable for downstream `omega` chaining.

  The trio is dependency-clean: it only uses already-public symbols
  (`c3_un_zero_of_qHat_mul_le`, `b3_prime_ge_pow63`,
  `EvmWord.u_top_lt_c3_of_addback_borrow_call_v2`,
  `isAddbackBorrowN4CallEvm_v2_def`) and has no in-repo Lean
  consumers outside doc references in
  `SpecCallAddbackBeq/NumericalTests.lean`.

  Issue #1337 algorithm fix migration. Authored by @pirapira;
  implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackPhase1Stubs

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **qHat * val256(b_shifted) > val256(a_shifted) under v2 borrow** —
    the shifted-domain version of `qHat_gt_q_true`. This statement is
    DIRECTLY derivable from `c3_un_zero_of_qHat_mul_le`'s contrapositive,
    avoiding the truncation issue with `q_true` (the original-domain
    quotient).

    Key insight: `c3_un_zero_of_qHat_mul_le` operates on raw limbs
    (whatever they are). In our setting the inputs are SHIFTED limbs,
    so the conclusion `qHat * val256(SHIFTED b) > val256(SHIFTED a)` is
    immediate from `c3 ≠ 0`.

    Issue #1337 algorithm fix migration. Path 3 shifted-domain sub-lemma. -/
theorem qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2 (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat * val256 b0' b1' b2' b3' > val256 u0 u1 u2 u3 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  -- Step 1: hborrow_v2 → c3 ≠ 0 via u_top_lt_c3.
  rw [isAddbackBorrowN4CallEvm_v2_def] at hborrow_v2
  have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call_v2
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hborrow_v2
  simp only [] at h_u4_lt_c3
  -- Step 2: contrapositive of `c3_un_zero_of_qHat_mul_le` — c3 ≠ 0 ⟹
  --   qHat * val256(b_shifted) > val256(a_shifted).
  by_contra hle
  push Not at hle
  -- hle : qHat.toNat * val256 b0' b1' b2' b3' ≤ val256 u0 u1 u2 u3.
  have h_c3_zero := c3_un_zero_of_qHat_mul_le hle
  -- h_c3_zero : (mulsubN4 ...).2.2.2.2 = 0 (as Word).
  -- h_u4_lt_c3 : u4.toNat < (mulsubN4 ...).2.2.2.2.toNat.
  -- Combine: u4.toNat < 0, contradiction.
  -- Bridge h_c3_zero (Word equality) to a Nat equality on the same expression.
  have h_zero : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
    rw [h_c3_zero]; rfl
  -- Convert h_u4_lt_c3 (unfolded form) to use the local lets via `change`
  -- (definitional equality through zeta-reduction of qHat, b0', etc.).
  change u4.toNat < (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
    at h_u4_lt_c3
  omega

/-- **qHat > val256(a_shifted) / val256(b_shifted) under v2 borrow** —
    direct corollary of `qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2`.

    Converts the multiplicative form `qHat * val256(b') > val256(a')` to
    the divisor form `qHat > val256(a') / val256(b')` via Nat division.
    Useful for the shifted-domain carry partition.

    Issue #1337 algorithm fix migration. -/
theorem qHat_gt_q_true_shifted_under_runtime_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat > val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  have h_mul := qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2 a b hb3nz hborrow_v2
  simp only [] at h_mul
  -- h_mul : qHat.toNat * val256 b0' b1' b2' b3' > val256 u0 u1 u2 u3.
  -- Need val256 b' > 0 to use Nat.div_lt_iff.
  have h_b3'_ge : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2)
    hb3nz (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1)
  have h_v_pos : val256 b0' b1' b2' b3' > 0 := by
    show b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128 + b3'.toNat * 2^192 > 0
    have : b3'.toNat * 2^192 > 0 := by positivity
    omega
  exact (Nat.div_lt_iff_lt_mul h_v_pos).mpr h_mul

/-- **qHat lower bound shifted-domain (ALONE)** — extracted from
    `qHat_in_range_under_runtime_v2` for direct use with the proven
    `qHat_gt_q_true_shifted_under_runtime_v2`. Just the lower-bound half.

    Issue #1337 algorithm fix migration. -/
theorem qHat_lower_shifted_under_runtime_v2 (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' + 1 ≤ qHat.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  have h := qHat_gt_q_true_shifted_under_runtime_v2 a b hb3nz hborrow_v2
  simp only [] at h
  -- Convert h's unfolded form to use local lets for omega.
  change qHat.toNat > val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' at h
  omega

end EvmAsm.Evm64
