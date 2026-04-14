/-
  EvmAsm.Evm64.EvmWordArith.Div128Lemmas

  Mathematical foundations for div128 correctness: half-word OR-combine,
  128-bit Euclidean uniqueness, and trial quotient bounds (Knuth TAOCP 4.3.1).
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Half-word OR-combine: non-overlapping shift+OR = add
-- ============================================================================

/-- Combining two half-words via shift-left + OR gives addition at the Nat level,
    since the bit ranges [63:32] and [31:0] are disjoint. -/
theorem halfword_combine (a b : Word) (ha : a.toNat < 2^32) (hb : b.toNat < 2^32) :
    (a <<< 32 ||| b).toNat = a.toNat * 2^32 + b.toNat := by
  have h_disjoint : a <<< 32 &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< 32) b h_disjoint).symm,
      BitVec.toNat_add_of_and_eq_zero h_disjoint,
      BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show a.toNat * 2 ^ 32 < 2 ^ 64 by nlinarith)]

/-- Corollary: combining hi32 and lo32 of a word reconstructs it at the Nat level. -/
theorem halfword_combine_hi_lo (x : Word) :
    (hi32 x <<< 32 ||| lo32 x).toNat = x.toNat := by
  rw [halfword_combine _ _ (hi32_toNat_lt x) (lo32_toNat_lt x)]
  exact (halfword_decompose x).symm

-- ============================================================================
-- 128-bit Euclidean uniqueness (Nat level)
-- ============================================================================

/-- If `val128 u_hi u_lo = d * q + r` with `r < d`, then `q = val128 u_hi u_lo / d`.
    Used to verify div128 output by checking the division equation and remainder bound. -/
theorem val128_div_unique (u_hi u_lo : Word) (d q r : Nat)
    (hr : r < d)
    (heq : val128 u_hi u_lo = d * q + r) :
    q = val128 u_hi u_lo / d := by
  have h1 : q * d ≤ val128 u_hi u_lo := by rw [heq]; nlinarith [Nat.mul_comm d q]
  have h2 : val128 u_hi u_lo < (q + 1) * d := by rw [heq]; nlinarith [Nat.mul_comm d q]
  exact (Nat.div_eq_of_lt_le h1 h2).symm

/-- Remainder uniqueness: if the Euclidean equation holds, the remainder equals mod. -/
theorem val128_mod_unique (u_hi u_lo : Word) (d q r : Nat)
    (hr : r < d)
    (heq : val128 u_hi u_lo = d * q + r) :
    r = val128 u_hi u_lo % d := by
  have hq := val128_div_unique u_hi u_lo d q r hr heq
  have hdm := Nat.div_add_mod (val128 u_hi u_lo) d
  subst hq; nlinarith [Nat.mul_comm d (val128 u_hi u_lo / d)]

-- ============================================================================
-- Trial quotient bounds (Knuth TAOCP Vol 2, Section 4.3.1)
-- ============================================================================

-- The trial quotient q̂ = ⌊u_hi / d_hi⌋ overestimates the true quotient digit
-- q_true = ⌊(u_hi * B + un1) / d⌋ where d = d_hi * B + d_lo, B = 2^32.
--
-- Bound 1 (no normalization needed): q̂ ≥ q_true
-- Bound 2 (normalization: d_hi ≥ B/2): q̂ ≤ q_true + 2

/-- Trial quotient upper bound: `⌊u_hi / d_hi⌋ ≥ ⌊(u_hi * B + un1) / d⌋`.
    The trial quotient never underestimates. No normalization needed.

    Proof idea: `(q̂ + 1) * d_hi > u_hi`, so `(q̂ + 1) * d > u_hi * B + un1`. -/
theorem trial_quotient_ge (u_hi un1 d_hi d_lo : Nat)
    (hd_hi : 0 < d_hi) (hun1 : un1 < 2^32) :
    (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) ≤ u_hi / d_hi := by
  have hd_pos : 0 < d_hi * 2^32 + d_lo := by positivity
  have : (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) < u_hi / d_hi + 1 :=
    (Nat.div_lt_iff_lt_mul hd_pos).mpr (by
      have hq : u_hi < d_hi * (u_hi / d_hi + 1) := Nat.lt_mul_div_succ u_hi hd_hi
      calc u_hi * 2^32 + un1
          < (u_hi + 1) * 2^32 := by nlinarith
        _ ≤ d_hi * (u_hi / d_hi + 1) * 2^32 := by nlinarith
        _ = (u_hi / d_hi + 1) * (d_hi * 2^32) := by ring
        _ ≤ (u_hi / d_hi + 1) * (d_hi * 2^32 + d_lo) := by nlinarith)
  omega

/-- Trial quotient lower bound: `⌊u_hi / d_hi⌋ ≤ ⌊(u_hi * B + un1) / d⌋ + 2`.
    The trial quotient overestimates by at most 2 when d_hi ≥ B/2 (normalized).

    This is the key bound from Knuth's analysis. The normalization condition ensures
    `q̂ ≤ B + 1`, so `q̂ * d_lo < B² ≤ 2d`, giving `q̂ * d ≤ u_hi * B + 2d`. -/
theorem trial_quotient_le (u_hi un1 d_hi d_lo : Nat)
    (hd_hi_bound : d_hi < 2^32) (hd_lo : d_lo < 2^32)
    (hun1 : un1 < 2^32) (hu : u_hi < d_hi * 2^32 + d_lo) (hnorm : d_hi ≥ 2^31) :
    u_hi / d_hi ≤ (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) + 2 := by
  have hd_hi : 0 < d_hi := by omega
  set d := d_hi * 2^32 + d_lo
  set q_hat := u_hi / d_hi
  have hd_pos : 0 < d := by positivity
  have hq_mul : q_hat * d_hi ≤ u_hi := Nat.div_mul_le_self u_hi d_hi
  -- q̂ ≤ B + 1: if q̂ ≥ B+2 then q̂*d_hi ≥ (B+2)*d_hi, giving 2*d_hi ≤ d_lo,
  -- contradicting d_hi ≥ B/2 and d_lo < B.
  have hq_bound : q_hat ≤ 2^32 + 1 := by
    by_contra h_contra; push Not at h_contra
    have h1 : (2^32 + 2) * d_hi ≤ q_hat * d_hi := Nat.mul_le_mul_right d_hi (by omega)
    have h2 : 2 * d_hi ≤ d_lo := by omega
    omega
  -- q̂ * d_lo < B² ≤ 2d
  have hq_dlo_bound : q_hat * d_lo < 2^64 := by
    have : d_lo ≤ 2^32 - 1 := by omega
    have : q_hat * d_lo ≤ (2^32 + 1) * (2^32 - 1) := Nat.mul_le_mul hq_bound this
    norm_num at this ⊢; omega
  have h2d_ge : 2 * d ≥ 2^64 := by
    show 2 * (d_hi * 2^32 + d_lo) ≥ _; omega
  have hq_d_eq : q_hat * d = q_hat * d_hi * 2^32 + q_hat * d_lo := by
    show q_hat * (d_hi * 2^32 + d_lo) = _; ring
  -- Key: q̂ * d ≤ u_hi * B + 2d ≤ X + 2d where X = u_hi * B + un1
  set X := u_hi * 2^32 + un1
  have key : q_hat * d ≤ X + 2 * d := by
    calc q_hat * d = q_hat * d_hi * 2^32 + q_hat * d_lo := hq_d_eq
      _ ≤ u_hi * 2^32 + q_hat * d_lo := by nlinarith
      _ ≤ u_hi * 2^32 + 2^64 := by omega
      _ ≤ u_hi * 2^32 + 2 * d := by omega
      _ ≤ X + 2 * d := by omega
  -- Convert: q̂ * d ≤ X + 2d < (X/d + 3) * d → q̂ < X/d + 3 → q̂ ≤ X/d + 2
  have hXmod : X < (X / d + 1) * d := by
    have := Nat.div_add_mod X d; have := Nat.mod_lt X hd_pos; nlinarith
  have hlt : q_hat * d < (X / d + 3) * d := by nlinarith
  have : q_hat < X / d + 3 := by
    by_contra hc; push Not at hc
    exact Nat.not_lt.mpr (Nat.mul_le_mul_right d hc) hlt
  omega

/-- Combined: the trial quotient is within 2 of the true value.
    `q_true ≤ q̂ ≤ q_true + 2` when `d_hi ≥ B/2` (normalization condition). -/
theorem trial_quotient_range (u_hi un1 d_hi d_lo : Nat)
    (hd_hi_bound : d_hi < 2^32) (hd_lo : d_lo < 2^32)
    (hun1 : un1 < 2^32) (hu : u_hi < d_hi * 2^32 + d_lo) (hnorm : d_hi ≥ 2^31) :
    let q_hat := u_hi / d_hi
    let q_true := (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo)
    q_true ≤ q_hat ∧ q_hat ≤ q_true + 2 :=
  ⟨trial_quotient_ge u_hi un1 d_hi d_lo (by omega) hun1,
   trial_quotient_le u_hi un1 d_hi d_lo hd_hi_bound hd_lo hun1 hu hnorm⟩

-- ============================================================================
-- Product check correction: reduces overestimate from ≤ 2 to ≤ 1
-- ============================================================================

-- After computing q̂ = ⌊u_hi / d_hi⌋ and r̂ = u_hi mod d_hi, the div128
-- algorithm checks: is q̂ * d_lo > r̂ * B + un1?
-- If yes, q̂ overestimates by ≥ 1, so decrement.
-- After at most one correction, the overestimate is ≤ 1.

/-- Product check soundness: if `q̂ * d_lo > r̂ * B + un1`,
    then `q̂ > q_true` (the trial quotient strictly overestimates).

    Proof: q̂ * d = q̂ * d_hi * B + q̂ * d_lo > r̂ * d_hi * B + r̂ * B + un1
    and from r̂ = u_hi - q̂ * d_hi: q̂ * d_hi = u_hi - r̂,
    so q̂ * d > (u_hi - r̂) * B + r̂ * B + un1 = u_hi * B + un1. -/
theorem product_check_gt_imp_overestimate (u_hi un1 d_hi d_lo q_hat r_hat : Nat)
    (B : Nat := 2^32)
    (hd_pos : 0 < d_hi * B + d_lo)
    (hr_hat : r_hat = u_hi - q_hat * d_hi)
    (hq_mul : q_hat * d_hi ≤ u_hi)
    (hcheck : q_hat * d_lo > r_hat * B + un1) :
    q_hat > (u_hi * B + un1) / (d_hi * B + d_lo) := by
  set d := d_hi * B + d_lo
  set X := u_hi * B + un1
  -- q̂ * d = q̂ * d_hi * B + q̂ * d_lo > (u_hi - r̂) * B + r̂ * B + un1 = X
  have hqd_gt : q_hat * d > X := by
    calc q_hat * d = q_hat * (d_hi * B + d_lo) := rfl
      _ = q_hat * d_hi * B + q_hat * d_lo := by ring
      _ > q_hat * d_hi * B + r_hat * B + un1 := by omega
      _ = (q_hat * d_hi + r_hat) * B + un1 := by ring
      _ = u_hi * B + un1 := by
            rw [hr_hat, Nat.add_sub_cancel' hq_mul]
  exact (Nat.div_lt_iff_lt_mul hd_pos).mpr hqd_gt

/-- After the product check correction, the overestimate is ≤ 1.
    If the product check passes (no correction needed), then q̂ ≤ q_true + 1.
    If the product check fails and we decrement, the result ≤ q_true + 1
    since the initial overestimate was ≤ 2. -/
theorem corrected_quotient_le (u_hi un1 d_hi d_lo q_hat : Nat)
    (hd_hi_pos : 0 < d_hi)
    (hq_mul : q_hat * d_hi ≤ u_hi)
    (r_hat : Nat) (hr_hat : r_hat = u_hi - q_hat * d_hi)
    (hcheck_pass : q_hat * d_lo ≤ r_hat * 2^32 + un1) :
    q_hat ≤ (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) + 1 := by
  set d := d_hi * 2^32 + d_lo
  set X := u_hi * 2^32 + un1
  have hd_pos : 0 < d := by positivity
  -- q̂ * d_lo ≤ r̂ * B + un1, so q̂ * d ≤ (q̂*d_hi + r̂)*B + un1 = u_hi*B + un1 = X
  have hqd_le : q_hat * d ≤ X := by
    calc q_hat * d = q_hat * d_hi * 2^32 + q_hat * d_lo := by ring
      _ ≤ q_hat * d_hi * 2^32 + r_hat * 2^32 + un1 := by omega
      _ = (q_hat * d_hi + r_hat) * 2^32 + un1 := by ring
      _ = u_hi * 2^32 + un1 := by
            rw [hr_hat, Nat.add_sub_cancel' hq_mul]
  -- From q̂ * d ≤ X: q̂ ≤ X / d
  have : q_hat ≤ X / d := Nat.le_div_iff_mul_le hd_pos |>.mpr hqd_le
  omega

end EvmWord

end EvmAsm.Evm64
