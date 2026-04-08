/-
  EvmAsm.Evm64.EvmWordArith.DivN4Lemmas

  Specialized lemmas for the n=4 division case (divisor uses all 4 limbs).
  When n=4 and shift=0, the quotient has at most 1 limb and the algorithm
  runs a single loop iteration. These lemmas establish:
  - quotient bound (≤ 1) from MSB condition
  - division correctness for the q=0 and q=1 subcases
  - val128 simplification when u_hi = 0
-/

import EvmAsm.Evm64.EvmWordArith.DivBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- val128 simplification
-- ============================================================================

/-- When u_hi = 0, val128 reduces to the low word's toNat. -/
theorem val128_zero_hi (u_lo : Word) : val128 0 u_lo = u_lo.toNat := by
  unfold val128; simp

-- ============================================================================
-- Quotient bound for n=4 shift=0
-- ============================================================================

/-- When the divisor's MSB is set (d ≥ 2^63) and u_hi = 0,
    the 128-bit quotient is at most 1.
    This is the key bound for n=4 shift=0: the single loop iteration
    produces a trial quotient q̂ ∈ {0, 1}. -/
theorem div_nat_le_one_of_msb (u_lo d : Word) (hd : d.toNat ≥ 2^63) :
    u_lo.toNat / d.toNat ≤ 1 := by
  have hulo := u_lo.isLt
  have : u_lo.toNat / d.toNat < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.toNat)]
    nlinarith
  omega

-- ============================================================================
-- n=4 shift=0 correctness: q=0 case (a < b)
-- ============================================================================

/-- When a < b, the quotient is 0 and the remainder is a itself. -/
theorem div_zero_of_lt (a b : EvmWord) (hbnz : b ≠ 0)
    (h_lt : a.toNat < b.toNat) :
    (0 : EvmWord) = EvmWord.div a b :=
  div_of_nat_euclidean a b 0 a hbnz (by simp) h_lt

theorem mod_self_of_lt (a b : EvmWord) (hbnz : b ≠ 0)
    (h_lt : a.toNat < b.toNat) :
    a = EvmWord.mod a b :=
  mod_of_nat_euclidean a b 0 a hbnz (by simp) h_lt

-- ============================================================================
-- n=4 shift=0 correctness: q=1 case (b ≤ a < 2*b)
-- ============================================================================

/-- When b ≤ a < 2b, the quotient is 1 and the remainder is a - b. -/
theorem div_one_of_ge_lt (a b : EvmWord) (hbnz : b ≠ 0)
    (h_ge : b.toNat ≤ a.toNat) (h_lt2 : a.toNat < 2 * b.toNat) :
    (1 : EvmWord) = EvmWord.div a b := by
  have h1 : (1 : EvmWord).toNat = 1 := by decide
  apply div_of_nat_euclidean a b 1 (a - b) hbnz
  · rw [h1, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega
  · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega

theorem mod_sub_of_ge_lt (a b : EvmWord) (hbnz : b ≠ 0)
    (h_ge : b.toNat ≤ a.toNat) (h_lt2 : a.toNat < 2 * b.toNat) :
    a - b = EvmWord.mod a b := by
  have h1 : (1 : EvmWord).toNat = 1 := by decide
  apply mod_of_nat_euclidean a b 1 (a - b) hbnz
  · rw [h1, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega
  · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega

-- ============================================================================
-- MSB condition implies divisor bound for trial quotient
-- ============================================================================

/-- If the top limb b3 has MSB set (b3 ≥ 2^63), then its upper half-word
    satisfies the normalization condition d_hi ≥ 2^31 for trial quotient bounds. -/
theorem msb_imp_hi32_ge (b3 : Word) (hmsb : b3.toNat ≥ 2^63) :
    (hi32 b3).toNat ≥ 2^31 := by
  unfold hi32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb3 := b3.isLt
  exact Nat.le_div_iff_mul_le (by positivity) |>.mpr (by omega)

/-- If b3 ≥ 2^63, the full 256-bit divisor b satisfies b ≥ 2^192 * 2^63 > 0. -/
theorem val256_pos_of_b3_msb (b0 b1 b2 b3 : Word) (hmsb : b3.toNat ≥ 2^63) :
    val256 b0 b1 b2 b3 ≥ 2^63 * 2^192 := by
  unfold val256
  nlinarith

end EvmWord

end EvmAsm.Evm64
