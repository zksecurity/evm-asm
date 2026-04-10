/-
  EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

  Trial quotient overestimate proofs for the n=4 case (b3 ≠ 0, single iteration).

  The max-trial quotient (signExtend12 4095 = 2^64-1) overestimates ⌊val256(a)/val256(b)⌋
  when b3 ≠ 0, because val256(b) ≥ 2^192 forces val256(a)/val256(b) < 2^64.

  These are the key hypotheses needed by `div_correct_n4_no_shift` to bridge
  from the algorithm's mulsub/addback computations to EvmWord.div correctness.
-/

import EvmAsm.Evm64.EvmWordArith.DivAccumulate
import EvmAsm.Evm64.DivMod.LoopSemantic

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

-- ============================================================================
-- Max trial overestimate: q_hat = 2^64 - 1 ≥ ⌊val256(a)/val256(b)⌋
-- ============================================================================

/-- When b3 ≠ 0, val256(a)/val256(b) ≤ 2^64 - 1.
    This is because val256(b) ≥ 2^192 (from b3 ≠ 0) and val256(a) < 2^256. -/
theorem val256_div_lt_pow64 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb3nz : b3 ≠ 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ 2^64 - 1 := by
  have hb_ge := val256_ge_pow192_of_limb3 b0 b1 b2 b3 hb3nz
  have ha_lt := val256_bound a0 a1 a2 a3
  -- val256(a) < 2^256 = 2^64 * 2^192 ≤ 2^64 * val256(b)
  -- So val256(a) / val256(b) < 2^64
  have hb_pos : 0 < val256 b0 b1 b2 b3 := by omega
  calc val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3
      ≤ (2^256 - 1) / val256 b0 b1 b2 b3 := Nat.div_le_div_right (by omega)
    _ ≤ (2^256 - 1) / 2^192 := Nat.div_le_div_left hb_ge (by omega)
    _ = 2^64 - 1 := by norm_num

/-- signExtend12 4095 as Word has toNat = 2^64 - 1. -/
theorem signExtend12_4095_toNat : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by
  native_decide

/-- Max trial quotient overestimate for n=4: when b3 ≠ 0,
    ⌊val256(a)/val256(b)⌋ ≤ (signExtend12 4095).toNat.
    This is the `hge` hypothesis needed by `div_correct_n4_no_shift`. -/
theorem max_trial_overestimate_n4 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb3nz : b3 ≠ 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ (signExtend12 (4095 : BitVec 12) : Word).toNat := by
  rw [signExtend12_4095_toNat]
  exact val256_div_lt_pow64 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz

-- ============================================================================
-- Skip path: mulsub c3=0 → Euclidean equation → EvmWord.div correctness
-- ============================================================================

/-- Skip path (c3 = 0, max trial) at n=4: when mulsubN4 produces no borrow,
    the max trial quotient (2^64-1) equals ⌊val256(a)/val256(b)⌋
    and fromLimbs [q_hat, 0, 0, 0] = EvmWord.div a b. -/
theorem n4_max_skip_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hc3_zero : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let q_hat : Word := signExtend12 4095
    let ms := mulsubN4 q_hat b0 b1 b2 b3 a0 a1 a2 a3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q_hat | 1 => (0 : Word) | 2 => (0 : Word) | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => ms.1 | 1 => ms.2.1 | 2 => ms.2.2.1 | 3 => ms.2.2.2.1
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro q_hat ms q r a b
  -- From mulsubN4_val256_eq: val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
  have hmulsub_raw := mulsubN4_val256_eq q_hat b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at hmulsub_raw
  -- c3 = 0, so val256(u) = val256(un) + q * val256(v)
  rw [show ms.2.2.2.2 = (0 : Word) from hc3_zero] at hmulsub_raw
  have : (0 : Word).toNat = 0 := by decide
  rw [this, Nat.zero_mul, Nat.add_zero] at hmulsub_raw
  -- Rearrange: val256 a = q.toNat * val256 b + val256 r
  have hmulsub : val256 a0 a1 a2 a3 = q_hat.toNat * val256 b0 b1 b2 b3 +
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by linarith
  -- Overestimate: val256(a)/val256(b) ≤ q_hat.toNat
  have hge := max_trial_overestimate_n4 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz
  exact div_correct_n4_no_shift hbnz hmulsub hge

-- Note: The addback path (c3 ≠ 0) requires additionally proving:
-- 1. The mulsub borrow c3 is exactly 0 or 1 (borrow bound from Knuth's Theorem B)
-- 2. The addback carry equals c3 (so 2^256 terms cancel)
-- 3. The combined Euclidean equation: val256(a) = (q_hat-1) * val256(b) + val256(aun)
-- This deeper analysis is left for a follow-up.

end EvmAsm.Evm64
