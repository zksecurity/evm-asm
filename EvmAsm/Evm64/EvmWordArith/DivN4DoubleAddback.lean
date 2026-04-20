/-
  EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback

  Inversion of `addbackN4_second_carry_one`: derive the trial-quotient
  overestimate bound (`q ≤ ⌊u/v⌋ + 2`) from the second-addback carry = 1.

  This unblocks the double-addback correctness path: the runtime
  `isAddbackCarry2NzN4Max` check gives the algorithm a carry2 ≠ 0 witness
  (combined with `carry2 < 2` to pin it to 1); from carry2 = 1 this file
  proves the overestimate bound, which then feeds
  `mulsub_double_addback_val256_combined` to get the Euclidean equation
  `val256(u) = (q - 2) * val256(v) + val256(ab')`.

  Foundation for `n4_max_double_addback_correct` (Phase A of the n=4
  max+addback stack spec roadmap, Issue #61).
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Inversion: if the second-addback carry is 1 (double-addback path), the
    trial quotient `q` overestimates `⌊val256(u)/val256(v)⌋` by at most 2.
    Converse to `addbackN4_second_carry_one` — that theorem assumes
    `hq_over` and proves `carry2 = 1`; this one uses `carry2 = 1` to
    conclude `hq_over`. -/
theorem hq_over_from_second_carry_one (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry_zero : (addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3) = 0)
    (hcarry2_one :
      let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat = 1) :
    q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 := by
  simp only [] at hcarry2_one
  -- From c3 = 1: val256(u) + 2^256 = val256(un) + q * val256(v)
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  rw [show (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = (1 : Word) from hc3_one] at hmulsub
  have h1w : (1 : Word).toNat = 1 := by decide
  rw [h1w] at hmulsub
  -- First addback: val256(un) + val256(v) = val256(ab1) + 0 * 2^256 = val256(ab1)
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3 with hms_def
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab1
  have hc1_val : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3).toNat = 0 := by
    rw [hcarry_zero]; decide
  rw [hc1_val] at hab1
  -- Second addback: val256(ab1) + val256(v) = val256(ab') + 1 * 2^256
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3 with hab_def
  have hab' := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab'
  rw [hcarry2_one] at hab'
  -- Bounds
  have hv_pos : 0 < val256 v0 v1 v2 v3 := val256_pos_of_or_ne_zero v0 v1 v2 v3 hbnz
  have hab'_bound := val256_bound
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.2.1
  -- From hab' + hab'_bound: val256(ab1) + val256(v) ≥ 2^256 + 1 > 2^256
  -- Combined with hab1 (val256(un) + val256(v) = val256(ab1)):
  --   val256(un) + 2 * val256(v) ≥ 2^256 + 1
  -- From hmulsub: val256(un) = val256(u) + 2^256 - q * val256(v)
  --   val256(u) + 2^256 - q * val256(v) + 2 * val256(v) ≥ 2^256 + 1
  --   val256(u) + (2 - q) * val256(v) ≥ 1  (signed arithmetic)
  --   val256(u) ≥ (q - 2) * val256(v)  (Nat subtraction handles q < 2 trivially)
  -- Hence u/v ≥ q - 2, i.e., q ≤ u/v + 2.
  have hq_v_le_plus : q.toNat * val256 v0 v1 v2 v3 ≤
      val256 u0 u1 u2 u3 + 2 * val256 v0 v1 v2 v3 := by nlinarith
  -- (q - 2) * v ≤ u
  have hqm2_le : (q.toNat - 2) * val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 := by
    rcases Nat.lt_or_ge q.toNat 2 with hq_lt | hq_ge
    · -- q < 2: q - 2 = 0, trivial
      have : q.toNat - 2 = 0 := by omega
      rw [this]; simp
    · -- q ≥ 2
      have hq_split : q.toNat * val256 v0 v1 v2 v3 =
          (q.toNat - 2) * val256 v0 v1 v2 v3 + 2 * val256 v0 v1 v2 v3 := by
        have : q.toNat = (q.toNat - 2) + 2 := by omega
        nlinarith
      linarith
  -- u/v ≥ q - 2
  have hdiv_ge : val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 ≥ q.toNat - 2 := by
    exact Nat.le_div_iff_mul_le hv_pos |>.mpr (by linarith [Nat.mul_comm (q.toNat - 2) (val256 v0 v1 v2 v3)])
  omega

end EvmAsm.Evm64
