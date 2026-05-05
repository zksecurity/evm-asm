/-
  EvmAsm.Evm64.EvmWordArith.Pow256ModN

  Helper for ADDMOD/MULMOD (GH issue #91): compute the runtime constant
  `m = 2^256 mod N` as an `EvmWord`, using only the existing
  `EvmWord.mod` and `BitVec` arithmetic. The construction relies on the
  identity

      2^256 mod N = (((2^256 - 1) mod N) + 1) mod N

  which is computable inside `EvmWord` because `2^256 - 1` is just
  `(-1 : EvmWord)` (i.e. `BitVec.allOnes 256`). This avoids a wider
  dividend that would not fit `EvmWord.mod`'s 4-limb signature.

  Refs: GH #91, `docs/91-addmod-mulmod-survey.md` §3, beads
  `evm-asm-7j463`.
-/

import EvmAsm.Evm64.EvmWordArith.DivCorrect

namespace EvmAsm.Evm64

namespace EvmWord

/-- The runtime EVM word `2^256 mod N` (with `N = 0 ⇒ 0`).

    Computed as `(((-1 : EvmWord) mod N) + 1) mod N`. The inner
    `EvmWord.mod` returns a value strictly less than `N`, so the
    `+ 1` step does not overflow the 256-bit `BitVec`; the outer
    `mod N` collapses the `N = ((2^256 - 1) mod N) + 1` corner case
    (which arises when `N` divides `2^256`) back to `0`. -/
def pow256ModN (N : EvmWord) : EvmWord :=
  if N = 0 then 0 else EvmWord.mod (EvmWord.mod (-1 : EvmWord) N + 1) N

/-- Algebraic correctness of `EvmWord.pow256ModN`:
    `(pow256ModN N).toNat = if N = 0 then 0 else 2^256 % N.toNat`. -/
theorem pow256ModN_correct (N : EvmWord) :
    (EvmWord.pow256ModN N).toNat =
      if N = 0 then 0 else 2 ^ 256 % N.toNat := by
  unfold pow256ModN
  by_cases hN : N = 0
  · simp [hN]
  · simp only [if_neg hN]
    -- Step 1: m1 := (-1) mod N has toNat = (2^256 - 1) % N.toNat.
    have hN_pos : 0 < N.toNat := by
      have : N.toNat ≠ 0 := fun hz => hN (BitVec.eq_of_toNat_eq (by simpa using hz))
      omega
    have hN_lt : N.toNat < 2 ^ 256 := N.isLt
    have h_neg_one : (-1 : EvmWord).toNat = 2 ^ 256 - 1 := by
      decide
    have h_m1 : (EvmWord.mod (-1 : EvmWord) N).toNat = (2 ^ 256 - 1) % N.toNat := by
      rw [mod_correct, if_neg hN, h_neg_one]
    -- Step 2: m1 + 1 in EvmWord. Since m1.toNat < N.toNat ≤ 2^256-1, we have
    -- m1.toNat + 1 ≤ N.toNat ≤ 2^256 - 1 < 2^256, so the BitVec add is exact.
    set m1 := EvmWord.mod (-1 : EvmWord) N with hm1_def
    have h_m1_lt_N : m1.toNat < N.toNat := by
      rw [h_m1]; exact Nat.mod_lt _ hN_pos
    have h_m1p1 : (m1 + 1).toNat = m1.toNat + 1 := by
      have h1 : (1 : EvmWord).toNat = 1 := by decide
      rw [BitVec.toNat_add, h1]
      apply Nat.mod_eq_of_lt
      omega
    -- Step 3: outer mod by N.
    rw [mod_correct, if_neg hN, h_m1p1, h_m1]
    -- Goal: ((2^256 - 1) % N.toNat + 1) % N.toNat = 2^256 % N.toNat
    -- Use: 2^256 = (2^256 - 1) + 1, then Nat.add_mod symmetry.
    have h_sum : (2 ^ 256 - 1) + 1 = 2 ^ 256 := by
      have : (1 : Nat) ≤ 2 ^ 256 := Nat.one_le_two_pow
      omega
    rw [← h_sum, Nat.add_mod]
    simp

end EvmWord

-- ============================================================================
-- Sanity checks
-- ============================================================================

-- N = 7: 2^256 mod 7. 2^256 = (2^3)^85 · 2 = 1^85 · 2 = 2 (mod 7).
example : (EvmWord.pow256ModN (BitVec.ofNat 256 7)).toNat = 2 := by native_decide

-- N = 0 ⇒ 0.
example : (EvmWord.pow256ModN 0).toNat = 0 := by native_decide

-- N = 1 ⇒ 0 (everything mod 1 is 0).
example : (EvmWord.pow256ModN 1).toNat = 0 := by native_decide

end EvmAsm.Evm64
