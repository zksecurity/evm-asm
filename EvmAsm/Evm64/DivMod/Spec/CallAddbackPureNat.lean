/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat

  Pure-Nat algebraic identities for the call+addback BEQ algorithm.

  Self-contained block — operates entirely on `Nat` (no `Word`, `EvmWord`,
  or `BitVec`). Provides the Euclidean-identity composition lemmas used by
  the Word-level wrappers in `Spec/CallAddback.lean`:

  - `val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4`
  - `c3_le_u4_plus_one_from_identity`
  - `c3_eq_u4_plus_one_from_mulsub_addback_bounds`
  - `val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4`
  - `c3_eq_u4_plus_one_from_double_mulsub_addback_bounds`
  - `abPrime_val_eq_amod_pow_s_pure_nat`

  Extracted from `Spec/CallAddback.lean` (file-size-exception, #1078).
  No external Lean expression depends on these names other than the
  consumers in `CallAddback.lean` (the docstrings in `SpecCallAddbackBeq/`
  cross-reference them by name only). See evm-asm-rfl / sub-slice of
  evm-asm-ry8.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import Mathlib.Tactic.Ring

namespace EvmAsm.Evm64

/-- **Pure-Nat algebraic identity: post1_low4 + (u4 + 1)*2^256 = a%b*2^s + c3*2^256.**

    Combines the mulsub Euclidean, addback Euclidean, val256 normalization
    identities, and qHat = a/b + 1 into a single Nat equation. Avoids Nat
    subtraction by rearranging.

    From this identity + bound `post1_low4 < 2^256` + `c3 < 2^256` + the
    range of `a%b * 2^s < 2^256`, omega can derive c3 = u4 + 1 in single-
    addback. (Note: the lemma exposes the algebra; the surrounding proof
    must establish u4_lt_c3 from hborrow to pin c3 ≥ u4 + 1.) -/
theorem val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s) :
    post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256 := by
  have h_dam_mul : a_val / b_val * b_val + a_val % b_val = a_val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a_val b_val
  -- Replace `a_val / b_val * b_val * 2^s` with `a_val * 2^s - a_val % b_val * 2^s`
  -- via h_dam_mul.
  have h_div_mul_pow : a_val / b_val * b_val * 2^s + a_val % b_val * 2^s = a_val * 2^s := by
    rw [← Nat.add_mul]; rw [h_dam_mul]
  have h_expand : (a_val / b_val + 1) * (b_val * 2^s) =
      a_val / b_val * b_val * 2^s + b_val * 2^s := by ring
  -- h_mulsub_simp: c3 * 2^256 + a_val % b_val * 2^s = ms_val + b_val * 2^s + u4 * 2^256.
  have h_mulsub_simp : c3 * 2^256 + a_val % b_val * 2^s =
      ms_val + b_val * 2^s + u4 * 2^256 := by
    -- Use h_mulsub + h_expand + h_div_mul_pow + h_u4_le.
    have h1 : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
              ms_val + (a_val / b_val * b_val * 2^s + b_val * 2^s) := by
      rw [← h_expand]; exact h_mulsub
    omega
  -- Combine with h_addback.
  omega

/-- **Pure-Nat: c3 ≤ u4 + 1 from the closed identity + bounds.**

    Direct corollary: from `post1_val + (u4 + 1)*2^256 = a%b*2^s + c3*2^256`
    plus `post1_val < 2^256` (val256 bound) and `a%b*2^s < 2^256` (a%b < b
    and b * 2^s ≤ 2^256), it follows that `c3 ≤ u4 + 1` — otherwise
    post1_val would exceed 2^256. -/
theorem c3_le_u4_plus_one_from_identity
    (post1_val a_val b_val s u4 c3 : Nat)
    (h_id : post1_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256) :
    c3 ≤ u4 + 1 := by
  -- Suppose c3 ≥ u4 + 2. Then RHS ≥ (u4 + 2)*2^256 = (u4 + 1)*2^256 + 2^256.
  -- LHS = post1_val + (u4 + 1)*2^256 < 2^256 + (u4 + 1)*2^256.
  -- a%b*2^s ≥ 0 and a%b*2^s < 2^256, so RHS could be in
  -- [(u4 + 2)*2^256, (u4 + 2)*2^256 + 2^256). LHS bound contradicts.
  by_contra h_gt
  have h_c3_ge : c3 ≥ u4 + 2 := Nat.lt_of_not_ge h_gt
  have h_c3_mul : c3 * 2^256 ≥ (u4 + 2) * 2^256 := Nat.mul_le_mul_right _ h_c3_ge
  have h_split : (u4 + 2) * 2^256 = (u4 + 1) * 2^256 + 2^256 := by ring
  omega

/-- **Pure-Nat: c3 = u4 + 1 from mulsub Euclidean + addback Euclidean + bounds.**

    Combined sub-stub: takes the val256-level Euclidean equations, normalization
    bounds, and `u4 < c3`, and outputs c3 = u4 + 1 directly. This is the
    pure-Nat composition of the algebraic identity, the c3 ≤ u4 + 1 bound,
    and the u4 < c3 hypothesis.

    Once the Word-level wrapper at `c3_n_eq_u4_plus_one_of_single_addback`
    is plumbed up, it just calls this. -/
theorem c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (post1_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) = ms_val + (a_val / b_val + 1) * (b_val * 2^s))
    (h_addback : post1_val + 2^256 = ms_val + b_val * 2^s)
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_post1_lt : post1_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    c3 = u4 + 1 := by
  have h_id := val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    post1_val ms_val a_val b_val s u4 c3 h_mulsub h_addback h_u4_le
  have h_le := c3_le_u4_plus_one_from_identity
    post1_val a_val b_val s u4 c3 h_id h_post1_lt h_amod_pow_lt
  omega

/-- **B.3 (pure-Nat algebra for double-addback): closed identity.**

    Mirror of `val256_post1_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4`
    for the **double-addback** branch. The double-addback path runs two
    `addbackN4` calls; the val256-level invariants are:
    - mulsub with qHat = a/b + 2.
    - First addback (carry₁ = 0): ab = ms + b * 2^s (no wrap).
    - Second addback (carry₂ = 1): ab' + 2^256 = ab + b * 2^s (wrap).

    Combined: `ab' + 2^256 = ms + 2 * (b * 2^s)`. Algebra below uses that
    combined form as `h_addback_combined`.

    **Algebraic surprise** (per #1338): the resulting identity is **identical**
    to single-addback's `c3 = u4 + 1` shape, despite qHat shifting from
    `a/b + 1` to `a/b + 2`. The +2's extra `b * 2^s` is absorbed by the
    second addback's `+ b * 2^s`.

    This pure-Nat lemma does NOT depend on Knuth-B (#1337). The Knuth bound
    is needed only to discharge the `(a/b + 2)` factor in `h_mulsub` (i.e.,
    Phase B.1 `qHat_eq_div_plus_two_of_double_addback`). -/
theorem val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s) :
    abPrime_val + (u4 + 1) * 2^256 = a_val % b_val * 2^s + c3 * 2^256 := by
  have h_dam_mul : a_val / b_val * b_val + a_val % b_val = a_val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a_val b_val
  have h_div_mul_pow : a_val / b_val * b_val * 2^s + a_val % b_val * 2^s = a_val * 2^s := by
    rw [← Nat.add_mul]; rw [h_dam_mul]
  have h_expand : (a_val / b_val + 2) * (b_val * 2^s) =
      a_val / b_val * b_val * 2^s + 2 * (b_val * 2^s) := by ring
  -- h_mulsub_simp: c3 * 2^256 + a%b * 2^s = ms_val + 2 * (b * 2^s) + u4 * 2^256.
  have h_mulsub_simp : c3 * 2^256 + a_val % b_val * 2^s =
      ms_val + 2 * (b_val * 2^s) + u4 * 2^256 := by
    have h1 : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
              ms_val + (a_val / b_val * b_val * 2^s + 2 * (b_val * 2^s)) := by
      rw [← h_expand]; exact h_mulsub
    omega
  -- Combine with h_addback_combined.
  omega

/-- **B.3: c3 = u4 + 1 from double-addback Euclidean + bounds** (CLOSED, pure-Nat).

    Direct mirror of `c3_eq_u4_plus_one_from_mulsub_addback_bounds` for the
    double-addback path. The closed identity from
    `val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4` has
    the same shape as single-addback's; combined with
    `c3_le_u4_plus_one_from_identity` (already closed, generic) and
    `u4 < c3`, omega gives c3 = u4 + 1.

    Pure Nat. Independent of Knuth-B (#1337). -/
theorem c3_eq_u4_plus_one_from_double_mulsub_addback_bounds
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_abPrime_lt : abPrime_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    c3 = u4 + 1 := by
  have h_id := val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    abPrime_val ms_val a_val b_val s u4 c3 h_mulsub h_addback_combined h_u4_le
  have h_le := c3_le_u4_plus_one_from_identity
    abPrime_val a_val b_val s u4 c3 h_id h_abPrime_lt h_amod_pow_lt
  omega

/-- **B.3: pure-Nat double-addback wrapper** (CLOSED, pure-Nat).

    Mirror of `post1_val_eq_amod_pow_s_pure_nat`. From the double-addback
    Euclidean equations + standard bounds, gives `abPrime_val = a%b * 2^s`.
    Composes:
    - `c3_eq_u4_plus_one_from_double_mulsub_addback_bounds` (above).
    - The val256-identity instantiated with c3 = u4 + 1.

    Independent of Knuth-B (#1337). The Knuth bound is needed only to
    DERIVE `h_mulsub` (with the `(a/b + 2)` factor), not for the algebra. -/
theorem abPrime_val_eq_amod_pow_s_pure_nat
    (abPrime_val ms_val a_val b_val s u4 c3 : Nat)
    (h_mulsub : c3 * 2^256 + (a_val * 2^s - u4 * 2^256) =
                ms_val + (a_val / b_val + 2) * (b_val * 2^s))
    (h_addback_combined : abPrime_val + 2^256 = ms_val + 2 * (b_val * 2^s))
    (h_u4_le : u4 * 2^256 ≤ a_val * 2^s)
    (h_abPrime_lt : abPrime_val < 2^256)
    (h_amod_pow_lt : a_val % b_val * 2^s < 2^256)
    (h_u4_lt_c3 : u4 < c3) :
    abPrime_val = a_val % b_val * 2^s := by
  have h_c3_eq := c3_eq_u4_plus_one_from_double_mulsub_addback_bounds
    abPrime_val ms_val a_val b_val s u4 c3
    h_mulsub h_addback_combined h_u4_le h_abPrime_lt h_amod_pow_lt h_u4_lt_c3
  have h_id := val256_abPrime_low4_eq_mod_times_pow_s_plus_c3_minus_one_minus_u4
    abPrime_val ms_val a_val b_val s u4 c3 h_mulsub h_addback_combined h_u4_le
  rw [h_c3_eq] at h_id
  omega

end EvmAsm.Evm64
