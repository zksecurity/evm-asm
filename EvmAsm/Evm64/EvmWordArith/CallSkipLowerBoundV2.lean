/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

  Replacement for PR #1154 (closed). Proves the call-skip exact lower bound
  `val256(a)/val256(b) ≤ (div128Quot u4 u3 b3').toNat` under shift_nz + hcall
  + hskip, via a **GLOBAL Phase 1+2 compensation argument** instead of the
  per-phase tight bounds that PR #1154 attempted.

  Background (why per-phase fails): see
  `memory/project_knuth_b_lower_large_rhatc.md`. Under `rhatc ≥ 2^32`, the
  Phase 1b `BitVec.ult` check can fire on a false alarm (truncation via
  `halfword_combine_mod`), producing `q1' = q_true_1 - 1`. So per-phase
  tight `q1' ≥ q_true_1` is FALSE. The overall Knuth bound
  `qHat ≥ q_true_full` holds only because Phase 2 compensates Phase 1
  undershoots — a global, not per-phase, property.

  This file's target:

      theorem div128Quot_call_skip_ge_val256_div :
          val256(a) / val256(b) ≤ (div128Quot u4 u3 b3').toNat

  Decomposition (all currently sorry'd):

  1. **Setup (PORTED from PR #1154)**: shift bounds (`u4 < 2^63`, `b3' ≥ 2^63`,
     `dHi' ≥ 2^31`, `dHi' < 2^32`, `dLo' < 2^32`), `u4 < b3'` from hcall.
     These are strategy-agnostic and valid.

  2. **`div128Quot_output_ge_q_true_triple`** (NEW, core lemma): at the
     NORMALIZED Word level,
        `(div128Quot u4 u3 b3').toNat ≥ q_true_triple`
     where `q_true_triple := (u4.toNat * 2^64 + u3.toNat * 2^32 + un0Placeholder) / b3'.toNat`.

     This is the GLOBAL argument. Proof strategy (to be built):
     (a) Case on whether Phase 1 undershoots (false alarm in large-rhatc).
     (b) Under "normal" case (no undershoot), per-phase bounds give the result.
     (c) Under undershoot: un21 after Phase 1 is `actual_un21 + vTop`. Phase 2
         operating on this larger un21 computes a q0' that is `q_true_0 + 2^32`
         (overshoot by 2^32). But `(q1' << 32) ||| q0'` uses q0' mod 2^32, so the
         overshoot falls off. After combine, qHat = (q1'+1) * 2^32 + (q0' - 2^32)
         (schematically) — the net result EQUALS what tight-Phase-1 would produce.

  3. **`q_true_triple_ge_q_true_full_normalized`**: bridge from the triple-digit
     trial to `val256(a_norm) / val256(b_norm)`. Uses the Knuth observation:
     truncating the numerator by dropping low digits can only REDUCE the quotient.
     So `q_true_triple ≥ val256(a_norm) / val256(b_norm)`.

     Wait — this is BACKWARDS. `q_true_triple` uses TOP 3 digits of a_norm;
     truncation goes DOWNWARD (drops low part), so q_true_triple ≤ val256(a_norm)/val256(b_norm)?
     Need to check. Actually for integer division, dropping low bits of numerator
     decreases it, so the quotient decreases. So q_true_triple ≤ val256/val256.

     So Lemma 2 (qHat ≥ q_true_triple) + (q_true_triple ≤ val256/val256) gives...
     nothing useful. That's the WRONG direction.

     Revised approach: instead use Knuth's Piece A (`knuth_theorem_b_from_clz`),
     which gives `q_true_triple ≤ val256(a) / val256(b) + 2`. Together with
     Knuth-B LOWER (qHat ≥ q_true_triple - 0 ... or q_true_triple - 2?), we
     piece together qHat ≥ val256/val256.

     Actually the cleanest statement of Knuth-B: qHat ∈ [q_true_full - 0,
     q_true_triple + 2] where q_true_full = floor(val256(a_norm)/val256(b_norm))
     and q_true_triple = floor((u4*2^64 + un3*2^32 + un2)/b3'). Under
     normalization these differ by at most 2. So qHat is within 2 of the true
     full quotient.

     For the LOWER direction, qHat ≥ q_true_full is needed. This is what Knuth
     proves as Theorem B (together with the upper `≤ q_true_full + 2`). The
     lower direction IS the hard part — this file tackles it.

  4. **`val256_ratio_normalized_eq_val256_ratio`** (already exists in part):
     `val256(a_norm) / val256(b_norm) = val256(a) / val256(b)` — trivial, both
     are multiplied by 2^shift.

  5. **Main theorem** composes: qHat ≥ q_true_full ≥ val256(a_norm)/val256(b_norm)
     = val256(a)/val256(b). Done.

  The true "deep" piece is Lemma 2. Everything else is composition.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

-- =============================================================================
-- Setup (ported from PR #1154 — strategy-agnostic)
--
-- - `b3_prime_ge_pow63`: normalized top-limb b3' ≥ 2^63. Already exists.
-- - `u_top_lt_pow63_of_shift_nz`: u4 < 2^63 under shift_nz. Already exists.
-- - `isCallTrialN4_toNat_lt`: u4 < b3' from hcall. Already exists.
--
-- No port needed; directly cite the existing infrastructure at call sites.
-- =============================================================================

-- =============================================================================
-- Core lower bound (SORRY — the deep math)
-- =============================================================================

/-- **Knuth-B lower direction (global)**. At the normalized Word level,
    `div128Quot`'s output is at least the true normalized quotient.

    This is the heart of the call-skip lower bound. The proof can't be
    factored through per-phase bounds (see file header); it requires a
    global analysis that:
    (a) bounds what Phase 1 produces in both normal and false-alarm cases,
    (b) tracks how Phase 2 compensates a Phase 1 undershoot via an
        off-by-2^32 adjustment that cancels in the final halfword combine.

    **TODO**: core proof (~500 lines). -/
theorem div128Quot_ge_q_true_normalized
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    -- Claim: qHat ≥ (u4 * 2^32 + (u3 >>> 32)) / (b3' >>> 32)... but that's
    -- not quite q_true_full. The right statement uses val256 of the full
    -- normalized dividend / val256(b_norm), but those aren't single Words.
    -- Simpler abstract form: at the 128/64 level,
    --   qHat ≥ (u4 * 2^64 + u3.toNat) / b3'.toNat
    -- captures Knuth-B's lower direction for the immediate algorithm inputs.
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
      (div128Quot u4 u3 b3').toNat := by
  sorry

-- =============================================================================
-- Bridge to val256
-- =============================================================================

/-- The normalized 128/64 true quotient matches `val256(a_norm) / val256(b_norm)`
    up to `u4 * 2^64`. Compositions under shift_nz:

      (u4 * 2^64 + u3) / b3' ≈ val256(a_norm_low4) / val256(b_norm) + u4-adjustment.

    **TODO**: careful val256 decomposition + u4 arithmetic. -/
theorem q_true_triple_bridge_to_val256_norm
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    -- val256(a) / val256(b) ≤ (u4 * 2^64 + u3) / b3' is claimed here:
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat := by
  sorry

-- =============================================================================
-- Main theorem (composition)
-- =============================================================================

/-- **Call-skip exact lower bound** (the target of PR #1154 replacement).
    Under shift_nz + hcall + hskip + hbnz,
    `val256(a) / val256(b) ≤ (div128Quot u4 u3 b3').toNat`.

    Proof: compose `q_true_triple_bridge_to_val256_norm` (bridge) with
    `div128Quot_ge_q_true_normalized` (core) via `Nat.le_trans`. Both
    sub-lemmas are currently `sorry`. -/
theorem div128Quot_call_skip_ge_val256_div_v2
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (_hskip : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3
  -- Step 1: Bridge to the normalized triple-digit quotient.
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  simp only [] at h_bridge
  -- Step 2: Core Knuth-B lower bound.
  -- Need `b3' ≥ 2^63` and `u4 < b3'`:
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_core := div128Quot_ge_q_true_normalized u4 u3 b3' h_b3'_ge h_u4_lt_b3'
  -- Step 3: Transitivity.
  exact Nat.le_trans h_bridge h_core

end EvmAsm.Evm64
