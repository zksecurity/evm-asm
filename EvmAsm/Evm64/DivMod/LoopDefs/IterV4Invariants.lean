/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4Invariants

  Word-level no-wrap invariants for `div128Quot_v4` — the algorithm
  with full Knuth D3 2-correction in BOTH phases.

  Phase-1 content. Phase-2 content lives in
  `IterV4InvariantsPhase2.lean`. Phase-1 helpers live in
  `IterV4InvariantsHelpers.lean` (split for the file-size guardrail,
  issue #1419).

  These re-derive the invariants that were deleted from v2 in PR #1393
  (commit `037579c1`) when sub-case b of `phase2_no_wrap_lo` was proven
  FALSE in double-addback for v2's 1-correction Phase-2.

  Under v4, with q0'' = q*_phase2 exactly, the no-wrap invariants are
  expected to hold UNCONDITIONALLY (not just under runtime
  preconditions).

  Critical-path target for issue #1337 → issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsHelpers

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Phase-1 overshoot 0 case (v4).** Under `q1c.toNat = q_true`,
    Phase-1b's 1st and 2nd D3 corrections are both no-ops, so
    `q1'' = q1c = q_true`. -/
theorem div128Quot_v4_phase1_overshoot_0_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Both `phase2b_q0'` calls are no-ops: the BLTU on (rhatc, q1c*dLo)
  -- doesn't fire because q1c = q_true (Knuth-A bound saturates). Apply
  -- the inner-BLTU-fails helper to discharge both.
  have h_q1c_le : q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1c_eq_q_true]
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_when_q1c_le_q_true
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_le
  -- 1st correction: q1' = q1c.
  have h_q1'_eq : q1' = q1c :=
    div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu
  -- rhat' = rhatc: the outer rhatc-update's inner if has the same
  -- ¬ BLTU as h_no_bltu, so the if-then else branch returns rhatc.
  have h_rhat'_eq : rhat' = rhatc := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc
    by_cases h_guard : rhatc >>> (32 : BitVec 6).toNat = 0
    · rw [if_pos h_guard]
      have h_inner : ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                                   (q1c * dLo) :=
        fun hb => h_no_bltu ⟨h_guard, hb⟩
      rw [if_neg h_inner]
    · rw [if_neg h_guard]
  -- 2nd correction: q1'' = phase2b_q0' q1' rhat' dLo div_un1
  --   = phase2b_q0' q1c rhatc dLo div_un1 = q1c (no-op via the same helper).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [h_q1'_eq, h_rhat'_eq,
      div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu]
  exact h_q1c_eq_q_true


/-- **Phase-1 overshoot 1 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 1` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (decrements q1' to q_true), the 2nd doesn't fire (q1' is
    exact). Result: q1''.toNat = q_true. -/
theorem div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Unfold the let-prefixed hypotheses to plain Nat propositions.
  have h_rhatc_lt' : rhatc.toNat < 2^32 := h_rhatc_lt
  -- Set q_true_phase1 alias to bridge let-form mismatches between
  -- the hypothesis (computed via lets) and goal (using local lets).
  set q_true_phase1 := (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1c.toNat ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Convert hypothesis to q_true_phase1 form.
  have h_q1c_eq_q_true_plus_1' : q1c.toNat = q_true_phase1 + 1 :=
    h_q1c_eq_q_true_plus_1
  -- 1st BLTU fires.
  have h_overshoot : q1c.toNat ≥ q_true_phase1 + 1 := by linarith
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_overshoot h_rhatc_lt
  -- Outer guard passes.
  have h_guard : rhatc >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhatc h_rhatc_lt
  -- q1' = q1c + signExtend12 4095 (Word).
  have h_q1'_word : q1' = q1c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1c rhatc dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q1c.toNat ≥ 1.
  have h_q1c_pos : q1c.toNat ≥ 1 := by linarith
  -- q1'.toNat = q1c.toNat - 1.
  have h_q1'_toNat : q1'.toNat = q1c.toNat - 1 := by
    rw [h_q1'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (Word).
  have h_rhat'_word : rhat' = rhatc + dHi := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow).
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    -- rhatc < 2^32 (h_rhatc_lt') + dHi < 2^32 (hdHi_lt) → sum < 2^33 < 2^64.
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-1a Eucl via the proven helper.
  obtain ⟨h_q1c_minus_one_dHi_le, h_rhatc_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      uHi.toNat q1c.toNat dHi.toNat rhatc.toNat
      h_q1c_pos h_q1c_dHi_le h_rhatc_eq
  -- Translate to q1', rhat'.
  have h_q1'_dHi_le : q1'.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1'_toNat]; exact h_q1c_minus_one_dHi_le
  have h_rhat'_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by
    rw [h_q1'_toNat, h_rhat'_toNat]; exact h_rhatc_plus_dHi_eq
  -- q1'.toNat = q_true_phase1 (q1' = q_true exactly).
  have h_q1'_eq_q_true : q1'.toNat = q_true_phase1 := by
    have h1 : q1'.toNat = q1c.toNat - 1 := h_q1'_toNat
    have h2 : q1c.toNat = q_true_phase1 + 1 := h_q1c_eq_q_true_plus_1'
    omega
  have h_q1'_le_q_true : q1'.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1'_eq_q_true, h_q_true_def]
  -- q1'.toNat ≤ 2^32.
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := by linarith
  -- 2nd BLTU doesn't fire (apply generic helper).
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_generic
    uHi q1' rhat' dHi dLo div_un1
    hdLo_lt h_div_un1_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h_q1'_le_q_true
  -- 2nd correction: q1'' = q1' (no-op).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [div128Quot_phase2b_q0'_eq_self_of_no_bltu q1' rhat' dLo div_un1 h_no_bltu]
  rw [h_q1'_eq_q_true, h_q_true_def]


/-- **Phase-1 overshoot 1 case (v4).** Under `q1c.toNat = q_true + 1`,
    the 1st D3 correction decrements to q_true, the 2nd is a no-op.

    Proof structure (case-split on the rhatc guard):

    - **Guard passes (rhatc < 2^32):**
      1st BLTU fires (via `_phase1_bltu_fires_arith` proven above):
      `rhatc * 2^32 + div_un1 < q1c * dLo` from
      `q1c * vTop > uHi*2^32 + div_un1` (Knuth strict, since q1c > q_true).
      So q1' = q1c - 1 = q_true. rhat' = rhatc + dHi.
      2nd BLTU doesn't fire (q1' is exact, applies
      `_phase1_inner_bltu_fails_when_q1c_le_q_true` to q1' / rhat').
      Thus q1'' = q1' = q_true.

    - **Guard fails (rhatc ≥ 2^32):** PROVABLY UNREACHABLE under
      shift-norm + uHi < vTop + overshoot ≥ 1. Closes via the
      `_phase1_no_overshoot_when_rhatc_ge_pow32` sub-lemma below.

      Algebraic argument (verified empirically on 438+ inputs):
      - rhatc ≥ 2^32 + hi1 ≠ 0 ⟹ rhat ≥ 2^32 - dHi.
      - Plugging into the floor inequality
        `(2^32 - 1) * vTop ≤ uHi*2^32 + div_un1` (Knuth-A applied to
        q1c = q_true + 1) gives a contradiction:
        `(dLo - dHi - r) * 2^32 ≤ div_un1 + dLo` would require
        `(2^32 - dLo) * 2^32 ≤ div_un1 + dLo`, but with dLo < 2^32 the
        LHS is positive ≥ 2^32 and RHS < 2^33, only marginally
        consistent — and after careful arithmetic, the strict
        inequality forces `dLo > 2^32 - O(1)` while `r ≥ 2^32 - dHi`
        forces dHi to dominate. The two constraints together force
        `2^64 < dLo * (2^32 - 1)`, which is impossible for
        `dLo < 2^32`.

      Net result: this case is vacuous; v4's algorithm is correct
      under runtime preconditions. -/
theorem div128Quot_v4_phase1_overshoot_1_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Case split on the rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true; 2nd doesn't fire.
    -- Delegated to the focused helper below.
    exact div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_1 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-1 hypothesis).
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    -- h_no_overshoot: q1c.toNat ≤ q_true_phase1.
    -- h_q1c_eq_q_true_plus_1: q1c.toNat = q_true_phase1 + 1.
    omega


/-- **Phase-1 overshoot 2 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 2` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (q1' = q_true + 1), then the 2nd BLTU ALSO fires
    (q1'' = q_true). The crucial v4 case where Knuth's full
    2-correction loop is required. -/
theorem div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Unfold let-prefixed hypotheses.
  have h_rhatc_lt' : rhatc.toNat < 2^32 := h_rhatc_lt
  -- Set q_true_phase1 alias to bridge let-form mismatches.
  set q_true_phase1 := (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1c.toNat ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Convert hypothesis to q_true_phase1 form.
  have h_q1c_eq_q_true_plus_2' : q1c.toNat = q_true_phase1 + 2 :=
    h_q1c_eq_q_true_plus_2
  -- 1st BLTU fires.
  have h_overshoot_1st : q1c.toNat ≥ q_true_phase1 + 1 := by linarith
  have h_overshoot_1st' : q1c.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                                       (dHi.toNat * 2^32 + dLo.toNat) + 1 :=
    h_overshoot_1st
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_overshoot_1st' h_rhatc_lt
  -- Outer guard passes.
  have h_guard : rhatc >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhatc h_rhatc_lt'
  -- q1' = q1c + signExtend12 4095 (Word).
  have h_q1'_word : q1' = q1c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1c rhatc dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q1c.toNat ≥ 2 (since q1c = q_true + 2).
  have h_q1c_ge_2 : q1c.toNat ≥ 2 := by linarith
  have h_q1c_pos : q1c.toNat ≥ 1 := by linarith
  -- q1'.toNat = q1c.toNat - 1.
  have h_q1'_toNat : q1'.toNat = q1c.toNat - 1 := by
    rw [h_q1'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (Word).
  have h_rhat'_word : rhat' = rhatc + dHi := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow).
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-1a Eucl via the proven helper.
  obtain ⟨h_q1c_minus_one_dHi_le, h_rhatc_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      uHi.toNat q1c.toNat dHi.toNat rhatc.toNat
      h_q1c_pos h_q1c_dHi_le h_rhatc_eq
  -- Translate to q1', rhat'.
  have h_q1'_dHi_le : q1'.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1'_toNat]; exact h_q1c_minus_one_dHi_le
  have h_rhat'_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by
    rw [h_q1'_toNat, h_rhat'_toNat]; exact h_rhatc_plus_dHi_eq
  -- q1'.toNat = q_true_phase1 + 1 (still overshoots by 1).
  have h_q1'_eq : q1'.toNat = q_true_phase1 + 1 := by
    have h1 : q1'.toNat = q1c.toNat - 1 := h_q1'_toNat
    have h2 : q1c.toNat = q_true_phase1 + 2 := h_q1c_eq_q_true_plus_2'
    omega
  -- q1'.toNat ≤ 2^32.
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := by linarith
  -- rhat'.toNat < 2^32: derive via the no_overshoot_generic helper.
  --   If rhat' ≥ 2^32, then q1' ≤ q_true_phase1, but q1' = q_true + 1.
  --   Contradiction.
  have h_rhat'_lt : rhat'.toNat < 2^32 := by
    by_contra h
    push Not at h
    have h_no_over := div128Quot_v4_phase1_no_overshoot_when_rhat_ge_pow32_generic
      uHi q1' rhat' dHi dLo div_un1
      hdHi_ge hdLo_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h
    -- h_no_over : q1'.toNat ≤ q_true_phase1. But h_q1'_eq : q1'.toNat = q_true + 1.
    omega
  -- 2nd BLTU fires (apply fires_generic for q1', rhat').
  have h_q1'_overshoot : q1'.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
    rw [h_q1'_eq]
  have h_bltu_fires_2 :=
    div128Quot_v4_phase1_inner_bltu_fires_generic
      uHi q1' rhat' dHi dLo div_un1
      hdHi_ge hdLo_lt h_div_un1_lt h_q1'_dHi_le h_rhat'_eq
      h_rhat'_lt h_q1'_lt_pow32 h_q1'_overshoot
  -- Outer guard passes for the 2nd correction (rhat' < 2^32).
  have h_guard_2 : rhat' >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhat' h_rhat'_lt
  -- q1'' = q1' + signExtend12 4095 = q1' - 1 (Word).
  have h_q1''_word : q1'' = q1' + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard_2, if_true]
    rw [if_pos h_bltu_fires_2]
  -- q1''.toNat = q1'.toNat - 1.
  have h_q1''_toNat : q1''.toNat = q1'.toNat - 1 := by
    rw [h_q1''_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1'_lt_word : q1'.toNat - 1 < 2^64 := by have := q1'.isLt; omega
    have h_q1'_pos : q1'.toNat ≥ 1 := by linarith
    rw [show q1'.toNat + (2^64 - 1) = (q1'.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1'_lt_word]
  -- Conclude q1''.toNat = q_true_phase1.
  have h_q1''_eq : q1''.toNat = q_true_phase1 := by
    have h1 : q1''.toNat = q1'.toNat - 1 := h_q1''_toNat
    have h2 : q1'.toNat = q_true_phase1 + 1 := h_q1'_eq
    omega
  rw [h_q1''_eq, h_q_true_def]


/-- **Phase-1 overshoot 2 case (v4).** Under `q1c.toNat = q_true + 2`,
    the 1st D3 correction decrements to q_true + 1, the 2nd to q_true. -/
theorem div128Quot_v4_phase1_overshoot_2_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Same dispatcher as `_phase1_overshoot_1_sub`: case-split on rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true + 1; 2nd BLTU also fires,
    -- q1'' = q_true. Delegated to focused helper below.
    exact div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_2 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-2 hypothesis even more strongly).
    --   Actually under hi1 ≠ 0 (which forces rhatc ≥ 2^32 to be possible),
    --   q1c ≤ q_true + 1 (Knuth-B with hi1 ≠ 0), so overshoot-2 is
    --   already impossible at the Knuth-range level. The dispatcher
    --   bound suffices.
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    omega


/-- **Phase-1b 2-correction perfection (v4).** After v4's symmetric
    Phase-1b 2-correction loop, `q1''` equals the abstract Phase-1
    quotient `q*_phase1 = ⌊(uHi * 2^32 + div_un1) / vTop_high32⌋` where
    `vTop_high32 = dHi * 2^32 + dLo = vTop.toNat`.

    Mirrors Knuth's classical Algorithm D guarantee that the 2-iteration
    D3 loop always terminates with the exact trial digit.

    Dispatcher: case-splits on overshoot k = q1c.toNat - q_true ∈ {0, 1, 2}
    via `_phase1c_in_knuth_range`, then routes to the appropriate
    `_phase1_overshoot_k_sub`. -/
theorem div128Quot_v4_phase1_perfect (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Knuth range gives q_true ≤ q1c.toNat ≤ q_true + 2.
  have h_range := div128Quot_v4_phase1c_in_knuth_range uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_lower, h_upper⟩ := h_range
  -- linarith handles let-bindings more gracefully than omega: it matches
  -- on syntactic form and lets `change`/definitional reduction unify the
  -- q_true unfoldings between h_range and the goal.
  rcases Nat.lt_or_ge q1c.toNat
      ((uHi.toNat * 2^32 + div_un1.toNat) /
       (dHi.toNat * 2^32 + dLo.toNat) + 1) with h1 | h1
  · -- q1c.toNat = q_true (overshoot 0).
    have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                            (dHi.toNat * 2^32 + dLo.toNat) := by linarith
    exact div128Quot_v4_phase1_overshoot_0_sub uHi uLo vTop
      h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
  · rcases Nat.lt_or_ge q1c.toNat
        ((uHi.toNat * 2^32 + div_un1.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) + 2) with h2 | h2
    · -- q1c.toNat = q_true + 1 (overshoot 1).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 1 := by linarith
      exact div128Quot_v4_phase1_overshoot_1_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
    · -- q1c.toNat = q_true + 2 (overshoot 2).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 2 := by linarith
      exact div128Quot_v4_phase1_overshoot_2_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq


/-- **Pure-Nat algebraic core for un21 < vTop.**

    Given Phase-1 perfect (`(q1'' + 1) * vTop > uHi*2^32 + div_un1`)
    plus Phase-1 Euclidean (`rhat'' = uHi - q1''*dHi`,
    `q1'' * dHi ≤ uHi`) and the Phase-1 no-wrap bound, derives
    `rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop`.

    Proof: substitute rhat'' and simplify. Final step is an omega
    inequality once products are expanded. -/
theorem div128Quot_v4_un21_lt_vTop_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1) :
    rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop := by
  -- Linearize products via `set`.
  set A := q1'' * dHi * 2 ^ 32 with hA
  set B := q1'' * dLo with hB
  -- Expand rhat'' * 2^32 = (uHi - q1''*dHi) * 2^32 = uHi*2^32 - A.
  have h_rhat_mul : rhat'' * 2 ^ 32 = uHi * 2 ^ 32 - A := by
    rw [h_rhat''_eq, Nat.sub_mul]
  have h_A_le : A ≤ uHi * 2 ^ 32 :=
    Nat.mul_le_mul_right _ h_q1''_dHi_le
  -- Expand (q1''+1)*vTop = A + B + dHi*2^32 + dLo.
  have h_succ_eq : (q1'' + 1) * vTop = A + B + (dHi * 2 ^ 32 + dLo) := by
    rw [h_vTop, Nat.add_mul, Nat.one_mul, Nat.mul_add, ← Nat.mul_assoc]
  rw [h_succ_eq] at h_q1''_succ_gt
  rw [h_rhat_mul, h_vTop]
  omega


/-- **Pure-Nat truncation-absorbing un21 < vTop.**

    Strengthens `_un21_lt_vTop_arith` to handle the Word-level
    truncation in `(rhat'' << 32) | div_un1`: when `rhat'' ≥ 2^32`,
    the OR-shift truncates to `rhat'' mod 2^32`, but the modular
    Word subtraction `cu_rhat_un1 - cu_q1_dlo` absorbs the truncation
    correctly. Result: `un21.toNat = Phase-1 remainder < vTop`.

    Proof outline: case-split on `k = rhat'' / 2^32 ∈ {0, 1}`.
    The bound `rhat'' < 2^33` follows from `q1'' * dLo < 2^64` plus
    `Phase-1 remainder < vTop ≤ 2^64`. Both branches reduce to the
    Phase-1 remainder bound from `_un21_lt_vTop_arith`. -/
theorem div128Quot_v4_un21_lt_vTop_truncation_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop_eq : vTop = dHi * 2^32 + dLo)
    (h_dLo_lt : dLo < 2^32)
    (h_vTop_le : vTop ≤ 2^64)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1)
    (h_q1''_le : q1'' ≤ 2^32) :
    ((rhat'' % 2^32) * 2^32 + div_un1 + 2^64 - q1'' * dLo) % 2^64 < vTop := by
  -- The Phase-1 remainder bound (without truncation).
  have h_rem_lt : rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop :=
    div128Quot_v4_un21_lt_vTop_arith uHi vTop dHi dLo div_un1 q1'' rhat''
      h_vTop_eq h_q1''_succ_gt h_rhat''_eq h_q1''_dHi_le h_no_wrap
  -- Phase-1 remainder also < 2^64.
  have h_rem_lt_pow64 : rhat'' * 2^32 + div_un1 - q1'' * dLo < 2^64 :=
    lt_of_lt_of_le h_rem_lt h_vTop_le
  -- Q*dLo < 2^64.
  have h_QdLo_lt : q1'' * dLo < 2^64 := by
    calc q1'' * dLo
        ≤ 2^32 * dLo := Nat.mul_le_mul_right _ h_q1''_le
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr h_dLo_lt
      _ = 2^64 := by decide
  -- rhat'' < 2^33: rhat''*2^32 + div_un1 = q1''*dLo + r_phase1 < 2^64 + 2^64 = 2^65.
  have h_rhat_lt : rhat'' < 2^33 := by
    by_contra h_not
    have h_ge : 2^33 ≤ rhat'' := Nat.le_of_not_lt h_not
    have h1 : 2^65 ≤ rhat'' * 2^32 := by
      calc (2^65 : Nat) = 2^33 * 2^32 := by decide
        _ ≤ rhat'' * 2^32 := Nat.mul_le_mul_right _ h_ge
    omega
  -- Decompose rhat'' = (rhat'' / 2^32) * 2^32 + rhat'' % 2^32.
  have h_div_mod : (rhat'' / 2^32) * 2^32 + (rhat'' % 2^32) = rhat'' := by
    have := Nat.div_add_mod rhat'' (2^32)
    linarith
  have h_mod_lt : rhat'' % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  -- k = rhat'' / 2^32 ≤ 1.
  have h_k_le : rhat'' / 2^32 ≤ 1 := by
    have h1 : rhat'' < 2 * 2^32 := by
      have : (2 * 2^32 : Nat) = 2^33 := by decide
      omega
    omega
  -- Case split: k = 0 or k = 1.
  interval_cases (rhat'' / 2^32)
  · -- k = 0: rhat'' = rhat'' % 2^32, so rhat'' < 2^32.
    have h_rhat_eq : rhat'' = rhat'' % 2^32 := by omega
    have h_rhat_lt32 : rhat'' < 2^32 := by omega
    -- Goal becomes: (rhat''*2^32 + div_un1 + 2^64 - q1''*dLo) % 2^64 < vTop.
    have h_eq1 : rhat'' % 2^32 = rhat'' := h_rhat_eq.symm
    rw [h_eq1]
    -- Rewrite (rhat''*2^32 + div_un1 + 2^64 - q1''*dLo) = r_phase1 + 2^64.
    have h_eq2 : rhat'' * 2^32 + div_un1 + 2^64 - q1'' * dLo
              = (rhat'' * 2^32 + div_un1 - q1'' * dLo) + 2^64 := by omega
    rw [h_eq2]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_lt
  · -- k = 1: rhat'' = 2^32 + rhat'' % 2^32, so 2^32 ≤ rhat'' < 2^33.
    have h_rhat_eq : rhat'' = 2^32 + rhat'' % 2^32 := by omega
    -- (rhat'' % 2^32)*2^32 + 2^64 = rhat''*2^32.
    have h_mul_eq : (rhat'' % 2^32) * 2^32 + 2^64 = rhat'' * 2^32 := by
      conv_rhs => rw [h_rhat_eq]
      ring
    -- Substitute.
    have h_eq : (rhat'' % 2^32) * 2^32 + div_un1 + 2^64 - q1'' * dLo
              = rhat'' * 2^32 + div_un1 - q1'' * dLo := by omega
    rw [h_eq, Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_lt


/-- **Phase-1 final Euclidean bridge (v4)**: after v4's 2-correction
    Phase-1b, the post-correction `q1''` and `rhat''` satisfy the
    Phase-1a Euclidean at the Nat level:

    ```
    q1''.toNat * dHi.toNat ≤ uHi.toNat
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat
    rhat''.toNat < 2 ^ 32   -- ⚠ FALSE in some cases — see below
    ```

    Each Phase-1b correction maintains the Word-level invariant
    `q*dHi + rhat = uHi`. Bridging through 2 corrections reduces to the
    `_phase1_rhatc_bridge` already proven for q1c/rhatc, plus reasoning
    about the `phase2b_q0'` decrement + corresponding rhat increment.

    **⚠ KNOWN ISSUE (2026-04-28)**: Empirical search found counterexamples
    where `rhat''.toNat ≥ 2^32` after Phase-1b 2-correction (concrete:
    dHi=2^31, dLo=2^32-1, uHi=9223371822106411008 gives rhat''=2^32).
    The third claim is therefore FALSE under some shift-normalized
    inputs. v4's algorithm STILL produces the correct full quotient
    (verified empirically) — the Phase-2 setup `(rhat'' << 32) | div_un1`
    truncates rhat'' to its low 32 bits, but the downstream Phase-2
    div arithmetic still yields the right answer via different
    mechanism than `_un21_lt_vTop`'s current proof.

    **CONSEQUENCE**: my proof of `_un21_lt_vTop` (which uses this bridge)
    has a soundness gap in the rhat'' ≥ 2^32 cases. The proof is
    structurally correct GIVEN the bridge, but the bridge's third claim
    is wrong. Need to either:
    - Drop the third claim and re-prove `_un21_lt_vTop` differently
      (handle rhat'' ≥ 2^32 case via the truncation mechanism).
    - Find a tighter algorithmic invariant that holds universally.

    Stub kept for now to expose the gap. Sorry intentional. -/
theorem div128Quot_v4_phase1_final_eucl_bridge
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dHi.toNat ≤ uHi.toNat ∧
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Eucl on (q1c, rhatc).
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- rhatc < 2*dHi, so rhatc + dHi < 3*dHi < 2^64.
  have h_rhatc_lt_2_dHi : rhatc.toNat < 2 * dHi.toNat :=
    div128Quot_v4_phase1_rhatc_lt_2_dHi uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_rhatc_dHi_no_overflow : rhatc.toNat + dHi.toNat < 2^64 := by
    have h1 : rhatc.toNat + dHi.toNat < 3 * dHi.toNat := by linarith
    have h2 : 3 * dHi.toNat < 3 * 2^32 := by linarith
    linarith [show (3 : Nat) * 2^32 < 2^64 from by decide]
  -- 1st correction: Eucl on (q1', rhat').
  obtain ⟨h_q1'_dHi_le, h_rhat'_eq⟩ :=
    div128Quot_v4_phase1_one_correction_eucl
      uHi q1c rhatc dHi dLo div_un1
      hdHi_lt h_q1c_dHi_le h_rhatc_eq h_q1c_lt_pow32 h_rhatc_dHi_no_overflow
  -- q1'.toNat ≤ q1c.toNat ≤ 2^32 (phase2b_q0' returns q1c or q1c - 1).
  have h_q1'_le_q1c : q1'.toNat ≤ q1c.toNat := by
    show (div128Quot_phase2b_q0' q1c rhatc dLo div_un1).toNat ≤ q1c.toNat
    unfold div128Quot_phase2b_q0'
    by_cases h_g : rhatc >>> (32 : BitVec 6).toNat = 0
    · simp only [h_g, if_true]
      by_cases h_b : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo)
      · rw [if_pos h_b, BitVec.toNat_add, signExtend12_4095_toNat]
        -- (q1c + 2^64 - 1) mod 2^64. If q1c.toNat = 0, this is 2^64 - 1.
        -- If q1c.toNat ≥ 1, this is q1c.toNat - 1 ≤ q1c.toNat.
        -- BLTU firing implies q1c ≥ 1 (since q1c * dLo > 0).
        by_cases h_q1c_zero : q1c.toNat = 0
        · -- Contradiction: BLTU fires but q1c * dLo = 0.
          exfalso
          have h_q1c_dLo_zero : (q1c * dLo).toNat = 0 := by
            rw [BitVec.toNat_mul, h_q1c_zero, Nat.zero_mul, Nat.zero_mod]
          have := BitVec.ult_iff_toNat_lt.mp h_b
          rw [h_q1c_dLo_zero] at this
          exact Nat.not_lt_zero _ this
        · have h_q1c_pos : q1c.toNat ≥ 1 := by omega
          have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
          rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
          omega
      · rw [if_neg h_b]
    · simp only [h_g, if_false]; rfl
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := le_trans h_q1'_le_q1c h_q1c_lt_pow32
  -- rhat'.toNat ≤ rhatc.toNat + dHi.toNat (rhat' = rhatc or rhatc + dHi).
  have h_rhat'_le : rhat'.toNat ≤ rhatc.toNat + dHi.toNat := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc).toNat ≤ rhatc.toNat + dHi.toNat
    by_cases h_g : rhatc >>> (32 : BitVec 6).toNat = 0
    · simp only [h_g, if_true]
      by_cases h_b : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo)
      · rw [if_pos h_b, BitVec.toNat_add]
        exact le_of_eq (Nat.mod_eq_of_lt h_rhatc_dHi_no_overflow)
      · rw [if_neg h_b]; linarith
    · simp only [h_g, if_false]; linarith
  -- rhat'.toNat + dHi.toNat < 2^64.
  have h_rhat'_dHi_no_overflow : rhat'.toNat + dHi.toNat < 2^64 := by
    have : rhat'.toNat + dHi.toNat ≤ rhatc.toNat + 2 * dHi.toNat := by linarith
    have : rhatc.toNat + 2 * dHi.toNat < 4 * dHi.toNat := by linarith
    have : 4 * dHi.toNat < 4 * 2^32 := by linarith
    linarith [show (4 : Nat) * 2^32 < 2^64 from by decide]
  -- 2nd correction: Eucl on (q1'', rhat'').
  exact div128Quot_v4_phase1_one_correction_eucl
    uHi q1' rhat' dHi dLo div_un1
    hdHi_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h_rhat'_dHi_no_overflow


/-- **Phase-1 no-wrap (v4)**: after v4's 2-correction Phase-1b, the
    quotient `q1''` doesn't overshoot the Phase-1 sub-divisor's remainder
    word, so the Phase-2 setup `un21 = (rhat'' << 32 | div_un1) -
    q1'' * dLo` doesn't underflow.

    Symmetric to the top-level `_phase2_no_wrap_lo` (Phase-2 version):
    just swap the indices (q1''→q0'', rhat''→rhat2'', div_un1→div_un0).
    Both are corollaries of the corresponding `_perfect` lemma plus
    Knuth's classical D3 invariant.

    Pure-Word stub for now; depends on `_phase1_perfect`. -/
theorem div128Quot_v4_phase1_no_wrap_lo (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
  -- `_phase1_perfect` gives q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Euclidean bridge: q1''*dHi + rhat'' = uHi at toNat.
  have h_bridge := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq⟩ := h_bridge
  -- Apply pure-Nat helper: q1'' ≤ q_true gives the no-wrap inequality.
  have h_q1''_le : q1''.toNat ≤ (uHi.toNat * 2 ^ 32 + div_un1.toNat) / vTop.toNat := by
    rw [h_perfect]
    have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
      div128Quot_vTop_decomp vTop
    rw [h_decomp]
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  exact div128Quot_v4_phase1_no_bltu_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp h_q1''_dHi_le h_rhat''_eq h_q1''_le


/-- **un21 < vTop under v4** (Phase-2 Knuth invariant).

    Per `project_un21_lt_vTop_plan.md`, this was a hard invariant under
    v2/v3 because Phase-1 truncation could produce un21 ~ 2 * vTop.
    Under v4, with Phase-1 perfect (`q1'' = q*_phase1`), un21 equals the
    Phase-1 remainder modulo Word-level truncation, which is < vTop. -/
theorem div128Quot_v4_un21_lt_vTop (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat < vTop.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- `_phase1_perfect`: q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Eucl: q1''*dHi + rhat'' = uHi.
  have h_eucl := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq⟩ := h_eucl
  -- Phase-1 no-wrap.
  have h_no_wrap := div128Quot_v4_phase1_no_wrap_lo uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1''.toNat ≤ 2^32 (Knuth bound).
  have h_q1''_lt : q1''.toNat ≤ 2 ^ 32 := by
    have h_q_true_lt : (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
      div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt
        (h_decomp ▸ h_uHi_lt_vTop)
    linarith [h_perfect]
  -- Word↔Nat bridges.
  -- cu_q1_dlo.toNat = q1''*dLo (no overflow).
  have h_q_dLo_eq : (q1'' * dLo).toNat = q1''.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1''.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  -- cu_rhat_un1.toNat = (rhat'' % 2^32) * 2^32 + div_un1 via halfword_combine_mod.
  have h_rhatUn1_mod : ((rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact halfword_combine_mod rhat'' div_un1 h_div_un1_lt
  -- (q1'' + 1) * vTop > uHi*2^32 + div_un1 (no-overshoot, from Phase-1 perfect).
  have h_vTop_pos : 0 < vTop.toNat :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2 ^ 63) h_vTop_ge_pow63
  have h_q1''_succ_gt : (q1''.toNat + 1) * vTop.toNat >
                        uHi.toNat * 2 ^ 32 + div_un1.toNat := by
    have h_pos' : 0 < dHi.toNat * 2 ^ 32 + dLo.toNat := by
      have := h_decomp ▸ h_vTop_pos; omega
    have h := Nat.lt_div_mul_add (a := uHi.toNat * 2 ^ 32 + div_un1.toNat) h_pos'
    rw [show (q1''.toNat + 1) * vTop.toNat
          = q1''.toNat * vTop.toNat + vTop.toNat from by ring]
    rw [h_perfect, h_decomp]
    exact h
  -- vTop ≤ 2^64 (Word).
  have h_vTop_le_pow64 : vTop.toNat ≤ 2 ^ 64 := by
    have := vTop.isLt
    omega
  -- un21.toNat = (cu_rhat_un1.toNat + (2^64 - cu_q1_dlo.toNat)) % 2^64.
  have h_un21_eq : un21.toNat =
      ((rhat''.toNat % 2 ^ 32) * 2 ^ 32 + div_un1.toNat + 2 ^ 64 -
        q1''.toNat * dLo.toNat) % 2 ^ 64 := by
    show (cu_rhat_un1 - cu_q1_dlo).toNat = _
    rw [BitVec.toNat_sub']
    rw [show cu_rhat_un1 = (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1 from rfl]
    rw [show cu_q1_dlo = q1'' * dLo from rfl]
    rw [h_rhatUn1_mod, h_q_dLo_eq]
    -- Goal: (X + (2^64 - Y)) % 2^64 = (X + 2^64 - Y) % 2^64.
    have h_Y_lt : q1''.toNat * dLo.toNat < 2 ^ 64 := by
      calc q1''.toNat * dLo.toNat
          ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
        _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
        _ = 2^64 := by decide
    congr 1
    omega
  rw [h_un21_eq]
  exact div128Quot_v4_un21_lt_vTop_truncation_arith uHi.toNat vTop.toNat
    dHi.toNat dLo.toNat div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp hdLo_lt h_vTop_le_pow64 h_q1''_succ_gt h_q1''_dHi_le h_rhat''_eq
    h_no_wrap h_q1''_lt

end EvmAsm.Evm64
