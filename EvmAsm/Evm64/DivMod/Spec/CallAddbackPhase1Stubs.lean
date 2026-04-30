/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackPhase1Stubs

  Phase-1 division-invariant decomposition stubs for `div128Quot_v2`.
  Extracted from Spec/CallAddback.lean per #1078 / beads evm-asm-aor to
  trim the 4369-line CallAddback.lean below the file-size cap.

  Contents (purely upstream of the overshoot_{0,1,2}_sub /
  phase1_div_invariant_under_runtime composition that still lives in
  CallAddback.lean):

  - `div128Quot_v2_phase1b_2nd_post` — Phase-1b 2nd D3 Euclidean
    invariant: q1'' * dHi + rhat'' = uHi.
  - `div128Quot_v2_phase1b_check_iff_overshoot_under_runtime` — Stub 2:
    1st BLTU check ⟺ q1c overshoots q* (under rhatc < 2^32).
  - `div128Quot_v2_phase1b_2nd_guard_under_runtime` — Stub 3: rhat' < 2^32
    holds when needed for the 2nd correction guard.
  - `div128Quot_v2_case_0_rhatc_lt_pow32_under_runtime` — case-0 rhatc bound.
  - `div128Quot_v2_q_true_lt_pow32_under_runtime` — q_true < 2^32 under
    runtime preconditions.

  Plus the private pure-Nat helper `phase1b_2nd_guard_arith` consumed
  only by `_2nd_guard_under_runtime` here.

  Issue #1337 algorithm fix migration (decomposition surface).
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgEuclideans
import EvmAsm.Evm64.DivMod.Shift0Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

/-- **Phase 1b 2nd D3 Euclidean invariant** for `div128Quot_v2`.

    The new substantive sub-lemma for v2: after the 2nd D3 correction
    iteration (gated by `rhat' >> 32 = 0`), the Euclidean invariant
    `q1'' * dHi + rhat'' = uHi` is preserved.

    Mirrors `div128Quot_phase1b_post` (KnuthTheoremB.lean:880) but for
    the 2nd correction iteration. The proof structure:
    - Guard taken (rhat' >> 32 ≠ 0): q1'' = q1', rhat'' = rhat',
      invariant carries through unchanged from `div128Quot_phase1b_post`.
    - Guard fall-through (rhat' >> 32 = 0):
      * Check fires (rhatUn1' < qDlo2): q1'' = q1' - 1, rhat'' = rhat' + dHi.
        Same algebra as 1st D3 correction (use `div128Quot_phase1b_correction_eucl`).
      * Check doesn't fire: q1'' = q1', rhat'' = rhat'.

    This sub-lemma plus the corresponding tightness `rhat'' < dHi` (under
    additional preconditions) lets us mirror v1's qHat_vTop_le proof
    without the no_wrap hypotheses (since the 2nd correction handles
    the truncation case that breaks v1).

    Issue #1337 algorithm fix migration. -/
theorem div128Quot_v2_phase1b_2nd_post
    (uHi dHi q1' rhat' dLo div_un1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (h_post_1st : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat) :
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dHi.toNat + rhat''.toNat = uHi.toNat := by
  intro q1'' rhat''
  by_cases h_guard : rhat' >>> (32 : BitVec 6).toNat = 0
  · -- Guard fall-through: case-split on the BLTU check.
    by_cases h_check : BitVec.ult ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1)
                                    (q1' * dLo)
    · -- Check fires: q1'' = q1' - 1, rhat'' = rhat' + dHi.
      have h_q1'' : q1'' = q1' + signExtend12 4095 := by
        show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_guard, if_pos h_check]
      have h_rhat'' : rhat'' = rhat' + dHi := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_pos h_check]
      rw [h_q1'', h_rhat'']
      have h_q1'_pos : q1'.toNat ≥ 1 :=
        div128Quot_phase1b_check_implies_q1c_pos q1' dLo
          ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) h_check
      -- Derive `rhat' < 2 * dHi` inline from h_guard + hdHi_ge.
      have h_rhat'_lt : rhat'.toNat < 2 * dHi.toNat := by
        have h_rhat'_lt_pow32 : rhat'.toNat < 2^32 := by
          have h := congrArg BitVec.toNat h_guard
          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
          have h_word : rhat'.toNat < 2^64 := rhat'.isLt
          omega
        omega
      exact div128Quot_phase1b_correction_eucl uHi dHi q1' rhat'
        hdHi_lt h_post_1st h_q1'_pos h_rhat'_lt
    · -- Check doesn't fire: q1'' = q1', rhat'' = rhat'.
      have h_q1'' : q1'' = q1' := by
        show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_guard, if_neg h_check]
      have h_rhat'' : rhat'' = rhat' := by
        show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
        rw [if_pos h_guard, if_neg h_check]
      rw [h_q1'', h_rhat''];  exact h_post_1st
  · -- Guard taken (rhat' >> 32 ≠ 0): q1'' = q1', rhat'' = rhat'.
    have h_q1'' : q1'' = q1' := by
      show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_guard]
    have h_rhat'' : rhat'' = rhat' := by
      show (if rhat' >>> (32 : BitVec 6).toNat = 0 then _ else rhat') = _
      rw [if_neg h_guard]
    rw [h_q1'', h_rhat'']; exact h_post_1st


/-- Pure-Nat helper for `div128Quot_v2_phase1b_2nd_guard_under_runtime`.

    Captures the algebraic core: from
    - `u4 * 2^32 + div_un1 < A * 2^32 + B` (Knuth-A boundary on q*),
    - `A ≤ u4` (q*+1 ≤ q1c so (q*+1)*dHi ≤ u4),
    - `B + 2^32 ≤ 2^64` (B = (q*+1)*dLo bound),
    conclude `u4 - A < 2^32`.

    Factored out to avoid maxRecDepth issues during elaboration of the
    main theorem (which has many let-zeta bindings). -/
private theorem phase1b_2nd_guard_arith
    (u4 A B div_un1 : Nat)
    (h_x_lt : u4 * 2^32 + div_un1 < A * 2^32 + B)
    (h_A_le_u4 : A ≤ u4)
    (h_B_bound : B + 2^32 ≤ 2^64) :
    u4 - A < 2^32 := by
  set X := u4 * 2^32 with hX
  set Y := A * 2^32 with hY
  have h_sub_mul : (u4 - A) * 2^32 = X - Y := by
    rw [hX, hY, Nat.sub_mul]
  have h_Y_le_X : Y ≤ X := Nat.mul_le_mul_right _ h_A_le_u4
  have h_step : (u4 - A) * 2^32 < B + 2^32 := by
    rw [h_sub_mul]; omega
  set Z := (u4 - A) * 2^32 with hZ
  by_contra h_ge
  push Not at h_ge
  have h_mul : 2^32 * 2^32 ≤ Z := by
    rw [hZ]; exact Nat.mul_le_mul_right _ h_ge
  have h_pow_eq : (2^32 * 2^32 : Nat) = 2^64 := by decide
  omega


/-- **Phase-1b 1st BLTU check semantics under no-truncation precondition**:
    the BLTU check `(rhatc << 32) ||| div_un1 < q1c * dLo` is equivalent to
    `q1c * vTop > x` (i.e., q1c overshoots q*) UNDER `rhatc < 2^32`.

    The `rhatc < 2^32` precondition is essential: without it, the
    `rhatc << 32` operation truncates the high bits of rhatc, breaking
    the equivalence. Phase-1a's `div128Quot_rhatc_lt_2dHi` only gives
    `rhatc < 2 * dHi < 2^33`, so the precondition isn't automatic.

    Pure-Nat algebraic equivalence under the precondition:
    1. `rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat` (no truncation
       since rhatc < 2^32 and div_un1 < 2^32).
    2. `qDlo.toNat = q1c.toNat * dLo.toNat` (no Word multiplication
       overflow since q1c < 2^32 and dLo < 2^32).
    3. BLTU ⟺ rhatc * 2^32 + div_un1 < q1c * dLo.
    4. Substitute Phase-1a Euclidean (rhatc = u4 - q1c * dHi):
       (u4 - q1c * dHi) * 2^32 + div_un1 < q1c * dLo
       ⟺ u4 * 2^32 + div_un1 < q1c * (dHi * 2^32 + dLo) = q1c * vTop.
       ⟺ q1c * vTop > x.

    **Issue #1337 algorithm fix migration. Decomposition sub-stub.** -/
theorem div128Quot_v2_phase1b_check_iff_overshoot_under_runtime (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    -- Hypothesis: rhatc fits in 32 bits (essential for the algebraic equivalence).
    rhatc.toNat < 2^32 → q1c.toNat < 2^32 →
    (BitVec.ult rhatUn1 qDlo ↔
      q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) > u4.toNat * 2^32 + div_un1.toNat) := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1
        h_rhatc_lt h_q1c_lt
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq
    have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
      b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
    have hdHi_ge : dHi.toNat ≥ 2^31 :=
      div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
    rw [heq] at hdHi_ge; simp at hdHi_ge
  -- Phase-1a Euclidean: q1c * dHi + rhatc = u4 (as Nats).
  have h_post1a : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  -- Bridge: rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat.
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
         rhatc.toNat * 2^32 + div_un1.toNat
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  -- Bridge: qDlo.toNat = q1c.toNat * dLo.toNat.
  have h_qDlo_eq : qDlo.toNat = q1c.toNat * dLo.toNat := by
    show (q1c * dLo).toNat = q1c.toNat * dLo.toNat
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have h_mul_lt : q1c.toNat * dLo.toNat < 2^32 * 2^32 :=
      Nat.mul_lt_mul_of_lt_of_lt h_q1c_lt hdLo_lt
    have h_pow : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  -- Main equivalence — convert ult to <.
  rw [EvmWord.ult_iff, h_rhatUn1_eq, h_qDlo_eq]
  -- Goal: rhatc * 2^32 + div_un1 < q1c * dLo ↔
  --       q1c * (dHi * 2^32 + dLo) > u4 * 2^32 + div_un1
  -- Pure-Nat algebra under h_post1a.
  have h_vTop_eq : q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) =
      q1c.toNat * dHi.toNat * 2^32 + q1c.toNat * dLo.toNat := by ring
  rw [h_vTop_eq]
  -- From h_post1a: rhatc.toNat = u4.toNat - q1c.toNat * dHi.toNat.
  have h_q1c_dHi_le : q1c.toNat * dHi.toNat ≤ u4.toNat := by omega
  have h_rhatc_2pow32 :
      rhatc.toNat * 2^32 = u4.toNat * 2^32 - q1c.toNat * dHi.toNat * 2^32 := by
    have h_rhatc_eq : rhatc.toNat = u4.toNat - q1c.toNat * dHi.toNat := by omega
    rw [h_rhatc_eq, Nat.sub_mul]
  have h_q1c_dHi_2pow32_le : q1c.toNat * dHi.toNat * 2^32 ≤ u4.toNat * 2^32 :=
    Nat.mul_le_mul_right _ h_q1c_dHi_le
  omega


/-- **Phase-1b 2nd guard fires when needed**: if the 1st correction fired
    (q1c was overshooting by ≥ 1), then the 2nd correction's guard
    `rhat' < 2^32` fires too, allowing the 2nd correction to evaluate.

    Equivalently: when q1c overshoots by 2 (the case requiring 2 corrections),
    after the 1st correction rhat' = rhatc + dHi is bounded by dHi + dHi-1
    < 2 * dHi < 2^33, but specifically < 2^32 in this regime.

    PROVEN STUB. Closes via Knuth's Theorem A bounds on rhat' after
    correction.

    **Issue #1337 algorithm fix migration. Decomposition sub-stub.** -/
theorem div128Quot_v2_phase1b_2nd_guard_under_runtime (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    -- When the 2nd correction is NEEDED (i.e., overshoot ≥ 1 after 1st
    -- correction), the guard `rhat' < 2^32` holds. Stated as: if q1c was
    -- overshooting by 2 before any correction, rhat' < 2^32.
    let q1c_overshoot_2 :=
      q1c.toNat = (u4.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2
    q1c_overshoot_2 → rhat'.toNat < 2^32 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 rhat' q1c_overshoot_2 h_overshoot
  -- Standard arithmetic facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hu4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact hu4_lt_b3prime
  have h_post1a : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
  have h_q1c_le_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 u4 dHi dLo hdHi_ge hdLo_lt hu4_lt_vTop
  -- Abbreviate q_true.
  set q_true := (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat)
    with h_q_true_def
  -- From overshoot: q1c = q_true + 2.
  have h_q1c_eq : q1c.toNat = q_true + 2 := h_overshoot
  -- Set explicit Nat names for non-linear products to help omega.
  set A : Nat := (q_true + 1) * dHi.toNat with h_A_def
  set B : Nat := (q_true + 1) * dLo.toNat with h_B_def
  set C : Nat := (q_true + 2) * dHi.toNat with h_C_def
  -- C = A + dHi.
  have h_C_eq : C = A + dHi.toNat := by
    show (q_true + 2) * dHi.toNat = (q_true + 1) * dHi.toNat + dHi.toNat
    ring
  -- vTop > 0.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h1 : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
    have h2 : (2^31 * 2^32 : Nat) = 2^63 := by decide
    omega
  -- x < (q_true + 1) * vTop = A * 2^32 + B.
  have h_x_lt_qtp1_vTop :
      u4.toNat * 2^32 + div_un1.toNat < A * 2^32 + B := by
    have h_div_mod := Nat.div_add_mod (u4.toNat * 2^32 + div_un1.toNat)
      (dHi.toNat * 2^32 + dLo.toNat)
    have h_mod_lt :
        (u4.toNat * 2^32 + div_un1.toNat) % (dHi.toNat * 2^32 + dLo.toNat) <
        dHi.toNat * 2^32 + dLo.toNat := Nat.mod_lt _ h_vTop_pos
    -- Goal: u4*2^32 + div_un1 < A * 2^32 + B = (q_true + 1) * (dHi*2^32 + dLo).
    -- Rewrite RHS via ring.
    have h_eq : A * 2^32 + B = (q_true + 1) * (dHi.toNat * 2^32 + dLo.toNat) := by
      show (q_true + 1) * dHi.toNat * 2^32 + (q_true + 1) * dLo.toNat = _
      ring
    rw [h_eq]
    have h_div_mod' :
        (dHi.toNat * 2^32 + dLo.toNat) * q_true +
        (u4.toNat * 2^32 + div_un1.toNat) % (dHi.toNat * 2^32 + dLo.toNat) =
        u4.toNat * 2^32 + div_un1.toNat := h_div_mod
    -- (q_true + 1) * vTop = q_true * vTop + vTop > x via div_mod.
    have h_qt_vTop : q_true * (dHi.toNat * 2^32 + dLo.toNat) =
        (dHi.toNat * 2^32 + dLo.toNat) * q_true := Nat.mul_comm _ _
    have h_step :
        (q_true + 1) * (dHi.toNat * 2^32 + dLo.toNat) =
        q_true * (dHi.toNat * 2^32 + dLo.toNat) + (dHi.toNat * 2^32 + dLo.toNat) := by
      ring
    rw [h_step, h_qt_vTop]
    omega
  -- A ≤ u4 (from h_q1c_dHi_le and h_q1c_eq).
  have h_q1c_dHi_le : q1c.toNat * dHi.toNat ≤ u4.toNat := by linarith [h_post1a]
  have h_q1c_dHi_eq_C_pre : q1c.toNat * dHi.toNat = C := by
    show q1c.toNat * dHi.toNat = (q_true + 2) * dHi.toNat
    rw [h_q1c_eq]
  have h_C_le : C ≤ u4.toNat := by rw [← h_q1c_dHi_eq_C_pre]; exact h_q1c_dHi_le
  have h_A_le : A ≤ u4.toNat := by
    have h_AC : A ≤ C := by
      show (q_true + 1) * dHi.toNat ≤ (q_true + 2) * dHi.toNat
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  -- B + 2^32 ≤ 2^64 (using B ≤ (2^32 - 1)^2).
  have h_B_tight : B ≤ (2^32 - 1) * (2^32 - 1) := by
    have h_qtp1_le : q_true + 1 ≤ 2^32 - 1 := by omega
    have h_dLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
    show (q_true + 1) * dLo.toNat ≤ (2^32 - 1) * (2^32 - 1)
    exact Nat.mul_le_mul h_qtp1_le h_dLo_le
  have h_arith : (2^32 - 1) * (2^32 - 1) + 2^32 ≤ 2^64 := by decide
  have h_B_plus_pow32_le : B + 2^32 ≤ 2^64 :=
    le_trans (Nat.add_le_add_right h_B_tight _) h_arith
  -- u4 - A < 2^32, via the pure-Nat helper.
  have h_u4_minus_A_lt : u4.toNat - A < 2^32 :=
    phase1b_2nd_guard_arith u4.toNat A B div_un1.toNat
      h_x_lt_qtp1_vTop h_A_le h_B_plus_pow32_le
  -- rhatc + dHi = u4 - A (using Phase-1a Euclidean and h_C_eq).
  have h_q1c_dHi_eq_C : q1c.toNat * dHi.toNat = C := by
    show q1c.toNat * dHi.toNat = (q_true + 2) * dHi.toNat
    rw [h_q1c_eq]
  have h_rhatc_plus_q1c_dHi : rhatc.toNat + q1c.toNat * dHi.toNat = u4.toNat := by
    linarith [h_post1a]
  have h_rhatc_eq : rhatc.toNat = u4.toNat - C := by
    have : rhatc.toNat + C = u4.toNat := by rw [← h_q1c_dHi_eq_C]; exact h_rhatc_plus_q1c_dHi
    omega
  have h_rhatc_plus_dHi : rhatc.toNat + dHi.toNat = u4.toNat - A := by
    rw [h_rhatc_eq, h_C_eq]; omega
  have h_rhatc_le_u4_minus_A : rhatc.toNat ≤ u4.toNat - A := by
    rw [h_rhatc_eq, h_C_eq]; omega
  -- No-wrap.
  have h_no_wrap : rhatc.toNat + dHi.toNat < 2^64 := by
    have h_pow : (2^32 : Nat) ≤ 2^64 := by decide
    have h_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by
      rw [h_rhatc_plus_dHi]; omega
    omega
  -- Case-split on BLTU check.
  by_cases h_check : BitVec.ult rhatUn1 qDlo
  · -- BLTU fires: rhat' = rhatc + dHi.
    have h_rhat'_unfold : rhat'.toNat =
        (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc).toNat := rfl
    rw [h_rhat'_unfold, if_pos h_check, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt h_no_wrap]
    rw [h_rhatc_plus_dHi]
    exact h_u4_minus_A_lt
  · -- BLTU doesn't fire: rhat' = rhatc ≤ rhatc + dHi.
    have h_rhat'_unfold : rhat'.toNat =
        (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc).toNat := rfl
    rw [h_rhat'_unfold, if_neg h_check]
    omega


theorem div128Quot_v2_case_0_rhatc_lt_pow32_under_runtime
    (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (_hborrow_v2 : isAddbackBorrowN4CallEvm_v2 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2^32 := by
  intro shift antiShift u4 b3' dHi q1 rhat hi1 rhatc
  -- Step 1: shift bounds. Under _hshift_nz: shift ∈ [1, 63].
  have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply _hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [EvmAsm.Rv64.AddrNorm.word_toNat_0]; omega
  -- Step 2: u4 < 2^63 (via u_top_lt_pow63_of_shift_nz).
  have h_u4_lt : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      hshift_pos hshift_le_63
  -- Step 3: dHi ≥ 2^31, < 2^32.
  have h_b3'_ge_pow63 : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) _hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 b3' h_b3'_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  -- Step 4: q1 = u4/dHi < 2^32 (from u4 < 2^63 and dHi ≥ 2^31).
  have h_q1_lt : q1.toNat < 2^32 := by
    show (rv64_divu u4 dHi).toNat < 2^32
    rw [rv64_divu_toNat u4 dHi hdHi_ne]
    have h1 : u4.toNat / dHi.toNat ≤ u4.toNat / 2^31 :=
      Nat.div_le_div_left hdHi_ge (by decide)
    have h2 : u4.toNat / 2^31 < 2^32 :=
      Nat.div_lt_of_lt_mul (by
        have h_pow : (2^32 * 2^31 : Nat) = 2^63 := by decide
        omega)
    omega
  -- Step 5: hi1 = 0 (from q1 < 2^32).
  have h_hi1_zero : hi1 = 0 := by
    show q1 >>> (32 : BitVec 6).toNat = 0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]
    rfl
  -- Step 6: Phase-1a Euclidean — q1 * dHi + rhat = u4 (using h_hi1_zero
  -- to simplify the if-branches).
  have h_post1a : q1.toNat * dHi.toNat + rhat.toNat = u4.toNat := by
    have h1 := div128Quot_first_round_post u4 dHi hdHi_ne hdHi_lt
    -- h1 : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat with q1c, rhatc as if-expressions.
    -- With hi1 = 0, if-branches collapse to q1 and rhat.
    show q1.toNat * dHi.toNat + (u4 - q1 * dHi).toNat = u4.toNat
    have h_q1_branch : (if q1 >>> (32 : BitVec 6).toNat = 0 then q1
                        else q1 + signExtend12 4095).toNat = q1.toNat := by
      rw [if_pos h_hi1_zero]
    have h_rhat_branch : (if q1 >>> (32 : BitVec 6).toNat = 0 then u4 - q1 * dHi
                          else u4 - q1 * dHi + dHi).toNat = (u4 - q1 * dHi).toNat := by
      rw [if_pos h_hi1_zero]
    rw [← h_q1_branch, ← h_rhat_branch]
    exact h1
  -- Step 7: q1 * dHi (Word) doesn't overflow.
  have h_q1_dHi_lt_pow64 : q1.toNat * dHi.toNat < 2^64 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt h_q1_lt hdHi_lt
    have h_pow : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  have h_q1_dHi_word : (q1 * dHi).toNat = q1.toNat * dHi.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h_q1_dHi_lt_pow64
  -- Step 8: rhat = u4 - q1 * dHi as Nats (no underflow).
  have h_rhat_eq : rhat.toNat = u4.toNat - q1.toNat * dHi.toNat := by
    show (u4 - q1 * dHi).toNat = u4.toNat - q1.toNat * dHi.toNat
    rw [BitVec.toNat_sub, h_q1_dHi_word]
    have h_q1_dHi_le : q1.toNat * dHi.toNat ≤ u4.toNat := by omega
    have h_u4_lt_pow64 : u4.toNat < 2^64 := u4.isLt
    omega
  -- Step 9: rhat < dHi (since rhat = u4 - q1*dHi ≤ dHi - 1 from Phase-1a remainder).
  have h_rhat_lt : rhat.toNat < dHi.toNat := by
    rw [h_rhat_eq]
    -- Phase-1a invariant: u4 = q1*dHi + rhat with 0 ≤ rhat < dHi (from rv64_divu).
    -- We have q1.toNat * dHi.toNat + rhat.toNat = u4.toNat, and from rv64_divu_toNat:
    -- q1.toNat = u4.toNat / dHi.toNat, so rhat.toNat = u4.toNat mod dHi.toNat.
    -- The Nat mod is < dHi.
    have h_q1_div : q1.toNat = u4.toNat / dHi.toNat := by
      show (rv64_divu u4 dHi).toNat = u4.toNat / dHi.toNat
      exact rv64_divu_toNat u4 dHi hdHi_ne
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_mod_lt := Nat.mod_lt u4.toNat h_dHi_pos
    have h_div_mod : dHi.toNat * (u4.toNat / dHi.toNat) + u4.toNat % dHi.toNat = u4.toNat :=
      Nat.div_add_mod u4.toNat dHi.toNat
    have h_rhat_mod_eq : u4.toNat - q1.toNat * dHi.toNat = u4.toNat % dHi.toNat := by
      rw [h_q1_div]
      have h_swap : dHi.toNat * (u4.toNat / dHi.toNat) =
                    u4.toNat / dHi.toNat * dHi.toNat := Nat.mul_comm _ _
      omega
    rw [h_rhat_mod_eq]
    exact h_mod_lt
  -- Step 10: rhatc = rhat (from hi1 = 0); rhat < dHi < 2^32.
  show rhatc.toNat < 2^32
  show (if hi1 = 0 then rhat else rhat + dHi).toNat < 2^32
  rw [if_pos h_hi1_zero]
  omega


/-- **q_true < 2^32 under runtime preconditions**.

    From the call-trial precondition `u4 < vTop` (i.e. uHi-half < vTop),
    plus `div_un1 < 2^32` (structural — div_un1 is a top-32-bits ushr),
    we have `x = u4*2^32 + div_un1 < vTop*2^32`. Hence `q_true = x/vTop < 2^32`.

    Used as the `q1c < 2^32` precondition of Stub 2 in case 0/1/2 sub-stubs. -/
theorem div128Quot_v2_q_true_lt_pow32_under_runtime
    (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hbltu : isCallTrialN4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    (u4.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) < 2^32 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1
  have h_b3'_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_u4_lt_b3prime : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      (isCallTrialN4Evm_def ▸ _hbltu)
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_b3'_decomp]; exact h_u4_lt_b3prime
  have h_x_lt : u4.toNat * 2^32 + div_un1.toNat <
      (dHi.toNat * 2^32 + dLo.toNat) * 2^32 :=
    q_true_x_lt_vTop_pow32_arith u4.toNat (dHi.toNat * 2^32 + dLo.toNat)
      div_un1.toNat h_u4_lt_vTop h_div_un1_lt
  exact Nat.div_lt_of_lt_mul h_x_lt


end EvmAsm.Evm64
