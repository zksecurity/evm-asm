/-
  EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

  Toward `isMaxTrialN4_false_of_shift_nz` (Option A of the
  max-trial vacuity discovery — see
  `memory/project_max_trial_vacuous_discovery.md`).

  The main claim (to be proven via 3 sublemmas):
  `isMaxTrialN4 a3 b2 b3 ∧ (clzResult b3).1 ≠ 0 → False`.

  This file hosts the sublemma pieces. Currently contains:
  - `clzStep_snd_ge` (Step 1 helper).
  - `clzPipeline_snd_ge_pow62` (Step 1 of the plan).
  - `u_top_lt_pow63_of_shift_nz` (Step 3 of the plan).
-/

import EvmAsm.Evm64.EvmWordArith.CLZLemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CLZ step lower-bound invariant: if input's 2nd component is ≥ 2^(K - M_s)
    (the previous stage's K), the output's 2nd component is ≥ 2^K. Dual to the
    existing `clzStep_invariant_pres` / `clzStep_invariant_and_bound` upper-bound
    machinery.

    * Pass case (`p.2 >>> K ≠ 0`): output.2 = p.2, and `p.2 ≥ 2^K` follows directly
      from `ushiftRight_ne_zero_iff`.
    * Fail case (`p.2 >>> K = 0`): output.2 = `p.2 <<< M_s = p.2.toNat * 2^M_s`
      (no wrap, since `p.2 < 2^K` and `K + M_s = 64`). Then
      `p.2.toNat * 2^M_s ≥ 2^(K - M_s) * 2^M_s = 2^K`. -/
theorem clzStep_snd_ge (K M_s : Nat) (m : Word) (p : Word × Word)
    (hlb : p.2.toNat ≥ 2^(K - M_s))
    (hKMs : K + M_s = 64) (hKM_s_pos : 0 < M_s)
    (hMs_lt_K : M_s ≤ K) :
    (clzStep K M_s m p).2.toNat ≥ 2^K := by
  unfold clzStep; dsimp only []
  by_cases hpass : p.2 >>> K ≠ 0
  · rw [if_pos hpass]
    exact (ushiftRight_ne_zero_iff K).mp hpass
  · rw [if_neg hpass]
    push Not at hpass
    have hp2_lt : p.2.toNat < 2^K := (ushiftRight_eq_zero_iff K).mp hpass
    have hshifted : (p.2 <<< M_s).toNat = p.2.toNat * 2^M_s := by
      rw [BitVec.toNat_shiftLeft]
      simp only [Nat.shiftLeft_eq]
      have : p.2.toNat * 2^M_s < 2^64 := by
        have hpos : 0 < (2 : Nat)^M_s := by positivity
        have : p.2.toNat * 2^M_s < 2^K * 2^M_s := Nat.mul_lt_mul_right hpos |>.mpr hp2_lt
        rw [← pow_add, hKMs] at this; exact this
      exact Nat.mod_eq_of_lt this
    rw [hshifted]
    have hmul : 2^(K - M_s) * 2^M_s = 2^K := by
      rw [← pow_add]; congr 1; omega
    calc p.2.toNat * 2^M_s ≥ 2^(K - M_s) * 2^M_s :=
        Nat.mul_le_mul_right _ hlb
      _ = 2^K := hmul

/-- After all 5 pipeline stages, the value is ≥ 2^62. Threads `clzStep_snd_ge`
    through the K-chain 32 → 48 → 56 → 60 → 62. -/
theorem clzPipeline_snd_ge_pow62 (val : Word) (hval : val ≠ 0) :
    (clzPipeline val).2.toNat ≥ 2^62 := by
  unfold clzPipeline
  have h_init : ((0 : Word), val).2.toNat ≥ 2^0 := by
    simp
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hval (BitVec.eq_of_toNat_eq (by simp [h])))
  have h0 := clzStep_snd_ge 32 32 (signExtend12 32) ((0 : Word), val)
    h_init (by norm_num) (by norm_num) (by norm_num)
  have h1 := clzStep_snd_ge 48 16 (signExtend12 16)
    (clzStep 32 32 (signExtend12 32) ((0 : Word), val))
    h0 (by norm_num) (by norm_num) (by norm_num)
  have h2 := clzStep_snd_ge 56 8 (signExtend12 8)
    (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val)))
    h1 (by norm_num) (by norm_num) (by norm_num)
  have h3 := clzStep_snd_ge 60 4 (signExtend12 4)
    (clzStep 56 8 (signExtend12 8)
      (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val))))
    h2 (by norm_num) (by norm_num) (by norm_num)
  exact clzStep_snd_ge 62 2 (signExtend12 2)
    (clzStep 60 4 (signExtend12 4)
      (clzStep 56 8 (signExtend12 8)
        (clzStep 48 16 (signExtend12 16) (clzStep 32 32 (signExtend12 32) ((0 : Word), val)))))
    h3 (by norm_num) (by norm_num) (by norm_num)

/-- For `shift.toNat ∈ [1, 63]`, the value `a3 >>> (64 - shift)` is bounded above
    by `2^63`. Concretely, the max-trial algorithm's `u_top` lies in `[0, 2^63)`
    under a non-zero shift.

    Proof chain: `signExtend12 0 - shift = 2^64 - shift.toNat` (Word), its `%64 =
    64 - shift.toNat`, then `BitVec.toNat_ushiftRight` + power split. -/
theorem u_top_lt_pow63_of_shift_nz (a3 shift : Word)
    (h1 : 1 ≤ shift.toNat) (h63 : shift.toNat ≤ 63) :
    (a3 >>> ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)).toNat < 2^63 := by
  have h0 : (signExtend12 (0 : BitVec 12) : Word) = 0 := by decide
  rw [h0]
  have hshift_toNat : ((0 : Word) - shift).toNat = 2^64 - shift.toNat := by
    rw [BitVec.toNat_sub]
    simp
    omega
  rw [hshift_toNat]
  have hmod : (2^64 - shift.toNat) % 64 = 64 - shift.toNat := by
    have : 2^64 - shift.toNat = (2^64 - 64) + (64 - shift.toNat) := by omega
    rw [this, Nat.add_mod]
    have : (2^64 - 64) % 64 = 0 := by decide
    rw [this]
    simp
    omega
  rw [hmod]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha3 : a3.toNat < 2^64 := a3.isLt
  have hsplit : (2 : Nat)^64 = 2^shift.toNat * 2^(64 - shift.toNat) := by
    rw [← pow_add, show shift.toNat + (64 - shift.toNat) = 64 from by omega]
  have hlt_pow_shift : a3.toNat / 2^(64 - shift.toNat) < 2^shift.toNat := by
    rw [hsplit, Nat.mul_comm] at ha3
    exact Nat.div_lt_of_lt_mul ha3
  exact lt_of_lt_of_le hlt_pow_shift (Nat.pow_le_pow_right (by norm_num) h63)

end EvmAsm.Evm64
