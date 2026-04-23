/-
  EvmAsm.Evm64.EvmWordArith.Div128Shift0

  Lemmas about `div128Quot 0 a3 b3` under shift=0 normalization
  (`b3 ≥ 2^63`). Under this regime, uHi=0 ⟹ un21 < 2^32 ⟹ Phase 2a
  doesn't correct ⟹ rhat2c < 2^32 ⟹ the Phase 2b false-positive
  (counterexample from #1138) CAN'T fire. So the algorithm is correct
  in this regime regardless of whether the Phase 2b guard is in place.

  Purpose: build the semantic bridge for
  `evm_div_n4_shift0_call_skip_stack_spec` (task #67 in
  `project_un21_lt_vTop_plan.md`) without depending on #1138 merging.

  Key lemma: `div128Quot_shift0_eq_val256_div` — under skip-borrow +
  shift=0 + hbnz, `(div128Quot 0 a3 b3).toNat = val256(a) / val256(b)`.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Key identity: `(a3 >>> 32).toNat * 2^32 + ((a3 <<< 32) >>> 32).toNat = a3.toNat`.
    Expresses a 64-bit word as its top-32-bits * 2^32 + low-32-bits. -/
theorem word_hi32_lo32_decomp (a : Word) :
    (a >>> (32 : BitVec 6).toNat).toNat * 2^32 +
    ((a <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat = a.toNat := by
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- top 32 bits: a.toNat / 2^32.
  -- low 32 bits: (a.toNat * 2^32 mod 2^64) / 2^32.
  have h_shl : ((a <<< 32 : Word) >>> 32).toNat = a.toNat % 2^32 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    -- (a.toNat * 2^32 % 2^64) / 2^32 = a.toNat % 2^32
    have h_eq : (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32 := by
      rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide, Nat.mul_mod_mul_right]
    rw [h_eq]
    have h_pos : (2^32 : Nat) > 0 := by decide
    rw [Nat.mul_div_cancel _ h_pos]
  rw [h_shl]
  have := Nat.div_add_mod a.toNat (2^32)
  omega

/-- Under shift=0 (b3 ≥ 2^63), the hypotheses of `div128Quot_toNat_eq_strict`
    and `div128Quot_q0_prime_lt_pow32` + `div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63`
    are all dischargeable for `div128Quot 0 a3 b3`. Conclusion:
    `(div128Quot 0 a3 b3).toNat ≥ a3.toNat / b3.toNat` under b3 ≥ 2^63. -/
theorem div128Quot_shift0_ge_a3_div_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0) :
    (div128Quot (0 : Word) a3 b3).toNat ≥ a3.toNat / b3.toNat := by
  -- dHi, dLo decomposition for b3. Under b3 ≥ 2^63, dHi ≥ 2^31.
  set dHi := b3 >>> (32 : BitVec 6).toNat with h_dHi_def
  set dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat with h_dLo_def
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3 >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    have h32 : (32 : BitVec 6).toNat = 32 := by decide
    rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
    have : b3.toNat / 2^32 ≥ 2^63 / 2^32 :=
      Nat.div_le_div_right hb3_ge
    have : (2^63 : Nat) / 2^32 = 2^31 := by decide
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    exact Word_ushiftRight_32_lt_pow32
  -- huHi_lt_vTop: 0 < dHi*2^32 + dLo. Since dHi ≥ 2^31 > 0, holds.
  have h_uHi_lt : (0 : Word).toNat < dHi.toNat * 2^32 + dLo.toNat := by
    show 0 < _
    have : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ h_dHi_ge
    omega
  -- Local let bindings for the theorem's let-chain.
  set q1 := rv64_divu (0 : Word) dHi with h_q1_def
  -- q1 = 0 since uHi = 0.
  have h_q1_zero : q1 = 0 := by
    show rv64_divu 0 dHi = 0
    have h_dHi_ne : dHi ≠ 0 := by
      intro heq
      rw [heq] at h_dHi_ge
      simp at h_dHi_ge
    apply BitVec.eq_of_toNat_eq
    rw [rv64_divu_toNat _ _ h_dHi_ne]
    show (0 : Word).toNat / dHi.toNat = (0 : Word).toNat
    simp
  -- Phase 1 intermediates all collapse to 0 under q1 = 0.
  -- Use KB-LB8 for Phase 2 lower bound.
  -- un21 under shift=0: un21 = a3 >> 32 < 2^32, so un21 < 2^63.
  have h_un21_lt_pow63 :
      let q1 := rv64_divu (0 : Word) dHi
      let rhat := (0 : Word) - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let div_un1 := a3 >>> (32 : BitVec 6).toNat
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c
      let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
      let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      let cu_q1_dlo := q1' * dLo
      let un21 := cu_rhat_un1 - cu_q1_dlo
      un21.toNat < 2^63 := by
    intro q1 rhat hi1 rhatc q1c div_un1 rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21
    -- TODO(#67): trace that un21 = a3 >> 32 < 2^32 < 2^63 under uHi = 0.
    -- This requires unfolding the let chain, showing q1' = 0, rhat' = 0,
    -- and un21 = a3 >> 32.
    sorry
  sorry

/-- Upper bound: under shift=0 (b3 ≥ 2^63), `div128Quot 0 a3 b3` is
    at most 1. -/
theorem div128Quot_shift0_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (div128Quot (0 : Word) a3 b3).toNat ≤ 1 := by
  sorry

/-- If `div128Quot 0 a3 b3 = 0` under shift=0, then a3 < b3. -/
theorem div128Quot_shift0_eq_zero_implies_a3_lt_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0)
    (hqHat_zero : div128Quot (0 : Word) a3 b3 = 0) :
    a3.toNat < b3.toNat := by
  -- Use div128Quot_shift0_ge_a3_div_b3: qHat ≥ a3/b3.
  -- qHat = 0 ⟹ a3/b3 = 0 ⟹ a3 < b3.
  have h_ge := div128Quot_shift0_ge_a3_div_b3 a3 b3 hb3_ge hb3_nz
  have h_zero_toNat : (div128Quot (0 : Word) a3 b3).toNat = 0 := by
    rw [hqHat_zero]; rfl
  rw [h_zero_toNat] at h_ge
  have h_b3_pos : 0 < b3.toNat := by
    have : b3.toNat ≥ 2^63 := hb3_ge
    omega
  have h_div_zero : a3.toNat / b3.toNat = 0 := Nat.le_zero.mp h_ge
  exact (Nat.div_eq_zero_iff_lt h_b3_pos).mp h_div_zero

/-- Under shift=0 (b3 ≥ 2^63), a3 < b3 implies val256(a) < val256(b).

    Direct: val256(a) = a0 + a1*2^64 + a2*2^128 + a3*2^192.
    a0,a1,a2 < 2^64 so a0+a1*2^64+a2*2^128 < 2^192.
    Hence val256(a) < (a3+1)*2^192 ≤ b3*2^192 ≤ val256(b). -/
theorem val256_lt_of_a3_lt_b3 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : a3.toNat < b3.toNat) :
    val256 a0 a1 a2 a3 < val256 b0 b1 b2 b3 := by
  have h_low_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 < 2^192 := by
    have h0 := a0.isLt
    have h1 := a1.isLt
    have h2 := a2.isLt
    -- a0 ≤ 2^64-1, a1*2^64 ≤ (2^64-1)*2^64, a2*2^128 ≤ (2^64-1)*2^128.
    -- Sum ≤ (2^64-1)*(1 + 2^64 + 2^128) = 2^192 - 1.
    calc a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128
        ≤ (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 := by
          have h1' : a1.toNat * 2^64 ≤ (2^64 - 1) * 2^64 :=
            Nat.mul_le_mul_right _ (by omega)
          have h2' : a2.toNat * 2^128 ≤ (2^64 - 1) * 2^128 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      _ = 2^192 - 1 := by decide
      _ < 2^192 := by decide
  -- val256 a = a0 + a1*2^64 + a2*2^128 + a3*2^192.
  -- a3 < b3 ⟹ a3 ≤ b3 - 1 ⟹ a3*2^192 ≤ (b3-1)*2^192 = b3*2^192 - 2^192.
  -- val256 a < (b3-1)*2^192 + 2^192 = b3*2^192 ≤ val256 b.
  have h_b_ge : val256 b0 b1 b2 b3 ≥ b3.toNat * 2^192 := by
    show b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192 ≥ _
    omega
  have h_a_ub : val256 a0 a1 a2 a3 < (a3.toNat + 1) * 2^192 := by
    show a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 < _
    have : (a3.toNat + 1) * 2^192 = a3.toNat * 2^192 + 2^192 := by ring
    omega
  have h_bound : (a3.toNat + 1) * 2^192 ≤ b3.toNat * 2^192 := by
    apply Nat.mul_le_mul_right
    omega
  omega

end EvmAsm.Evm64
