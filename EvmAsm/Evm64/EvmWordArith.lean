/-
  EvmAsm.Evm64.EvmWordArith

  Mathematical correctness lemmas connecting limb-level computations
  to 256-bit EvmWord operations. Used by stack-level specs.
-/

import EvmAsm.Evm64.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Shared helpers
-- ============================================================================

private theorem bv_or_eq_zero {n : Nat} {x y : BitVec n} (h : x ||| y = 0) :
    x = 0 ∧ y = 0 :=
  BitVec.or_eq_zero_iff.mp h

private theorem ult_one_eq_zero {x : Word} : BitVec.ult x 1 ↔ x = 0 := by
  constructor
  · intro h
    have h1 := of_decide_eq_true h
    change x.toNat < (1 : Word).toNat at h1
    have : (1 : Word).toNat = 1 := by native_decide
    have : x.toNat = 0 := by omega
    have : (0 : Word).toNat = 0 := by native_decide
    exact BitVec.eq_of_toNat_eq (by omega)
  · intro h; subst h; native_decide

private theorem xor_eq_zero_imp {n : Nat} {x y : BitVec n} (h : x ^^^ y = 0) : x = y :=
  BitVec.xor_eq_zero_iff.mp h

-- OR of two borrow/carry flags (0-or-1 valued bitvectors)
private theorem borrow_or_iff (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)) =
    (if (c1 ∨ c2) then (1 : Word) else 0) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp_all

-- The toNat decomposition of a 256-bit value into 4 limbs.
private theorem toNat_eq_limb_sum (v : EvmWord) :
    v.toNat = (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
              (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 := by
  simp only [getLimb, BitVec.extractLsb'_toNat,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    Nat.zero_mul, Nat.shiftRight_zero]
  have hv := v.isLt  -- v.toNat < 2^256
  omega

-- getLimb as toNat division
private theorem getLimb_toNat_eq (v : EvmWord) (i : Fin 4) :
    (v.getLimb i).toNat = (v.toNat / 2 ^ (i.val * 64)) % 2 ^ 64 := by
  simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

-- BitVec.ult ↔ toNat comparison
private theorem ult_iff {n : Nat} (x y : BitVec n) : BitVec.ult x y ↔ x.toNat < y.toNat :=
  ⟨fun h => BitVec.lt_def.mp (of_decide_eq_true h),
   fun h => decide_eq_true (BitVec.lt_def.mpr h)⟩

-- ============================================================================
-- ISZERO correctness
-- ============================================================================

theorem iszero_or_reduce_correct (a : EvmWord) :
    (if BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1
     then (1 : Word) else 0) =
    (if a = 0 then (1 : Word) else 0) := by
  suffices h : BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1 ↔ a = 0 by
    by_cases ha : a = 0 <;> simp_all
  constructor
  · intro h
    have hor := ult_one_eq_zero.mp h
    have h12 := bv_or_eq_zero (show (a.getLimb 0 ||| a.getLimb 1) ||| (a.getLimb 2 ||| a.getLimb 3) = 0 by
      rw [BitVec.or_assoc] at hor; exact hor)
    exact (eq_zero_iff_limbs a).mpr
      ⟨(bv_or_eq_zero h12.1).1, (bv_or_eq_zero h12.1).2,
       (bv_or_eq_zero h12.2).1, (bv_or_eq_zero h12.2).2⟩
  · intro h; subst h; exact ult_one_eq_zero.mpr rfl

-- ============================================================================
-- EQ correctness
-- ============================================================================

theorem eq_xor_or_reduce_correct (a b : EvmWord) :
    let acc0 := a.getLimb 0 ^^^ b.getLimb 0
    let acc1 := acc0 ||| (a.getLimb 1 ^^^ b.getLimb 1)
    let acc2 := acc1 ||| (a.getLimb 2 ^^^ b.getLimb 2)
    let acc3 := acc2 ||| (a.getLimb 3 ^^^ b.getLimb 3)
    (if BitVec.ult acc3 1 then (1 : Word) else 0) =
    (if a = b then (1 : Word) else 0) := by
  intro acc0; intro acc1; intro acc2; intro acc3
  suffices h : BitVec.ult acc3 1 ↔ a = b by
    by_cases hab : a = b <;> simp_all
  constructor
  · intro h
    have hacc : acc3 = 0 := ult_one_eq_zero.mp h
    have hacc_flat : (a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1) |||
                     (a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3) = 0 := by
      show acc3 = 0; exact hacc
    have h12 := bv_or_eq_zero (show ((a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1)) |||
        ((a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3)) = 0 by
      rw [BitVec.or_assoc] at hacc_flat; exact hacc_flat)
    calc a = fromLimbs a.getLimb := (fromLimbs_getLimb a).symm
      _ = fromLimbs b.getLimb := by unfold fromLimbs; simp only [
            xor_eq_zero_imp (bv_or_eq_zero h12.1).1, xor_eq_zero_imp (bv_or_eq_zero h12.1).2,
            xor_eq_zero_imp (bv_or_eq_zero h12.2).1, xor_eq_zero_imp (bv_or_eq_zero h12.2).2]
      _ = b := fromLimbs_getLimb b
  · intro h; subst h
    show BitVec.ult ((((a.getLimb 0 ^^^ a.getLimb 0) |||
      (a.getLimb 1 ^^^ a.getLimb 1)) |||
      (a.getLimb 2 ^^^ a.getLimb 2)) |||
      (a.getLimb 3 ^^^ a.getLimb 3)) 1
    simp [BitVec.xor_self, BitVec.ult]

-- ============================================================================
-- LT correctness: borrow chain = unsigned less-than
-- ============================================================================

-- Single-step borrow lemma: borrow condition ↔ multi-limb comparison.
-- M is the positional multiplier (2^64 at step 1, 2^128 at step 2, 2^192 at step 3).
-- aH, bH are single limbs (< 2^64). aLo, bLo are partial sums (< M).
private theorem borrow_step_iff (M : Nat)
    {aH bH : Nat} (_haH : aH < 2^64) (_hbH : bH < 2^64)
    {aLo bLo : Nat} (haLo : aLo < M) (hbLo : bLo < M) :
    (aH < bH ∨ (aH + 2^64 - bH) % 2^64 < (if aLo < bLo then 1 else 0)) ↔
    (aLo + aH * M < bLo + bH * M) := by
  constructor
  · intro h; rcases h with h1 | h2
    · nlinarith [Nat.mul_le_mul_right M (show aH + 1 ≤ bH by omega)]
    · split at h2
      · have : (aH + 2^64 - bH) % 2^64 = 0 := by omega
        have : aH + 2^64 - bH < 2 * 2^64 := by omega
        have heq : aH = bH := by omega
        subst heq; omega
      · omega
  · intro h
    by_cases hcmp : aH < bH
    · left; exact hcmp
    · right
      have heq : aH = bH := by
        nlinarith [Nat.mul_le_mul_right M (show bH + 1 ≤ aH + 1 by omega)]
      subst heq
      have hlt : aLo < bLo := by omega
      simp [hlt]

set_option maxHeartbeats 400000 in
theorem lt_borrow_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    borrow3 = if BitVec.ult a b then (1 : Word) else 0 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro borrow0 borrow1a temp1 borrow1b borrow1
  intro borrow2a temp2 borrow2b borrow2
  intro borrow3a temp3 borrow3b borrow3
  -- Step 1: borrow0 tracks 1-limb comparison
  have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
    simp only [borrow0]; split
    · rename_i h; rw [if_pos ((ult_iff _ _).mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h ((ult_iff _ _).mpr hlt))]; rfl
  -- Step 2: borrow1 tracks 2-limb comparison
  have hb1_or : borrow1 = if (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp1_nat : temp1.toNat = (a1.toNat + 2^64 - b1.toNat) % 2^64 := by
    simp only [temp1, BitVec.toNat_sub]; congr 1; omega
  have hb1_cond : (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0) ↔
      (a0.toNat + a1.toNat * 2^64 < b0.toNat + b1.toNat * 2^64) := by
    rw [show BitVec.ult a1 b1 ↔ a1.toNat < b1.toNat from ult_iff _ _,
        show BitVec.ult temp1 borrow0 ↔ temp1.toNat < borrow0.toNat from ult_iff _ _,
        htemp1_nat, hb0_nat]
    exact borrow_step_iff (2^64) a1.isLt b1.isLt a0.isLt b0.isLt
  have hb1_nat : borrow1.toNat = if (a0.toNat + a1.toNat * 2^64 <
      b0.toNat + b1.toNat * 2^64) then 1 else 0 := by
    rw [hb1_or]; split
    · rename_i h; rw [if_pos (hb1_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb1_cond.mpr hlt))]; rfl
  -- Step 3: borrow2 tracks 3-limb comparison
  have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp2_nat : temp2.toNat = (a2.toNat + 2^64 - b2.toNat) % 2^64 := by
    simp only [temp2, BitVec.toNat_sub]; congr 1; omega
  have hb2_cond : (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
    rw [show BitVec.ult a2 b2 ↔ a2.toNat < b2.toNat from ult_iff _ _,
        show BitVec.ult temp2 borrow1 ↔ temp2.toNat < borrow1.toNat from ult_iff _ _,
        htemp2_nat, hb1_nat]
    have ha_bound : a0.toNat + a1.toNat * 2^64 < 2^128 := by
      have := a0.isLt; have := a1.isLt; nlinarith
    have hb_bound : b0.toNat + b1.toNat * 2^64 < 2^128 := by
      have := b0.isLt; have := b1.isLt; nlinarith
    convert borrow_step_iff (2^128) a2.isLt b2.isLt ha_bound hb_bound using 2
  have hb2_nat : borrow2.toNat = if (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
      b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) then 1 else 0 := by
    rw [hb2_or]; split
    · rename_i h; rw [if_pos (hb2_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb2_cond.mpr hlt))]; rfl
  -- Step 4: borrow3 tracks full 4-limb comparison
  have hb3_or : borrow3 = if (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp3_nat : temp3.toNat = (a3.toNat + 2^64 - b3.toNat) % 2^64 := by
    simp only [temp3, BitVec.toNat_sub]; congr 1; omega
  have hb3_cond : (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192) := by
    rw [show BitVec.ult a3 b3 ↔ a3.toNat < b3.toNat from ult_iff _ _,
        show BitVec.ult temp3 borrow2 ↔ temp3.toNat < borrow2.toNat from ult_iff _ _,
        htemp3_nat, hb2_nat]
    have ha_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 < 2^192 := by
      have := a0.isLt; have := a1.isLt; have := a2.isLt; nlinarith
    have hb_bound : b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 < 2^192 := by
      have := b0.isLt; have := b1.isLt; have := b2.isLt; nlinarith
    convert borrow_step_iff (2^192) a3.isLt b3.isLt ha_bound hb_bound using 2
  -- Final: connect borrow3 to BitVec.ult a b
  have hfinal : (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2) ↔ BitVec.ult a b := by
    constructor
    · intro h; rw [ult_iff, toNat_eq_limb_sum a, toNat_eq_limb_sum b]; exact hb3_cond.mp h
    · intro h; rw [ult_iff, toNat_eq_limb_sum a, toNat_eq_limb_sum b] at h; exact hb3_cond.mpr h
  rw [hb3_or]; split
  · rename_i h; rw [if_pos (hfinal.mp h)]
  · rename_i h; rw [if_neg (fun hab => h (hfinal.mpr hab))]

-- ============================================================================
-- ADD correctness: carry chain produces (a + b) limbs
-- ============================================================================

/-- Each limb of a + b equals the carry-chain result at that limb position. -/
theorem add_carry_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let result3 := psum3 + carry2
    (a + b).getLimb 0 = sum0 ∧
    (a + b).getLimb 1 = result1 ∧
    (a + b).getLimb 2 = result2 ∧
    (a + b).getLimb 3 = result3 := by
  sorry

-- ============================================================================
-- SUB correctness: borrow chain produces (a - b) limbs
-- ============================================================================

/-- Each limb of a - b equals the borrow-chain result at that limb position. -/
theorem sub_borrow_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    (a - b).getLimb 0 = diff0 ∧
    (a - b).getLimb 1 = result1 ∧
    (a - b).getLimb 2 = result2 ∧
    (a - b).getLimb 3 = result3 := by
  sorry

-- ============================================================================
-- SLT correctness: signed comparison decomposition
-- ============================================================================

/-- The SLT result equals `if BitVec.slt a b then 1 else 0`. -/
theorem slt_result_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    -- Lower 3 limbs borrow chain
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs
    let slt_msb := if BitVec.slt a3 b3 then (1 : Word) else 0
    let result := if a3 = b3 then borrow2 else slt_msb
    result = if BitVec.slt a b then (1 : Word) else 0 := by
  sorry

end EvmWord

end EvmAsm.Rv64
