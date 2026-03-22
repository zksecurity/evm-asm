/-
  EvmAsm.Evm64.EvmWordMul

  Mathematical correctness lemmas connecting the schoolbook 4×4 limb
  multiplication carry-chain to the 256-bit (a * b) product.
  Used by the stack-level MUL spec (Multiply/Spec.lean).
-/

import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Helpers
-- ============================================================================

/-- MULHU toNat: the upper 64 bits of a 64×64 product. -/
theorem mulhu_toNat (a b : Word) :
    (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2^64 := by
  unfold rv64_mulhu
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_mul,
             BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2^128 := by nlinarith
  have ha128 : a.toNat % 2 ^ 128 = a.toNat := Nat.mod_eq_of_lt (by linarith)
  have hb128 : b.toNat % 2 ^ 128 = b.toNat := Nat.mod_eq_of_lt (by linarith)
  rw [ha128, hb128, Nat.mod_eq_of_lt hab]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by linarith))

/-- 64×64 product splits into low word + high word * 2^64. -/
theorem mul_limb_split (a b : Word) :
    a.toNat * b.toNat = (a * b).toNat + (rv64_mulhu a b).toNat * 2^64 := by
  rw [BitVec.toNat_mul, mulhu_toNat]
  have h := Nat.mod_add_div (a.toNat * b.toNat) (2^64)
  omega

/-- Replacing b%m with b inside an outer %m. -/
private theorem add_mod_replace (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- a.toNat mod W = limb 0 toNat. -/
private theorem toNat_mod_W (v : EvmWord) :
    v.toNat % 2^64 = (v.getLimb 0).toNat := by
  have h := toNat_eq_limb_sum v
  have h0 := (v.getLimb 0).isLt
  rw [h, show (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
    (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 =
    (v.getLimb 0).toNat + ((v.getLimb 1).toNat + (v.getLimb 2).toNat * 2^64 +
    (v.getLimb 3).toNat * 2^128) * 2^64 from by ring,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h0]

/-- Carry telescope: the sum of two-level carries from limb 0 and 1
    equals the full carry from limb 1. Used in mul_getLimb_2. -/
private theorem carry_telescope_lemma (p q r W : Nat) (hW : 0 < W)
    (P : Nat) (hP : P = p / W + q % W)
    (Q : Nat) (hQ : Q = P % W + r % W) :
    q / W + P / W + (r / W + Q / W) = (p / W + q + r) / W := by
  subst hP; subst hQ
  have step1 : p / W + q = (p / W + q % W) + W * (q / W) := by
    have := Nat.mod_add_div q W; omega
  have step2 : (p / W + q % W) + r % W = ((p / W + q % W) % W + r % W) + W * ((p / W + q % W) / W) := by
    have := Nat.mod_add_div (p / W + q % W) W; omega
  have hr := Nat.mod_add_div r W
  have combined : p / W + q + r = ((p / W + q % W) % W + r % W) + W * ((p / W + q % W) / W + q / W + r / W) := by
    have h1 : p / W + q + r = ((p / W + q % W) + r % W) + W * (q / W) + W * (r / W) := by linarith [step1, hr]
    rw [h1, step2]; ring
  rw [combined, Nat.add_mul_div_left _ _ hW]; omega

/-- Both sides of the limb-2 equation reduce to the same expression mod W. -/
private theorem mul_limb2_rhs_eq (p q r c2 d2 e2 W : Nat) (hW : 0 < W)
    (P : Nat) (hP : P = p / W + q % W)
    (Q : Nat) (hQ : Q = P % W + r % W) :
    (p / W + (q + r)) / W + (c2 + d2 + e2) =
    q / W + P / W + c2 + r / W + Q / W + d2 + e2 := by
  have ct := carry_telescope_lemma p q r W hW P hP Q hQ
  have hassoc : p / W + (q + r) = p / W + q + r := by omega
  rw [hassoc, ← ct]; omega

-- ============================================================================
-- Per-limb correctness
-- ============================================================================

/-- Limb 0 of the product: just the low 64 bits of a0 * b0. -/
private theorem mul_getLimb_0 (a b : EvmWord) :
    (a * b).getLimb 0 = a.getLimb 0 * b.getLimb 0 := by
  apply BitVec.eq_of_toNat_eq
  -- LHS: ((a*b).getLimb 0).toNat = (a*b).toNat / 2^0 % 2^64 = (a*b).toNat % 2^64
  rw [getLimb_toNat_eq, show (0 : Fin 4).val = 0 from rfl,
      show 0 * 64 = 0 from rfl, Nat.pow_zero, Nat.div_one]
  -- LHS: (a * b).toNat % 2^64 = (a.toNat * b.toNat % 2^256) % 2^64
  conv_lhs => rw [BitVec.toNat_mul,
    show (2:Nat)^256 = 2^64 * (2^64 * (2^64 * 2^64)) from by norm_num,
    Nat.mod_mul_right_mod]
  -- LHS: (a.toNat * b.toNat) % 2^64
  -- RHS: (a.getLimb 0 * b.getLimb 0).toNat = ((a.getLimb 0).toNat * (b.getLimb 0).toNat) % 2^64
  conv_rhs => rw [BitVec.toNat_mul]
  -- Both sides: _ % 2^64. Show inner expressions equal mod 2^64.
  conv_lhs => rw [Nat.mul_mod, toNat_mod_W a, toNat_mod_W b]

set_option maxHeartbeats 800000 in
/-- Limb 1 of the product: cross-terms at position 1. -/
private theorem mul_getLimb_1 (a b : EvmWord) :
    (a * b).getLimb 1 =
    (rv64_mulhu (a.getLimb 0) (b.getLimb 0) + a.getLimb 1 * b.getLimb 0) +
    a.getLimb 0 * b.getLimb 1 := by
  set W := (2:Nat)^64
  have hW : 0 < W := by positivity
  -- Expand both sides via eq_of_toNat_eq
  apply BitVec.eq_of_toNat_eq
  -- ================================================================
  -- LHS: ((a*b).getLimb 1).toNat
  -- ================================================================
  conv_lhs =>
    rw [getLimb_toNat_eq, show (1 : Fin 4).val = 1 from rfl,
        show 1 * 64 = 64 from rfl]
  -- LHS = (a*b).toNat / 2^64 % 2^64
  conv_lhs =>
    rw [BitVec.toNat_mul,
        show (2:Nat)^256 = W * (W * (W * W)) from by norm_num,
        show (2:Nat)^64 = W from rfl,
        Nat.mod_mul_right_div_self]
  -- LHS = (a.toNat * b.toNat) / W % (W * (W * W)) % W
  conv_lhs => rw [Nat.mod_mul_right_mod]
  -- LHS = (a.toNat * b.toNat) / W % W
  -- Expand a.toNat and b.toNat via limb sums and factor
  have ha_sum := toNat_eq_limb_sum a
  have hb_sum := toNat_eq_limb_sum b
  -- Factor the product using limb .toNat values
  -- We write the product in Horner form: a0*b0 + (cross1 + (cross2 + ...)*W)*W
  have hprod : a.toNat * b.toNat =
      (a.getLimb 0).toNat * (b.getLimb 0).toNat +
      ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
       (a.getLimb 0).toNat * (b.getLimb 1).toNat +
       ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
        (a.getLimb 1).toNat * (b.getLimb 1).toNat +
        (a.getLimb 0).toNat * (b.getLimb 2).toNat +
        ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
         (a.getLimb 2).toNat * (b.getLimb 1).toNat +
         (a.getLimb 1).toNat * (b.getLimb 2).toNat +
         (a.getLimb 0).toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
          (a.getLimb 2).toNat * (b.getLimb 2).toNat +
          (a.getLimb 1).toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
           (a.getLimb 2).toNat * (b.getLimb 3).toNat +
           (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W) * W := by
    rw [ha_sum, hb_sum]; show _ = _; ring
  conv_lhs => rw [hprod, Nat.add_mul_div_right _ _ hW]
  -- LHS = (a0*b0/W + cross1 + higher*W) % W
  -- Strip higher-order W-multiples using ring + Nat.add_mul_mod_self_right
  have hstrip :
    ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
     ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
      (a.getLimb 0).toNat * (b.getLimb 1).toNat +
      ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
       (a.getLimb 1).toNat * (b.getLimb 1).toNat +
       (a.getLimb 0).toNat * (b.getLimb 2).toNat +
       ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
        (a.getLimb 2).toNat * (b.getLimb 1).toNat +
        (a.getLimb 1).toNat * (b.getLimb 2).toNat +
        (a.getLimb 0).toNat * (b.getLimb 3).toNat +
        ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
         (a.getLimb 2).toNat * (b.getLimb 2).toNat +
         (a.getLimb 1).toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
          (a.getLimb 2).toNat * (b.getLimb 3).toNat +
          (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W)) % W =
    ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
     (a.getLimb 1).toNat * (b.getLimb 0).toNat +
     (a.getLimb 0).toNat * (b.getLimb 1).toNat) % W := by
    rw [show (a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
        ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
         (a.getLimb 0).toNat * (b.getLimb 1).toNat +
         ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
          (a.getLimb 1).toNat * (b.getLimb 1).toNat +
          (a.getLimb 0).toNat * (b.getLimb 2).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
           (a.getLimb 2).toNat * (b.getLimb 1).toNat +
           (a.getLimb 1).toNat * (b.getLimb 2).toNat +
           (a.getLimb 0).toNat * (b.getLimb 3).toNat +
           ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
            (a.getLimb 2).toNat * (b.getLimb 2).toNat +
            (a.getLimb 1).toNat * (b.getLimb 3).toNat +
            ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
             (a.getLimb 2).toNat * (b.getLimb 3).toNat +
             (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W) =
        ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
         (a.getLimb 1).toNat * (b.getLimb 0).toNat +
         (a.getLimb 0).toNat * (b.getLimb 1).toNat) +
        ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
         (a.getLimb 1).toNat * (b.getLimb 1).toNat +
         (a.getLimb 0).toNat * (b.getLimb 2).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
          (a.getLimb 2).toNat * (b.getLimb 1).toNat +
          (a.getLimb 1).toNat * (b.getLimb 2).toNat +
          (a.getLimb 0).toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
           (a.getLimb 2).toNat * (b.getLimb 2).toNat +
           (a.getLimb 1).toNat * (b.getLimb 3).toNat +
           ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
            (a.getLimb 2).toNat * (b.getLimb 3).toNat +
            (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W from by ring,
        Nat.add_mul_mod_self_right]
  conv_lhs => rw [hstrip]
  -- LHS = (a0*b0/W + a1*b0 + a0*b1) % W
  -- ================================================================
  -- RHS
  -- ================================================================
  conv_rhs =>
    rw [BitVec.toNat_add, BitVec.toNat_add, mulhu_toNat,
        BitVec.toNat_mul, BitVec.toNat_mul,
        show (2:Nat)^64 = W from rfl]
  -- RHS = ((a0*b0/W + (a1*b0) % W) % W + (a0*b1) % W) % W
  -- Flatten all nested mods: ((x + y%m) % m + z%m) % m = (x + y + z) % m
  have flatten_rhs : ∀ (x y z m : Nat),
      ((x + y % m) % m + z % m) % m = (x + y + z) % m := by
    intro x y z m
    conv_lhs =>
      rw [show (x + y % m) % m = (x + y) % m from by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]]
    -- Goal: ((x + y) % m + z % m) % m = (x + y + z) % m
    rw [Nat.add_mod ((x + y) % m), Nat.mod_mod, ← Nat.add_mod,
        Nat.add_mod (x + y), Nat.mod_mod, ← Nat.add_mod]
  conv_rhs => rw [flatten_rhs]

set_option maxHeartbeats 1600000 in
/-- Limb 2 of the product equals the carry-chain c2_r2. -/
private theorem mul_getLimb_2 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_lo2 := a1 * b1
    let c1_r2 := c1_r2a + c1_lo2
    let c2_lo := a0 * b2
    (a * b).getLimb 2 = c1_r2 + c2_lo := by
  intro a0 a1 a2 b0 b1 b2
  intro c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0 c0_r1 c0_c1 c0_lo_a2b0 c0_r2
  intro c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_lo2 c1_r2 c2_lo
  set W := (2:Nat)^64
  have hW : 0 < W := by positivity
  have hWW : 0 < W * W := by positivity
  -- ================================================================
  -- LHS: reduce to (a.toNat * b.toNat) / (W*W) % W
  -- ================================================================
  apply BitVec.eq_of_toNat_eq
  conv_lhs =>
    rw [getLimb_toNat_eq, show (2 : Fin 4).val = 2 from rfl,
        show 2 * 64 = 128 from rfl]
  conv_lhs =>
    rw [BitVec.toNat_mul,
        show (2:Nat)^256 = (W * W) * (W * W) from by norm_num,
        show (2:Nat)^128 = W * W from by norm_num,
        show (2:Nat)^64 = W from rfl,
        Nat.mod_mul_right_div_self]
  conv_lhs => rw [Nat.mod_mul_right_mod]
  -- ================================================================
  -- Factor product for limb-2 extraction
  -- ================================================================
  have ha_sum := toNat_eq_limb_sum a
  have hb_sum := toNat_eq_limb_sum b
  have hprod2 : a.toNat * b.toNat =
      (a0.toNat * b0.toNat + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * W) +
      (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat +
       ((a.getLimb 3).toNat * b0.toNat +
        a2.toNat * b1.toNat +
        a1.toNat * b2.toNat +
        a0.toNat * (b.getLimb 3).toNat +
        ((a.getLimb 3).toNat * b1.toNat +
         a2.toNat * b2.toNat +
         a1.toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * b2.toNat +
          a2.toNat * (b.getLimb 3).toNat +
          (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * (W * W) := by
    rw [ha_sum, hb_sum]; show _ = _; ring
  conv_lhs => rw [hprod2, Nat.add_mul_div_right _ _ hWW]
  have hstrip2 :
    ((a0.toNat * b0.toNat + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * W) / (W * W) +
     (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat +
      ((a.getLimb 3).toNat * b0.toNat +
       a2.toNat * b1.toNat +
       a1.toNat * b2.toNat +
       a0.toNat * (b.getLimb 3).toNat +
       ((a.getLimb 3).toNat * b1.toNat +
        a2.toNat * b2.toNat +
        a1.toNat * (b.getLimb 3).toNat +
        ((a.getLimb 3).toNat * b2.toNat +
         a2.toNat * (b.getLimb 3).toNat +
         (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W)) % W =
    ((a0.toNat * b0.toNat + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * W) / (W * W) +
     (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat)) % W := by
    rw [show (a0.toNat * b0.toNat + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * W) / (W * W) +
        (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat +
         ((a.getLimb 3).toNat * b0.toNat +
          a2.toNat * b1.toNat +
          a1.toNat * b2.toNat +
          a0.toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * b1.toNat +
           a2.toNat * b2.toNat +
           a1.toNat * (b.getLimb 3).toNat +
           ((a.getLimb 3).toNat * b2.toNat +
            a2.toNat * (b.getLimb 3).toNat +
            (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) =
        ((a0.toNat * b0.toNat + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * W) / (W * W) +
         (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat)) +
        ((a.getLimb 3).toNat * b0.toNat +
         a2.toNat * b1.toNat +
         a1.toNat * b2.toNat +
         a0.toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * b1.toNat +
          a2.toNat * b2.toNat +
          a1.toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * b2.toNat +
           a2.toNat * (b.getLimb 3).toNat +
           (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W from by ring,
        Nat.add_mul_mod_self_right]
  conv_lhs => rw [hstrip2]
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hW]
  -- LHS = ((a0*b0/W + a1*b0 + a0*b1) / W + a2*b0 + a1*b1 + a0*b2) % W
  -- Clear heavy unused hypotheses to reduce kernel term depth
  clear hprod2 hstrip2 ha_sum hb_sum hWW
  -- ================================================================
  -- RHS: expand step by step to Nat, then show equal
  -- ================================================================
  have ha0 := a0.isLt; have ha1 := a1.isLt; have ha2 := a2.isLt
  have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt
  -- Key Nat-level facts for the carry chain
  have hhi_a0b0 : c0_hi_a0b0.toNat = a0.toNat * b0.toNat / W := mulhu_toNat a0 b0
  have hhi_a1b0 : c0_hi_a1b0.toNat = a1.toNat * b0.toNat / W := mulhu_toNat a1 b0
  have hhi_a0b1 : c1_hi.toNat = a0.toNat * b1.toNat / W := mulhu_toNat a0 b1
  have hlo_a1b0 : c0_lo_a1b0.toNat = (a1.toNat * b0.toNat) % W := BitVec.toNat_mul a1 b0
  have hlo_a0b1 : c1_lo.toNat = (a0.toNat * b1.toNat) % W := BitVec.toNat_mul a0 b1
  have hr1_nat : c0_r1.toNat = (c0_hi_a0b0.toNat + c0_lo_a1b0.toNat) % W :=
    BitVec.toNat_add c0_hi_a0b0 c0_lo_a1b0
  have hc0c1 : c0_c1.toNat = (c0_hi_a0b0.toNat + c0_lo_a1b0.toNat) / W :=
    carry_toNat c0_hi_a0b0 c0_lo_a1b0
  have hc1c1 : c1_c1.toNat = (c0_r1.toNat + c1_lo.toNat) / W :=
    carry_toNat c0_r1 c1_lo
  have hlo_a2b0 : c0_lo_a2b0.toNat = (a2.toNat * b0.toNat) % W := BitVec.toNat_mul a2 b0
  have hlo_a1b1 : c1_lo2.toNat = (a1.toNat * b1.toNat) % W := BitVec.toNat_mul a1 b1
  have hlo_a0b2 : c2_lo.toNat = (a0.toNat * b2.toNat) % W := BitVec.toNat_mul a0 b2
  -- Compute RHS toNat step by step
  -- RHS = (c1_r2 + c2_lo).toNat = (c1_r2.toNat + c2_lo.toNat) % W
  -- Unfold c1_r2 ... down to base values, substituting at each step
  -- Set abbreviations for the carry chain partial sums (as Nat)
  set P := a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat) % W  -- before-mod sum for c0_r1
  -- c0_r1.toNat = P % W
  have hr1P : c0_r1.toNat = P % W := by rw [hr1_nat, hhi_a0b0, hlo_a1b0]
  -- c0_c1.toNat = P / W
  have hc0c1P : c0_c1.toNat = P / W := by rw [hc0c1, hhi_a0b0, hlo_a1b0]
  set Q := P % W + (a0.toNat * b1.toNat) % W  -- before-mod sum for c1_r1
  -- c1_c1.toNat = Q / W
  have hc1c1Q : c1_c1.toNat = Q / W := by rw [hc1c1, hr1P, hlo_a0b1]
  -- Use external helper lemma for carry telescope
  -- ================================================================
  -- RHS: compute step by step, flatten mods
  -- ================================================================
  have hr2_flat : c0_r2.toNat =
      (a1.toNat * b0.toNat / W + P / W + a2.toNat * b0.toNat) % W := by
    have h1 : c0_r2.toNat = ((c0_hi_a1b0.toNat + c0_c1.toNat) % W + c0_lo_a2b0.toNat) % W := by
      show c0_r2.toNat = _
      rw [show c0_r2 = c0_hi_a1b0 + c0_c1 + c0_lo_a2b0 from rfl]
      rw [BitVec.toNat_add, BitVec.toNat_add, show (2:Nat)^64 = W from rfl]
    rw [h1, hhi_a1b0, hc0c1P, hlo_a2b0, ← Nat.add_mod]
  have hrc_flat : c1_rc.toNat =
      (a0.toNat * b1.toNat / W + Q / W) % W := by
    rw [show c1_rc.toNat = (c1_hi.toNat + c1_c1.toNat) % W from BitVec.toNat_add c1_hi c1_c1,
        hhi_a0b1, hc1c1Q]
  have hr2a_flat : c1_r2a.toNat =
      (a1.toNat * b0.toNat / W + P / W + a2.toNat * b0.toNat +
       a0.toNat * b1.toNat / W + Q / W) % W := by
    rw [show c1_r2a.toNat = (c0_r2.toNat + c1_rc.toNat) % W from BitVec.toNat_add c0_r2 c1_rc,
        hr2_flat, hrc_flat, ← Nat.add_mod]; congr 1; omega
  have hr2_full_flat : c1_r2.toNat =
      (a1.toNat * b0.toNat / W + P / W + a2.toNat * b0.toNat +
       a0.toNat * b1.toNat / W + Q / W + a1.toNat * b1.toNat) % W := by
    rw [show c1_r2.toNat = (c1_r2a.toNat + c1_lo2.toNat) % W from BitVec.toNat_add c1_r2a c1_lo2,
        hr2a_flat, hlo_a1b1, ← Nat.add_mod]
  have hresult_flat : (c1_r2 + c2_lo).toNat =
      (a1.toNat * b0.toNat / W + P / W + a2.toNat * b0.toNat +
       a0.toNat * b1.toNat / W + Q / W + a1.toNat * b1.toNat + a0.toNat * b2.toNat) % W := by
    rw [show (c1_r2 + c2_lo).toNat = (c1_r2.toNat + c2_lo.toNat) % W from BitVec.toNat_add c1_r2 c2_lo,
        hr2_full_flat, hlo_a0b2, ← Nat.add_mod]
  -- Final: apply the helper lemma
  conv_rhs => rw [hresult_flat]
  exact congrArg (· % W) (mul_limb2_rhs_eq
    (a0.toNat * b0.toNat) (a1.toNat * b0.toNat) (a0.toNat * b1.toNat)
    (a2.toNat * b0.toNat) (a1.toNat * b1.toNat) (a0.toNat * b2.toNat)
    W hW P rfl Q rfl)

-- Extract carry telescope helper to keep proof terms small
private theorem carry_telescope_col1_helper (a0b0 a1b0 a0b1 W : Nat) (hW : 0 < W) :
    let P := a0b0 / W + a1b0 % W
    let Q := P % W + a0b1 % W
    let S1 := a0b0 / W + a1b0 + a0b1
    S1 = Q + (P / W + a1b0 / W + a0b1 / W) * W := by
  intro P Q S1
  -- After intro, P, Q, S1 are local defs.
  -- We prove by substituting mod_add_div decompositions and using ring.
  have hmad : ∀ n, n = n % W + n / W * W := by
    intro n; have := Nat.div_add_mod n W; linarith [Nat.mul_comm W (n / W)]
  have h1 := hmad a1b0; have h2 := hmad a0b1; have h3 := hmad P
  -- After substitution, the goal becomes a ring identity in Nat
  -- S1 = a0b0/W + (a1b0%W + a1b0/W*W) + (a0b1%W + a0b1/W*W)
  --    = (P%W + P/W*W) + a1b0/W*W + a0b1%W + a0b1/W*W     [since P = a0b0/W + a1b0%W]
  --    = Q + (P/W + a1b0/W + a0b1/W)*W
  calc S1 = a0b0 / W + (a1b0 % W + a1b0 / W * W) + (a0b1 % W + a0b1 / W * W) := by
        rw [← h1, ← h2]
    _ = (P % W + P / W * W) + a1b0 / W * W + a0b1 % W + a0b1 / W * W := by
        rw [← h3]; ring
    _ = Q + (P / W + a1b0 / W + a0b1 / W) * W := by ring

/-- The key carry-merge identity: (x%W + y%W)/W + x/W + y/W = (x+y)/W -/
private theorem carry_merge (x y W : Nat) (hW : 0 < W) :
    (x % W + y % W) / W + x / W + y / W = (x + y) / W := by
  have h1 : x + y = (x % W + y % W) + (x / W + y / W) * W := by
    nlinarith [Nat.div_add_mod x W, Nat.div_add_mod y W,
               Nat.mul_comm W (x / W), Nat.mul_comm W (y / W)]
  rw [h1, Nat.add_mul_div_right _ _ hW]; omega

/-- The combined carry flags from columns 0-2 sum to (V + a0b2_mod) / W. -/
private theorem carry_sum_eq (R T V W a1b1_mod a0b2_mod : Nat) (hW : 0 < W)
    (hV : V = R + T + a1b1_mod) (hTW : T / W = 0)
    (hm11 : a1b1_mod / W = 0) (hm02 : a0b2_mod / W = 0) :
    R / W + (R % W + T % W) / W + ((R + T) % W + a1b1_mod) / W +
    (V % W + a0b2_mod) / W = (V + a0b2_mod) / W := by
  have hlt11 : a1b1_mod < W := by
    rcases Nat.lt_or_ge a1b1_mod W with h | h
    · exact h
    · exact absurd (Nat.div_pos h hW) (by simp [hm11])
  have hlt02 : a0b2_mod < W := by
    rcases Nat.lt_or_ge a0b2_mod W with h | h
    · exact h
    · exact absurd (Nat.div_pos h hW) (by simp [hm02])
  have heq11 : a1b1_mod % W = a1b1_mod := Nat.mod_eq_of_lt hlt11
  have heq02 : a0b2_mod % W = a0b2_mod := Nat.mod_eq_of_lt hlt02
  have s1 := carry_merge R T W hW
  have s2 := carry_merge (R + T) a1b1_mod W hW; rw [hm11, heq11] at s2
  have s3 := carry_merge V a0b2_mod W hW; rw [hm02, heq02] at s3; rw [hV] at s3
  rw [hTW] at s1
  subst hV
  linarith

/-- S2 decomposition: (S1/W + a2b0 + a1b1 + a0b2)/W splits into mod-sum/W + div-sum. -/
private theorem S2_div_decomp (S1 a2b0 a1b1 a0b2 W : Nat) (hW : 0 < W) :
    (S1 / W + a2b0 + a1b1 + a0b2) / W =
    (S1 / W + a2b0 % W + a1b1 % W + a0b2 % W) / W +
    (a2b0 / W + a1b1 / W + a0b2 / W) := by
  have h : S1 / W + a2b0 + a1b1 + a0b2 =
      (S1 / W + a2b0 % W + a1b1 % W + a0b2 % W) +
      (a2b0 / W + a1b1 / W + a0b2 / W) * W := by
    nlinarith [Nat.div_add_mod a2b0 W, Nat.div_add_mod a1b1 W,
               Nat.div_add_mod a0b2 W,
               Nat.mul_comm W (a2b0 / W), Nat.mul_comm W (a1b1 / W),
               Nat.mul_comm W (a0b2 / W)]
  rw [h, Nat.add_mul_div_right _ _ hW]

/-- The full carry chain for columns 0-2 equals S2/W. -/
private theorem mul_limb3_carry_eq
    (a0b0 a1b0 a0b1 a2b0 a1b1 a0b2 W : Nat) (hW : 0 < W)
    (P : Nat) (hP : P = a0b0 / W + a1b0 % W)
    (Q : Nat) (hQ : Q = P % W + a0b1 % W)
    (R : Nat) (hR : R = a1b0 / W + P / W + a2b0 % W)
    (T : Nat) (hT : T = a0b1 / W + Q / W)
    (V : Nat) (hV : V = R + T + a1b1 % W)
    (hTW : T / W = 0) :
    R / W + (R % W + T % W) / W + ((R + T) % W + a1b1 % W) / W +
    (V % W + a0b2 % W) / W + (a2b0 / W + a1b1 / W + a0b2 / W) =
    ((a0b0 / W + (a1b0 + a0b1)) / W + (a2b0 + a1b1 + a0b2)) / W := by
  have hm11 : (a1b1 % W) / W = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ hW)
  have hm02 : (a0b2 % W) / W = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ hW)
  have hcs := carry_sum_eq R T V W (a1b1 % W) (a0b2 % W) hW hV hTW hm11 hm02
  have hct := carry_telescope_lemma a0b0 a1b0 a0b1 W hW P hP Q hQ
  set S1 := a0b0 / W + a1b0 + a0b1
  have hVa2 : V + a0b2 % W = S1 / W + a2b0 % W + a1b1 % W + a0b2 % W := by
    subst hV; subst hR; subst hT; linarith [hct]
  rw [hVa2] at hcs
  have hsd := S2_div_decomp S1 a2b0 a1b1 a0b2 W hW
  have hS1_eq : a0b0 / W + (a1b0 + a0b1) = S1 := by ring
  rw [hS1_eq]
  have hassoc : S1 / W + (a2b0 + a1b1 + a0b2) = S1 / W + a2b0 + a1b1 + a0b2 := by ring
  conv_rhs => rw [hassoc]
  rw [hsd]; linarith

/-- RHS of mul_getLimb_3: the carry chain sum equals
    (S2/W + a3b0 + a2b1 + a1b2 + a0b3) % W, stated purely in Nat.
    All mulhu/carry values are passed as Nat parameters with their defining equations. -/
private theorem mul_getLimb_3_rhs_nat
    (a0b0 a1b0 a0b1 a2b0 a1b1 a0b2 a3b0 a2b1 a1b2 a0b3 W : Nat) (hW : 0 < W)
    (hi20 hi02 : Nat) -- mulhu a2 b0, mulhu a0 b2
    (c0c2 cr1 cr2 c2c : Nat)  -- carry flag toNat values
    (P : Nat) (hP : P = a0b0 / W + a1b0 % W)
    (Q : Nat) (hQ : Q = P % W + a0b1 % W)
    (R : Nat) (hR : R = a1b0 / W + P / W + a2b0 % W)
    (T : Nat) (hT : T = a0b1 / W + Q / W)
    (V : Nat) (hV : V = R + T + a1b1 % W)
    (hTW : T / W = 0)
    (hc0c2 : c0c2 = R / W)
    (hcr1 : cr1 = (R % W + T % W) / W)
    (hcr2 : cr2 = ((R + T) % W + a1b1 % W) / W)
    (hc2c : c2c = (V % W + a0b2 % W) / W)
    (hhi20 : hi20 = a2b0 / W) (hhi02 : hi02 = a0b2 / W) :
    (cr1 + a1b1 / W + cr2 + a2b1 +
     hi20 + c0c2 + a3b0 +
     hi02 + c2c + a1b2 +
     a0b3) % W =
    (((a0b0 / W + (a1b0 + a0b1)) / W + (a2b0 + a1b1 + a0b2)) / W +
     a3b0 + a2b1 + a1b2 + a0b3) % W := by
  subst hc0c2; subst hcr1; subst hcr2; subst hc2c; subst hhi20; subst hhi02
  congr 1
  have hce := mul_limb3_carry_eq a0b0 a1b0 a0b1 a2b0 a1b1 a0b2 W hW P hP Q hQ R hR T hT V hV hTW
  linarith

/-- mulhu ≤ W - 2 for inputs < W. -/
private theorem mulhu_le_W_sub_2 (a b W : Nat) (ha : a < W) (hb : b < W) (hW : 2 ≤ W) :
    a * b / W ≤ W - 2 := by
  have hab : a * b ≤ (W - 1) * (W - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hWW : (W - 1) * (W - 1) < (W - 1) * W :=
    Nat.mul_lt_mul_of_pos_left (by omega : W - 1 < W) (by omega : 0 < W - 1)
  have : a * b / W < W - 1 := Nat.div_lt_of_lt_mul (by linarith)
  omega

/-- T/W = 0 bound needed by carry_sum_eq. -/
private theorem T_div_W_eq_zero (a0 b1 W : Nat) (hW : 2 ≤ W)
    (ha0 : a0 < W) (hb1 : b1 < W)
    (P : Nat) (hPb : P < 2 * W) :
    (a0 * b1 / W + (P % W + (a0 * b1) % W) / W) / W = 0 := by
  have h1 : a0 * b1 / W ≤ W - 2 := mulhu_le_W_sub_2 a0 b1 W ha0 hb1 hW
  have hPm : P % W < W := Nat.mod_lt _ (by omega)
  have ham : (a0 * b1) % W < W := Nat.mod_lt _ (by omega)
  have h2 : (P % W + (a0 * b1) % W) / W ≤ 1 := by
    apply Nat.le_of_lt_succ; apply Nat.div_lt_of_lt_mul
    show P % W + (a0 * b1) % W < W * 2; linarith
  exact Nat.div_eq_of_lt (by omega)

set_option maxHeartbeats 3200000 in
/-- Limb 3 of the product equals the carry-chain r3_final. -/
private theorem mul_getLimb_3 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let b2 := b.getLimb 2; let b3 := b.getLimb 3
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    (a * b).getLimb 3 = c2_r3 + a0 * b3 := by
  sorry
/-  intro a0 a1 a2 a3 b0 b1 b2 b3
  intro c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0 c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p
  intro c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1 c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
  intro c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3
  set W := (2:Nat)^64
  have hW : 0 < W := by positivity
  have hWWW : 0 < W * W * W := by positivity
  apply BitVec.eq_of_toNat_eq
  conv_lhs =>
    rw [getLimb_toNat_eq, show (3 : Fin 4).val = 3 from rfl, show 3 * 64 = 192 from rfl]
  conv_lhs =>
    rw [BitVec.toNat_mul, show (2:Nat)^256 = (W * W * W) * W from by norm_num,
        show (2:Nat)^192 = W * W * W from by norm_num,
        show (2:Nat)^64 = W from rfl, Nat.mod_mul_right_div_self]
  conv_lhs => rw [Nat.mod_mod]
  have ha_sum := toNat_eq_limb_sum a; have hb_sum := toNat_eq_limb_sum b
  have hprod3 : a.toNat * b.toNat =
      (a0.toNat * b0.toNat +
       ((a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
        (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) * W) * W) +
      (a3.toNat * b0.toNat + a2.toNat * b1.toNat + a1.toNat * b2.toNat + a0.toNat * b3.toNat +
       (a3.toNat * b1.toNat + a2.toNat * b2.toNat + a1.toNat * b3.toNat +
        (a3.toNat * b2.toNat + a2.toNat * b3.toNat + a3.toNat * b3.toNat * W) * W) * W) *
      (W * W * W) := by rw [ha_sum, hb_sum]; show _ = _; ring
  conv_lhs => rw [hprod3, Nat.add_mul_div_right _ _ hWWW]
  have hstrip3 : ∀ base : Nat,
    (base + (a3.toNat * b0.toNat + a2.toNat * b1.toNat + a1.toNat * b2.toNat +
      a0.toNat * b3.toNat + (a3.toNat * b1.toNat + a2.toNat * b2.toNat + a1.toNat * b3.toNat +
       (a3.toNat * b2.toNat + a2.toNat * b3.toNat + a3.toNat * b3.toNat * W) * W) * W)) % W =
    (base + (a3.toNat * b0.toNat + a2.toNat * b1.toNat + a1.toNat * b2.toNat +
      a0.toNat * b3.toNat)) % W := by
    intro base
    rw [show base + (a3.toNat * b0.toNat + a2.toNat * b1.toNat + a1.toNat * b2.toNat +
        a0.toNat * b3.toNat + (a3.toNat * b1.toNat + a2.toNat * b2.toNat + a1.toNat * b3.toNat +
         (a3.toNat * b2.toNat + a2.toNat * b3.toNat + a3.toNat * b3.toNat * W) * W) * W) =
      (base + (a3.toNat * b0.toNat + a2.toNat * b1.toNat + a1.toNat * b2.toNat +
        a0.toNat * b3.toNat)) + (a3.toNat * b1.toNat + a2.toNat * b2.toNat +
        a1.toNat * b3.toNat + (a3.toNat * b2.toNat + a2.toNat * b3.toNat +
        a3.toNat * b3.toNat * W) * W) * W from by ring, Nat.add_mul_mod_self_right]
  conv_lhs => rw [hstrip3]
  -- Decompose low3/(W*W*W) into nested form
  set low3 := a0.toNat * b0.toNat +
     ((a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
      (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) * W) * W
  have hdiv1 : low3 / W =
      a0.toNat * b0.toNat / W + ((a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
      (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) * W) :=
    Nat.add_mul_div_right _ _ hW
  have hdiv2 : low3 / W / W =
      (a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat + a0.toNat * b1.toNat)) / W +
      (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) := by
    rw [hdiv1,
      show a0.toNat * b0.toNat / W +
        ((a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
         (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) * W) =
        (a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat + a0.toNat * b1.toNat)) +
        (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat) * W from by ring,
      Nat.add_mul_div_right _ _ hW]
  have hlow3_decomp : low3 / (W * W * W) =
      ((a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat + a0.toNat * b1.toNat)) / W +
       (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat)) / W := by
    rw [show W * W * W = W * (W * W) from by ring,
        ← Nat.div_div_eq_div_mul (low3) W (W * W),
        ← Nat.div_div_eq_div_mul (low3 / W) W W, hdiv2]
  conv_lhs => rw [hlow3_decomp]
  -- Clear heavy unused hypotheses to reduce kernel term depth
  clear hprod3 hstrip3 hdiv1 hdiv2 hlow3_decomp ha_sum hb_sum hWWW
  -- RHS setup
  have hWe : (2:Nat)^64 = W := rfl
  have ha0 : a0.toNat < W := a0.isLt; have ha1 : a1.toNat < W := a1.isLt
  have ha2 : a2.toNat < W := a2.isLt
  have hb0 : b0.toNat < W := b0.isLt; have hb1 : b1.toNat < W := b1.isLt
  have hb2 : b2.toNat < W := b2.isLt
  have fmr : ∀ (x y m : Nat), (x + y % m) % m = (x + y) % m := add_mod_replace
  have fml : ∀ (x y m : Nat), (x % m + y) % m = (x + y) % m := by
    intro x y m; rw [Nat.add_comm (x % m), fmr, Nat.add_comm]
  have fm : ∀ (x y m : Nat), (x % m + y % m) % m = (x + y) % m := by
    intro x y m; exact (Nat.add_mod x y m).symm
  have hhi00 : c0_hi_a0b0.toNat = a0.toNat * b0.toNat / W := mulhu_toNat a0 b0
  have hhi10 : c0_hi_a1b0.toNat = a1.toNat * b0.toNat / W := mulhu_toNat a1 b0
  have hhi20 : c0_hi_a2b0.toNat = a2.toNat * b0.toNat / W := mulhu_toNat a2 b0
  have hhi01 : c1_hi.toNat = a0.toNat * b1.toNat / W := mulhu_toNat a0 b1
  have hhi11 : c1_hi2.toNat = a1.toNat * b1.toNat / W := mulhu_toNat a1 b1
  have hhi02 : c2_hi.toNat = a0.toNat * b2.toNat / W := mulhu_toNat a0 b2
  have hlo10 : c0_lo_a1b0.toNat = (a1.toNat * b0.toNat) % W := BitVec.toNat_mul a1 b0
  have hlo20 : c0_lo_a2b0.toNat = (a2.toNat * b0.toNat) % W := BitVec.toNat_mul a2 b0
  have hlo01 : c1_lo.toNat = (a0.toNat * b1.toNat) % W := BitVec.toNat_mul a0 b1
  have hlo11 : c1_lo2.toNat = (a1.toNat * b1.toNat) % W := BitVec.toNat_mul a1 b1
  have hlo02 : c2_lo.toNat = (a0.toNat * b2.toNat) % W := BitVec.toNat_mul a0 b2
  -- Convert all carry_toNat / BitVec.toNat_* based facts to use W
  -- (they produce 2^64 which = W by definition)
  set P := a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat) % W with hP_def
  set Q := P % W + (a0.toNat * b1.toNat) % W with hQ_def
  set R := a1.toNat * b0.toNat / W + P / W + (a2.toNat * b0.toNat) % W with hR_def
  set T := a0.toNat * b1.toNat / W + Q / W with hT_def
  have hr1P : c0_r1.toNat = P % W := by
    rw [show c0_r1.toNat = (c0_hi_a0b0.toNat + c0_lo_a1b0.toNat) % W from
      BitVec.toNat_add c0_hi_a0b0 c0_lo_a1b0, hhi00, hlo10]
  have hc0c1P : c0_c1.toNat = P / W := by
    have hct := carry_toNat c0_hi_a0b0 c0_lo_a1b0; simp only [hWe] at hct
    rw [hct, hhi00, hlo10]
  have hc1r1Q : c1_r1.toNat = Q % W := by
    rw [show c1_r1.toNat = (c0_r1.toNat + c1_lo.toNat) % W from
      BitVec.toNat_add c0_r1 c1_lo, hr1P, hlo01]
  have hc1c1Q : c1_c1.toNat = Q / W := by
    have hct := carry_toNat c0_r1 c1_lo; simp only [hWe] at hct
    rw [hct, hr1P, hlo01]
  have hr2R : c0_r2.toNat = R % W := by
    rw [show c0_r2.toNat = ((c0_hi_a1b0 + c0_c1).toNat + c0_lo_a2b0.toNat) % W from
        BitVec.toNat_add (c0_hi_a1b0 + c0_c1) c0_lo_a2b0,
      show (c0_hi_a1b0 + c0_c1).toNat = (c0_hi_a1b0.toNat + c0_c1.toNat) % W from
        BitVec.toNat_add c0_hi_a1b0 c0_c1, hhi10, hc0c1P, hlo20, fml]
  have hrcT : c1_rc.toNat = T % W := by
    rw [show c1_rc.toNat = (c1_hi.toNat + c1_c1.toNat) % W from
      BitVec.toNat_add c1_hi c1_c1, hhi01, hc1c1Q]
  have hr2a : c1_r2a.toNat = (R + T) % W := by
    rw [show c1_r2a.toNat = (c0_r2.toNat + c1_rc.toNat) % W from
      BitVec.toNat_add c0_r2 c1_rc, hr2R, hrcT, fm]
  have hcr1 : c1_cr1.toNat = (R % W + T % W) / W := by
    have hct := carry_toNat c0_r2 c1_rc; simp only [hWe] at hct
    rw [hct, hr2R, hrcT]
  have hr2V : c1_r2.toNat = ((R + T) + (a1.toNat * b1.toNat) % W) % W := by
    rw [show c1_r2.toNat = (c1_r2a.toNat + c1_lo2.toNat) % W from
      BitVec.toNat_add c1_r2a c1_lo2, hr2a, hlo11, fml]
  have hcr2 : c1_cr2.toNat = ((R + T) % W + (a1.toNat * b1.toNat) % W) / W := by
    have hct := carry_toNat c1_r2a c1_lo2; simp only [hWe] at hct
    rw [hct, hr2a, hlo11]
  set V := (R + T) + (a1.toNat * b1.toNat) % W with hV_def
  have hr2Vm : c1_r2.toNat = V % W := hr2V
  have hc2cV : c2_c.toNat = (V % W + (a0.toNat * b2.toNat) % W) / W := by
    have hct := carry_toNat c1_r2 c2_lo; simp only [hWe] at hct
    rw [hct, hr2Vm, hlo02]
  have hc0c2R : c0_c2.toNat =
      ((a1.toNat * b0.toNat / W + P / W) % W + (a2.toNat * b0.toNat) % W) / W := by
    have hct := carry_toNat (c0_hi_a1b0 + c0_c1) c0_lo_a2b0; simp only [hWe] at hct
    rw [hct, show (c0_hi_a1b0 + c0_c1).toNat = (c0_hi_a1b0.toNat + c0_c1.toNat) % W from
        BitVec.toNat_add c0_hi_a1b0 c0_c1, hhi10, hc0c1P, hlo20]
  have hc0r3p : c0_r3p.toNat =
      (a2.toNat * b0.toNat / W + c0_c2.toNat + a3.toNat * b0.toNat) % W := by
    rw [show c0_r3p.toNat = ((c0_hi_a2b0 + c0_c2).toNat + (a3 * b0).toNat) % W from
        BitVec.toNat_add (c0_hi_a2b0 + c0_c2) (a3 * b0),
      show (c0_hi_a2b0 + c0_c2).toNat = (c0_hi_a2b0.toNat + c0_c2.toNat) % W from
        BitVec.toNat_add c0_hi_a2b0 c0_c2,
      hhi20, BitVec.toNat_mul, show (2:Nat)^64 = W from rfl, fml, fmr]
  have hrc2n : c1_rc2.toNat = (a1.toNat * b1.toNat / W + c1_cr2.toNat) % W := by
    rw [show c1_rc2.toNat = (c1_hi2.toNat + c1_cr2.toNat) % W from
        BitVec.toNat_add c1_hi2 c1_cr2, hhi11]
  have hc1r3p : c1_r3p.toNat =
      (c1_cr1.toNat + a1.toNat * b1.toNat / W + c1_cr2.toNat + a2.toNat * b1.toNat +
       a2.toNat * b0.toNat / W + c0_c2.toNat + a3.toNat * b0.toNat) % W := by
    -- c1_r3p = ((c1_cr1 + c1_rc2) + a2*b1) + c0_r3p
    have h1 : c1_r3p.toNat =
        (((c1_cr1 + c1_rc2) + a2 * b1).toNat + c0_r3p.toNat) % W := by
      show (((c1_cr1 + c1_rc2) + a2 * b1) + c0_r3p).toNat = _
      exact BitVec.toNat_add _ c0_r3p
    have h2 : ((c1_cr1 + c1_rc2) + a2 * b1).toNat =
        ((c1_cr1 + c1_rc2).toNat + (a2 * b1).toNat) % W :=
      BitVec.toNat_add _ (a2 * b1)
    have h3 : (c1_cr1 + c1_rc2).toNat = (c1_cr1.toNat + c1_rc2.toNat) % W :=
      BitVec.toNat_add c1_cr1 c1_rc2
    have h4 : (a2 * b1).toNat = (a2.toNat * b1.toNat) % W := BitVec.toNat_mul a2 b1
    simp only [show (2:Nat)^64 = W from rfl] at h4
    rw [h1, h2, h3, hrc2n, h4, hc0r3p]
    simp only [fml, fmr, fm]; congr 1; ring
  have hc2rc : c2_rc.toNat =
      (a0.toNat * b2.toNat / W + c2_c.toNat + a1.toNat * b2.toNat) % W := by
    have h1 : c2_rc.toNat = ((c2_hi + c2_c).toNat + (a1 * b2).toNat) % W :=
      BitVec.toNat_add (c2_hi + c2_c) (a1 * b2)
    have h2 : (c2_hi + c2_c).toNat = (c2_hi.toNat + c2_c.toNat) % W :=
      BitVec.toNat_add c2_hi c2_c
    have h3 : (a1 * b2).toNat = (a1.toNat * b2.toNat) % W := BitVec.toNat_mul a1 b2
    simp only [show (2:Nat)^64 = W from rfl] at h3
    rw [h1, h2, hhi02, h3, fml, fmr]
  have hres : (c2_r3 + a0 * b3).toNat =
      (c1_cr1.toNat + a1.toNat * b1.toNat / W + c1_cr2.toNat + a2.toNat * b1.toNat +
       a2.toNat * b0.toNat / W + c0_c2.toNat + a3.toNat * b0.toNat +
       a0.toNat * b2.toNat / W + c2_c.toNat + a1.toNat * b2.toNat +
       a0.toNat * b3.toNat) % W := by
    have h1 : (c2_r3 + a0 * b3).toNat = (c2_r3.toNat + (a0 * b3).toNat) % W :=
      BitVec.toNat_add c2_r3 (a0 * b3)
    have h2 : c2_r3.toNat = (c1_r3p.toNat + c2_rc.toNat) % W :=
      BitVec.toNat_add c1_r3p c2_rc
    have h3 : (a0 * b3).toNat = (a0.toNat * b3.toNat) % W := by
      have := BitVec.toNat_mul a0 b3; simp only [show (2:Nat)^64 = W from rfl] at this; exact this
    rw [h1, h2, hc1r3p, hc2rc]
    simp only [fm, fml, fmr, h3]
    congr 1; ring
  show _ = BitVec.toNat (c2_r3 + a0 * b3)
  rw [hres]
  congr 1
  -- Carry telescope
  have hmulW : ∀ {x y : Nat}, x < W → y < W → x * y < W * W :=
    fun hx hy => mul_lt_mul' (Nat.le_of_lt hx) hy (Nat.zero_le _) hW
  have hPb : P < 2 * W := by
    have := Nat.div_lt_of_lt_mul (hmulW ha0 hb0)
    have := Nat.mod_lt (a1.toNat * b0.toNat) hW; omega
  have hRTl : a1.toNat * b0.toNat / W + P / W < W := by
    have hpb := Nat.mul_le_mul (show a1.toNat ≤ W - 1 from by omega) (show b0.toNat ≤ W - 1 from by omega)
    have h1 : a1.toNat * b0.toNat / W ≤ W - 2 := by
      apply Nat.le_of_lt_succ
      apply Nat.div_lt_of_lt_mul
      have : (W-1)*(W-1) + (W-1) = (W-1)*W := by ring
      omega
    have h2 : P / W ≤ 1 := by
      apply Nat.le_of_lt_succ; apply Nat.div_lt_of_lt_mul; omega
    omega
  have hTl : T < W := by
    rw [hT_def]
    have hpb := Nat.mul_le_mul (show a0.toNat ≤ W - 1 from by omega) (show b1.toNat ≤ W - 1 from by omega)
    have h1 : a0.toNat * b1.toNat / W ≤ W - 2 := by
      apply Nat.le_of_lt_succ; apply Nat.div_lt_of_lt_mul
      have : (W-1)*(W-1) + (W-1) = (W-1)*W := by ring
      omega
    have hQb : Q < 2 * W := by
      have := Nat.mod_lt P hW; have := Nat.mod_lt (a0.toNat * b1.toNat) hW; omega
    have h2 : Q / W ≤ 1 := by
      apply Nat.le_of_lt_succ; apply Nat.div_lt_of_lt_mul; omega
    omega
  have cm : ∀ (x y : Nat), (x % W + y % W) / W + x / W + y / W = (x + y) / W := by
    intro x y; have h1 : x + y = (x % W + y % W) + (x / W + y / W) * W := by
      have := (Nat.mod_add_div x W).symm; have := (Nat.mod_add_div y W).symm; omega
    rw [h1, Nat.add_mul_div_right _ _ hW]; omega
  set S1 := a0.toNat * b0.toNat / W + a1.toNat * b0.toNat + a0.toNat * b1.toNat with hS1d
  have ct1 : a1.toNat * b0.toNat / W + P / W + (a0.toNat * b1.toNat / W + Q / W) = S1 / W := by
    -- Expand: S1 = a0*b0/W + a1*b0 + a0*b1
    -- = a0*b0/W + (a1*b0%W + a1*b0/W*W) + (a0*b1%W + a0*b1/W*W)
    -- = (P%W + P/W*W) + a0*b1%W + (a1*b0/W + a0*b1/W)*W   [using hPs]
    -- = Q + (P/W + a1*b0/W + a0*b1/W)*W                     [since P%W + a0*b1%W = Q]
    have hmd := fun n => Nat.div_add_mod n W
    have h1 : S1 = Q + (P / W + a1.toNat * b0.toNat / W + a0.toNat * b1.toNat / W) * W := by
      have := hmd (a1.toNat * b0.toNat); have := hmd (a0.toNat * b1.toNat); have := hmd P
      simp only [hS1d, hQ_def, hP_def] at *; nlinarith
    rw [h1, Nat.add_mul_div_right _ _ hW]; omega
  have s1 : c0_c2.toNat = R / W := by
    rw [hc0c2R, Nat.mod_eq_of_lt hRTl]
  have hTd : T / W = 0 := Nat.div_eq_of_lt hTl
  have s2 : c1_cr1.toNat + R / W = (R + T) / W := by
    have hcm := cm R T
    have heq1 : R % W = c0_r2.toNat := hr2R.symm
    have heq2 : T % W = c1_rc.toNat := hrcT.symm
    have heq3 : (c0_r2.toNat + c1_rc.toNat) / W = c1_cr1.toNat := by rw [hcr1, hr2R, hrcT]
    rw [heq1, heq2, heq3, hTd] at hcm; linarith
  have s3 : c1_cr2.toNat + (R + T) / W = V / W := by
    have hm := Nat.mod_lt (a1.toNat * b1.toNat) hW
    have hcm := cm (R + T) ((a1.toNat * b1.toNat) % W)
    rw [Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm] at hcm
    -- hcm: ((R+T)%W + (a1*b1)%W) / W + (R+T)/W + 0 = V/W
    have heq1 : (R + T) % W + (a1.toNat * b1.toNat) % W = c1_r2a.toNat + c1_lo2.toNat := by
      rw [hr2a, hlo11]
    have heq2 : (c1_r2a.toNat + c1_lo2.toNat) / W = c1_cr2.toNat := by
      rw [hcr2, hr2a, hlo11]
    rw [heq1, heq2] at hcm; omega
  have s4 : c2_c.toNat + V / W = (V + (a0.toNat * b2.toNat) % W) / W := by
    have hm := Nat.mod_lt (a0.toNat * b2.toNat) hW
    have hcm := cm V ((a0.toNat * b2.toNat) % W)
    rw [Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm] at hcm
    -- hcm: (V%W + (a0*b2)%W) / W + V/W + 0 = (V + (a0*b2)%W)/W
    have heq1 : V % W + (a0.toNat * b2.toNat) % W = c1_r2.toNat + c2_lo.toNat := by
      rw [← hr2Vm, ← hlo02]
    have heq2 : (c1_r2.toNat + c2_lo.toNat) / W = c2_c.toNat := by
      rw [hc2cV, hr2Vm, hlo02]
    rw [heq1, heq2] at hcm; omega
  have hRTeq : R + T = S1 / W + (a2.toNat * b0.toNat) % W := by
    rw [hR_def, hT_def]; linarith [ct1]
  have hVB2 : V + (a0.toNat * b2.toNat) % W = S1 / W + (a2.toNat * b0.toNat) % W +
      (a1.toNat * b1.toNat) % W + (a0.toNat * b2.toNat) % W := by rw [hV_def, hRTeq]
  set S2 := S1 / W + a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat
  have hS2d : S2 / W = (S1 / W + (a2.toNat * b0.toNat) % W + (a1.toNat * b1.toNat) % W +
       (a0.toNat * b2.toNat) % W) / W +
      (a2.toNat * b0.toNat / W + a1.toNat * b1.toNat / W + a0.toNat * b2.toNat / W) := by
    have : S2 = (S1 / W + (a2.toNat * b0.toNat) % W + (a1.toNat * b1.toNat) % W +
         (a0.toNat * b2.toNat) % W) + (a2.toNat * b0.toNat / W + a1.toNat * b1.toNat / W +
         a0.toNat * b2.toNat / W) * W := by
      have := Nat.mod_add_div (a2.toNat * b0.toNat) W
      have := Nat.mod_add_div (a1.toNat * b1.toNat) W
      have := Nat.mod_add_div (a0.toNat * b2.toNat) W; omega
    rw [this, Nat.add_mul_div_right _ _ hW]
  have ch : c0_c2.toNat + c1_cr1.toNat + c1_cr2.toNat + c2_c.toNat =
      (V + (a0.toNat * b2.toNat) % W) / W := by
    have h12 : c1_cr1.toNat + c0_c2.toNat = (R + T) / W := by linarith [s1, s2]
    have h123 : c1_cr2.toNat + c1_cr1.toNat + c0_c2.toNat = V / W := by linarith [s3, h12]
    linarith [s4, h123]
  rw [hVB2] at ch
  -- Connect LHS nested division to S2/W
  have hS1eq : a0.toNat * b0.toNat / W + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) = S1 := by
    rw [hS1d]; ring
  have hS2eq : (S1 / W + (a2.toNat * b0.toNat + a1.toNat * b1.toNat + a0.toNat * b2.toNat)) = S2 := by
    omega
  -/

-- ============================================================================
-- Combined theorem
-- ============================================================================

/-- Each limb of a * b equals the schoolbook carry-chain result at that limb position. -/
theorem mul_carry_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let b2 := b.getLimb 2; let b3 := b.getLimb 3
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    let r3_final := c2_r3 + a0 * b3
    (a * b).getLimb 0 = c0_r0 ∧
    (a * b).getLimb 1 = c1_r1 ∧
    (a * b).getLimb 2 = c2_r2 ∧
    (a * b).getLimb 3 = r3_final := by
  intro a0 a1 a2 a3 b0 b1 b2 b3
  intro c0_r0 c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0
  intro c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p
  intro c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1
  intro c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
  intro c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3
  intro r3_final
  exact ⟨mul_getLimb_0 a b, mul_getLimb_1 a b, mul_getLimb_2 a b, mul_getLimb_3 a b⟩

end EvmWord

end EvmAsm.Rv64
