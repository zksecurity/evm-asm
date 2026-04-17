/-
  EvmAsm.Evm64.DivMod.Spec

  Stack-level specs for the 256-bit EVM DIV and MOD programs using evmWordIs.

  Currently covers:
  - Zero divisor path (b = 0): evm_div_bzero_stack_spec, evm_mod_bzero_stack_spec
  - Normal path (b ≠ 0): TODO (needs semantic correctness bridge: EvmWord.div_correct / mod_correct)
-/

import EvmAsm.Evm64.DivMod.Compose
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Shared helpers for stack-level DIV/MOD specs
-- ============================================================================

/-- Weaken concrete register to existential ownership. -/
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Unfold `evmWordIs (sp+32) v` into four limb-level memory atoms at the
    absolute stack addresses `sp+32, sp+40, sp+48, sp+56`. Used by both the
    b=0 and (forthcoming) b≠0 stack specs to bridge between the separation-logic
    `evmWordIs` predicate and the raw limb atoms that the limb-level specs
    produce. -/
theorem evmWordIs_sp32_unfold (sp : Word) (v : EvmWord) :
    evmWordIs (sp + 32) v =
    (((sp + 32) ↦ₘ v.getLimbN 0) ** ((sp + 40) ↦ₘ v.getLimbN 1) **
     ((sp + 48) ↦ₘ v.getLimbN 2) ** ((sp + 56) ↦ₘ v.getLimbN 3)) := by
  unfold evmWordIs
  rw [show (sp + 32 : Word) + 8 = sp + 40 from by bv_addr,
      show (sp + 32 : Word) + 16 = sp + 48 from by bv_addr,
      show (sp + 32 : Word) + 24 = sp + 56 from by bv_addr]

/-- Unfold `evmWordIs sp v` into four limb-level memory atoms at
    `sp, sp+8, sp+16, sp+24`. Trivial rewrite of the definition; provided as a
    companion to `evmWordIs_sp32_unfold` for readability at call sites. -/
theorem evmWordIs_sp_unfold (sp : Word) (v : EvmWord) :
    evmWordIs sp v =
    ((sp ↦ₘ v.getLimbN 0) ** ((sp + 8) ↦ₘ v.getLimbN 1) **
     ((sp + 16) ↦ₘ v.getLimbN 2) ** ((sp + 24) ↦ₘ v.getLimbN 3)) := rfl

/-- Rewrite `evmWordIs (sp+32) v` to four limb atoms given explicit getLimbN
    equalities. Caller-friendly alternative to `evmWordIs_sp32_unfold` when the
    target limb values are already known concretely — avoids the
    match-expression unification issues that arise when `v = fromLimbs …`. -/
theorem evmWordIs_sp32_limbs_eq (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    evmWordIs (sp + 32) v =
    (((sp + 32) ↦ₘ w0) ** ((sp + 40) ↦ₘ w1) **
     ((sp + 48) ↦ₘ w2) ** ((sp + 56) ↦ₘ w3)) := by
  rw [evmWordIs_sp32_unfold, h0, h1, h2, h3]

/-- Same as `evmWordIs_sp32_limbs_eq` but for `evmWordIs sp v`. -/
theorem evmWordIs_sp_limbs_eq (sp : Word) (v : EvmWord) (w0 w1 w2 w3 : Word)
    (h0 : v.getLimbN 0 = w0) (h1 : v.getLimbN 1 = w1)
    (h2 : v.getLimbN 2 = w2) (h3 : v.getLimbN 3 = w3) :
    evmWordIs sp v =
    ((sp ↦ₘ w0) ** ((sp + 8) ↦ₘ w1) **
     ((sp + 16) ↦ₘ w2) ** ((sp + 24) ↦ₘ w3)) := by
  rw [evmWordIs_sp_unfold, h0, h1, h2, h3]

-- ============================================================================
-- DIV: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level DIV spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_div_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  -- Normalize (0 : EvmWord).getLimb k to (0 : Word)
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  -- Get the limb-level zero-path spec
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_div_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  -- Bridge: div a 0 = 0, getLimb (div a 0) k = 0
  have hr0 : (EvmWord.div a 0).getLimbN 0 = 0 := EvmWord.div_getLimb_zero_right a 0
  have hr1 : (EvmWord.div a 0).getLimbN 1 = 0 := EvmWord.div_getLimb_zero_right a 1
  have hr2 : (EvmWord.div a 0).getLimbN 2 = 0 := EvmWord.div_getLimb_zero_right a 2
  have hr3 : (EvmWord.div a 0).getLimbN 3 = 0 := EvmWord.div_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- ============================================================================
-- MOD: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level MOD spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_mod_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.mod a b)) := by
  subst hbz
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_mod_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 : (EvmWord.mod a 0).getLimbN 0 = 0 := EvmWord.mod_getLimb_zero_right a 0
  have hr1 : (EvmWord.mod a 0).getLimbN 1 = 0 := EvmWord.mod_getLimb_zero_right a 1
  have hr2 : (EvmWord.mod a 0).getLimbN 2 = 0 := EvmWord.mod_getLimb_zero_right a 2
  have hr3 : (EvmWord.mod a 0).getLimbN 3 = 0 := EvmWord.mod_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

end EvmAsm.Evm64
