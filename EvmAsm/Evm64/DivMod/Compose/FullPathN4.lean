/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4

  Full n=4 DIV path composition: pre-loop → loop body (j=0) → post-loop.
  Composes base → base+1064 for the b[3]≠0 case.

  For n=4, the loop runs exactly 1 iteration (j=0 only).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address form helpers: signExtend12 K = K for small offsets
-- ============================================================================

private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

-- ============================================================================
-- Loop body n=4, max+skip, j=0: normalized sp-relative precondition
-- ============================================================================

/-- Loop body n=4, max+skip, j=0 with sp-relative addresses in precondition.
    Uses (sp + K) for v[] cells and (sp + signExtend12 K) for u[]/q[] cells,
    matching the forms used in loopSetupPost. -/
theorem divK_loop_body_n4_max_skip_j0_norm (sp base : Word)
    (j_old v5_old v6_old v7_old v10_old v11_old v2_old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + 32) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_v1 : isValidDwordAccess (sp + 40) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_v2 : isValidDwordAccess (sp + 48) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_v3 : isValidDwordAccess (sp + 56) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let q_hat : Word := signExtend12 4095
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u_top) **
       ((sp + signExtend12 4088) ↦ₘ q_old))
      (loopBodyN4SkipPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro q_hat hborrow
  -- Convert validity hypotheses: sp-relative → raw form (small terms, no recursion issue)
  rw [← se12_32] at hv_v0; rw [← se12_40] at hv_v1
  rw [← se12_48] at hv_v2; rw [← se12_56] at hv_v3
  rw [← u_base_off0_j0] at hv_u0; rw [← u_base_off4088_j0] at hv_u1
  rw [← u_base_off4080_j0] at hv_u2; rw [← u_base_off4072_j0] at hv_u3
  rw [← u_base_off4064_j0] at hv_u4; rw [← q_addr_j0] at hv_q
  -- Get raw spec
  have raw := divK_loop_body_n4_max_skip_j0_divCode sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2
    hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
  -- Normalize raw addresses in the type of raw to sp-relative form
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

/-- Loop body n=4, max+addback, j=0 with sp-relative addresses in precondition. -/
theorem divK_loop_body_n4_max_addback_j0_norm (sp base : Word)
    (j_old v5_old v6_old v7_old v10_old v11_old v2_old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + 32) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_v1 : isValidDwordAccess (sp + 40) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_v2 : isValidDwordAccess (sp + 48) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_v3 : isValidDwordAccess (sp + 56) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let q_hat : Word := signExtend12 4095
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u_top) **
       ((sp + signExtend12 4088) ↦ₘ q_old))
      (loopBodyN4AddbackPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro q_hat hborrow
  rw [← se12_32] at hv_v0; rw [← se12_40] at hv_v1
  rw [← se12_48] at hv_v2; rw [← se12_56] at hv_v3
  rw [← u_base_off0_j0] at hv_u0; rw [← u_base_off4088_j0] at hv_u1
  rw [← u_base_off4080_j0] at hv_u2; rw [← u_base_off4072_j0] at hv_u3
  rw [← u_base_off4064_j0] at hv_u4; rw [← q_addr_j0] at hv_q
  have raw := divK_loop_body_n4_max_addback_j0_divCode sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2
    hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

end EvmAsm.Evm64
