/-
  EvmAsm.Evm64.DivMod.LoopBodyN4Unified

  Unified loop body spec for n=4, j=0: combines the 4 per-case concrete specs
  (max_skip, max_addback, call_skip, call_addback) into a single cpsTriple
  with postcondition expressed via loopBodyN4_fullpost.

  The postcondition uses externally defined functions (loopIterN4,
  loopIterN4_c3, loopScratchN4) — no let-chains in the theorem type.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN4Concrete

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- trialQuotientN4 case lemmas
-- ============================================================================

private theorem trialQuotientN4_max (v3 u3 u_top : Word) (h : ¬BitVec.ult u_top v3) :
    trialQuotientN4 v3 u3 u_top = signExtend12 (4095 : BitVec 12) := by
  unfold trialQuotientN4; simp [Bool.eq_false_iff.mpr h]

-- ============================================================================
-- Postcondition matching lemmas: show loopBodyN4_fullpost agrees with each
-- concrete spec's postcondition in the corresponding case.
-- ============================================================================

/-- In the MAX+SKIP case (¬BLTU, ¬borrow), loopBodyN4_fullpost
    equals the max_skip concrete spec's postcondition. -/
private theorem fullpost_eq_max_skip
    (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top ret_mem d_mem dlo_mem scratch_un0 base : Word)
    (hbltu : ¬BitVec.ult u_top v3)
    (hborrow : ¬BitVec.ult u_top
      (mulsubN4 (signExtend12 (4095 : BitVec 12)) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let q_hat := signExtend12 (4095 : BitVec 12)
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    loopBodyN4_fullpost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
      ret_mem d_mem dlo_mem scratch_un0 base =
    loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
      ms.2.2.2.1 ms.2.2.2.2 q_hat
      ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) q_hat
      ret_mem d_mem dlo_mem scratch_un0 := by
  intro q_hat ms
  have hq := trialQuotientN4_max v3 u3 u_top hbltu
  have hb1 : BitVec.ult u_top v3 = false := Bool.eq_false_iff.mpr hbltu
  have hb2 : BitVec.ult u_top (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = false := Bool.eq_false_iff.mpr hborrow
  unfold loopBodyN4_fullpost loopIterN4 loopIterN4_c3 loopScratchN4
  simp only [hq, hb1, hb2, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]; rfl

/-- In the MAX+ADDBACK case (¬BLTU, borrow), loopBodyN4_fullpost
    equals the max_addback concrete spec's postcondition. -/
private theorem fullpost_eq_max_addback
    (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top ret_mem d_mem dlo_mem scratch_un0 base : Word)
    (hbltu : ¬BitVec.ult u_top v3)
    (hborrow : BitVec.ult u_top
      (mulsubN4 (signExtend12 (4095 : BitVec 12)) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let q_hat := signExtend12 (4095 : BitVec 12)
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3
    loopBodyN4_fullpost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
      ret_mem d_mem dlo_mem scratch_un0 base =
    loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
      ab.2.2.2.1 ms.2.2.2.2 (q_hat + signExtend12 4095)
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 (q_hat + signExtend12 4095)
      ret_mem d_mem dlo_mem scratch_un0 := by
  intro q_hat ms ab
  have hq := trialQuotientN4_max v3 u3 u_top hbltu
  have hb1 : BitVec.ult u_top v3 = false := Bool.eq_false_iff.mpr hbltu
  unfold loopBodyN4_fullpost loopIterN4 loopIterN4_c3 loopScratchN4
  simp only [hq, hb1, hborrow, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]; rfl

/-- In the CALL+SKIP case (BLTU, ¬borrow), loopBodyN4_fullpost
    equals the call_skip concrete spec's postcondition. -/
private theorem fullpost_eq_call_skip
    (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top ret_mem d_mem dlo_mem scratch_un0 base : Word)
    (hbltu : BitVec.ult u_top v3)
    (hborrow : ¬BitVec.ult u_top
      (mulsubN4 (trialQuotientN4 v3 u3 u_top) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let q_hat := trialQuotientN4 v3 u3 u_top
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    loopBodyN4_fullpost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
      ret_mem d_mem dlo_mem scratch_un0 base =
    loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
      ms.2.2.2.1 ms.2.2.2.2 q_hat
      ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) q_hat
      (base + 516) v3
      ((v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) := by
  intro q_hat ms
  have hb2 : BitVec.ult u_top (mulsubN4 (trialQuotientN4 v3 u3 u_top) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = false := Bool.eq_false_iff.mpr hborrow
  unfold loopBodyN4_fullpost loopIterN4 loopIterN4_c3 loopScratchN4
  simp only [hbltu, hb2, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]; rfl

/-- In the CALL+ADDBACK case (BLTU, borrow), loopBodyN4_fullpost
    equals the call_addback concrete spec's postcondition. -/
private theorem fullpost_eq_call_addback
    (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top ret_mem d_mem dlo_mem scratch_un0 base : Word)
    (hbltu : BitVec.ult u_top v3)
    (hborrow : BitVec.ult u_top
      (mulsubN4 (trialQuotientN4 v3 u3 u_top) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let q_hat := trialQuotientN4 v3 u3 u_top
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3
    loopBodyN4_fullpost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
      ret_mem d_mem dlo_mem scratch_un0 base =
    loopBodyPostN4 sp (0 : Word) v0 v1 v2 v3
      ab.2.2.2.1 ms.2.2.2.2 (q_hat + signExtend12 4095)
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 (q_hat + signExtend12 4095)
      (base + 516) v3
      ((v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) := by
  intro q_hat ms ab
  unfold loopBodyN4_fullpost loopIterN4 loopIterN4_c3 loopScratchN4
  simp only [hbltu, hborrow, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]; rfl

-- ============================================================================
-- Unified loop body theorem for n=4 at j=0
-- ============================================================================

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Unified loop body for n=4, j=0: entry at base+448, exit at base+904.
    Combines all 4 per-case concrete specs. Postcondition uses
    loopBodyN4_fullpost — no let-chains in the theorem type. -/
theorem divK_loop_body_n4_j0_unified
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - ((0 : Word) + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4_fullpost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
        ret_mem d_mem dlo_mem scratch_un0 base) := by
  intro u_base q_addr
  -- Case split: BLTU taken (u_top < v3) or not
  by_cases hbltu : BitVec.ult u_top v3
  · -- CALL path: trial quotient via div128
    -- Get the mulsub carry for the borrow case split
    let c3_val := (mulsubN4 (trialQuotientN4 v3 u3 u_top) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
    by_cases hborrow : BitVec.ult u_top c3_val
    · -- CALL + ADDBACK
      rw [fullpost_eq_call_addback sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
        ret_mem d_mem dlo_mem scratch_un0 base hbltu hborrow]
      have hspec := divK_loop_body_n4_j0_call_addback_concrete
        sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0
        halign hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      intro_lets at hspec
      have hbne : (if BitVec.ult u_top c3_val then (1 : Word) else 0) ≠ (0 : Word) := by
        simp [hborrow]
      exact hspec hbne
    · -- CALL + SKIP
      rw [fullpost_eq_call_skip sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
        ret_mem d_mem dlo_mem scratch_un0 base hbltu hborrow]
      have hspec := divK_loop_body_n4_j0_call_skip_concrete
        sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0
        halign hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      intro_lets at hspec
      have hbeq : (if BitVec.ult u_top c3_val then (1 : Word) else 0) = (0 : Word) := by
        simp [hborrow]
      exact hspec hbeq
  · -- MAX path: trial quotient = MAX64
    let c3_val := (mulsubN4 (signExtend12 (4095 : BitVec 12)) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
    by_cases hborrow : BitVec.ult u_top c3_val
    · -- MAX + ADDBACK
      rw [fullpost_eq_max_addback sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
        ret_mem d_mem dlo_mem scratch_un0 base hbltu hborrow]
      have hspec := divK_loop_body_n4_j0_max_addback_concrete
        sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2
        hv_v3 hv_u3 hv_u4 hv_q hbltu
      intro_lets at hspec
      have hbne : (if BitVec.ult u_top c3_val then (1 : Word) else 0) ≠ (0 : Word) := by
        simp [hborrow]
      exact hspec hbne
    · -- MAX + SKIP
      rw [fullpost_eq_max_skip sp v0 v1 v2 v3 u0 u1 u2 u3 u_top
        ret_mem d_mem dlo_mem scratch_un0 base hbltu hborrow]
      have hspec := divK_loop_body_n4_j0_max_skip_concrete
        sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2
        hv_v3 hv_u3 hv_u4 hv_q hbltu
      intro_lets at hspec
      have hbeq : (if BitVec.ult u_top c3_val then (1 : Word) else 0) = (0 : Word) := by
        simp [hborrow]
      exact hspec hbeq

end EvmAsm.Evm64
