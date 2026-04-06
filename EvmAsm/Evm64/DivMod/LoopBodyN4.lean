/-
  EvmAsm.Evm64.DivMod.LoopBodyN4

  Fixed loop body compositions for n=4 (4-limb divisor, m=0, single iteration).
  Eliminates the u_addr/window-cell and vtop/v3 overlaps in the original combined spec.

  For n=4, three overlaps exist in the original spec:
  1. u_addr = u_base + signExtend12 4064 → u_hi = u_top (u[j+4] = u[j+4])
  2. u_addr + 8 = u_base + signExtend12 4072 → u_lo = u3 (u[j+3] = u[j+3])
  3. vtop_base + signExtend12 32 = sp + signExtend12 56 → v_top = v3

  This file eliminates these overlaps by using only the 5 window cells and 4 v cells.
  Parameters u_hi, u_lo, v_top are removed — they are u_top, u3, v3 respectively.
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=4
-- ============================================================================

/-- For n=4: u_addr = u_base + signExtend12 4064 -/
private theorem u_addr_eq_utop_n4 (sp j : Word) :
    sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by native_decide]
  bv_omega

/-- For n=4: u_addr + 8 = u_base + signExtend12 4072 -/
private theorem u_addr8_eq_u3_n4 (sp j : Word) :
    (sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by native_decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by native_decide]
  bv_omega

/-- For n=4: vtop_base + signExtend12 32 = sp + signExtend12 56 -/
private theorem vtop_eq_v3_n4 (sp : Word) :
    sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 =
    sp + signExtend12 56 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by native_decide,
    show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide,
    show signExtend12 (56 : BitVec 12) = (56 : Word) from by native_decide]
  bv_omega

-- ============================================================================
-- loopBodyPost for n=4 (no u_addr/vtop overlap)
-- ============================================================================

/-- Postcondition for one loop iteration at n=4.
    Uses only window cells (u_base offsets) and v cells (sp offsets).
    No u_addr or vtop_base cells. -/
private def loopBodyPostN4
    (sp j v0 v1 v2 v3 : Word) : Assertion :=
  fun h =>
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    ∃ (x2v x10v x11v : Word)
      (un0v un1v un2v un3v u4v qv : Word)
      (retv dv dlov sunv : Word),
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
     (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
     (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
     (.x2 ↦ᵣ x2v) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0v) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1v) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2v) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3v) **
     ((u_base + signExtend12 4064) ↦ₘ u4v) **
     (q_addr ↦ₘ qv) **
     (sp + signExtend12 3968 ↦ₘ retv) **
     (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) **
     (sp + signExtend12 3944 ↦ₘ sunv)) h

-- ============================================================================
-- Combined loop body spec for n=4 (no overlapping cells)
-- ============================================================================

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12800000 in
/-- Combined loop body for n=4: one iteration at base+448.
    cpsBranch to base+448 (loop back) or base+904 (exit).
    No u_addr/vtop overlap — precondition uses only window cells.
    For n=4: u_hi = u_top, u_lo = u3, v_top = v3. -/
theorem divK_loop_body_n4_combined_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_vtop : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + 448)
      (loopBodyPostN4 sp j v0 v1 v2 v3)
      (base + 904)
      (loopBodyPostN4 sp j v0 v1 v2 v3) := by
  intro u_base
  -- Case split on BLTU (u_top < v3?)
  by_cases hbltu : BitVec.ult u_top v3
  · -- BLTU taken: div128 call path
    sorry
  · -- BLTU not taken: max path
    -- Proof approach: instantiate trial_max_full with u_hi := u_top, u_lo := u3,
    -- rewrite u_addr addresses to u_base + offsets, frame with non-overlapping
    -- window cells (u0, u1, u2), compose with mulsub + store_loop.
    -- The key challenge is rewriting let-bound u_addr in TF's type to u_base offsets.
    -- Requires a tactic that can see through let-bindings for address rewriting.
    sorry

end EvmAsm.Rv64
