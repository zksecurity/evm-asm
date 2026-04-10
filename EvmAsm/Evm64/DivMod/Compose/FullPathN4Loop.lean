/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

  Full n=4 path: pre-loop + single loop iteration (j=0) + post-loop.
  Composes evm_div_n4_to_loopSetup_spec (base → base+448) with the j=0
  loop body cpsTriple (base+448 → base+904) and post-loop denorm chain
  (base+904 → base+1064).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.LoopIterN4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Loop body j=0 extended to divCode (from sharedDivModCode)
-- ============================================================================

/-- Extend max_skip j=0 loop body from sharedDivModCode to divCode. -/
theorem divK_loop_body_n4_max_skip_j0_divCode
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 904) (divCode base)
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
       (q_addr ↦ₘ q_old))
      (loopBodyN4SkipPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_body_n4_max_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2
      hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow)

end EvmAsm.Evm64
