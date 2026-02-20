/-
  EvmAsm.Evm.Not

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- pcFree proof for a 7-element memIs chain -/
local macro "pcFree7" : term =>
  `(pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_memIs _ _)))))))

/-- Full 256-bit EVM NOT: composes 8 per-limb NOT specs.
    24 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (code : CodeMem) (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (v7 : Word)
    -- Limb 0 code (base + 0/4/8)
    (hc0 : code base = some (.LW .x7 .x12 0))
    (hc1 : code (base + 4) = some (.XORI .x7 .x7 (-1)))
    (hc2 : code (base + 8) = some (.SW .x12 .x7 0))
    -- Limb 1 code (base + 12/16/20)
    (hc3 : code (base + 12) = some (.LW .x7 .x12 4))
    (hc4 : code (base + 16) = some (.XORI .x7 .x7 (-1)))
    (hc5 : code (base + 20) = some (.SW .x12 .x7 4))
    -- Limb 2 code (base + 24/28/32)
    (hc6 : code (base + 24) = some (.LW .x7 .x12 8))
    (hc7 : code (base + 28) = some (.XORI .x7 .x7 (-1)))
    (hc8 : code (base + 32) = some (.SW .x12 .x7 8))
    -- Limb 3 code (base + 36/40/44)
    (hc9 : code (base + 36) = some (.LW .x7 .x12 12))
    (hc10 : code (base + 40) = some (.XORI .x7 .x7 (-1)))
    (hc11 : code (base + 44) = some (.SW .x12 .x7 12))
    -- Limb 4 code (base + 48/52/56)
    (hc12 : code (base + 48) = some (.LW .x7 .x12 16))
    (hc13 : code (base + 52) = some (.XORI .x7 .x7 (-1)))
    (hc14 : code (base + 56) = some (.SW .x12 .x7 16))
    -- Limb 5 code (base + 60/64/68)
    (hc15 : code (base + 60) = some (.LW .x7 .x12 20))
    (hc16 : code (base + 64) = some (.XORI .x7 .x7 (-1)))
    (hc17 : code (base + 68) = some (.SW .x12 .x7 20))
    -- Limb 6 code (base + 72/76/80)
    (hc18 : code (base + 72) = some (.LW .x7 .x12 24))
    (hc19 : code (base + 76) = some (.XORI .x7 .x7 (-1)))
    (hc20 : code (base + 80) = some (.SW .x12 .x7 24))
    -- Limb 7 code (base + 84/88/92)
    (hc21 : code (base + 84) = some (.LW .x7 .x12 28))
    (hc22 : code (base + 88) = some (.XORI .x7 .x7 (-1)))
    (hc23 : code (base + 92) = some (.SW .x12 .x7 28))
    -- Memory validity
    (hv0 : isValidMemAccess sp = true)
    (hv4 : isValidMemAccess (sp + 4) = true)
    (hv8 : isValidMemAccess (sp + 8) = true)
    (hv12 : isValidMemAccess (sp + 12) = true)
    (hv16 : isValidMemAccess (sp + 16) = true)
    (hv20 : isValidMemAccess (sp + 20) = true)
    (hv24 : isValidMemAccess (sp + 24) = true)
    (hv28 : isValidMemAccess (sp + 28) = true) :
    let c := signExtend12 (-1 : BitVec 12)
    cpsTriple code base (base + 96)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 4) ↦ₘ (a1 ^^^ c)) ** ((sp + 8) ↦ₘ (a2 ^^^ c)) ** ((sp + 12) ↦ₘ (a3 ^^^ c)) **
       ((sp + 16) ↦ₘ (a4 ^^^ c)) ** ((sp + 20) ↦ₘ (a5 ^^^ c)) ** ((sp + 24) ↦ₘ (a6 ^^^ c)) ** ((sp + 28) ↦ₘ (a7 ^^^ c))) := by
  simp only
  have hse0 : sp + signExtend12 (0 : BitVec 12) = sp := by
    simp only [signExtend12_0]; apply BitVec.eq_of_toNat_eq; simp
  -- Limb 0
  have L0 := not_limb_spec code 0 sp a0 v7 base hc0 hc1 hc2 (by rw [hse0]; exact hv0)
  rw [hse0] at L0
  have L0f := cpsTriple_frame_left code base (base + 12) _ _
    (((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L0
  -- Limb 1
  have L1 := not_limb_spec code 4 sp a1 (a0 ^^^ signExtend12 (-1)) (base + 12) hc3
    (by rw [show (base + 12) + 4 = base + 16 from by bv_addr]; exact hc4)
    (by rw [show (base + 12) + 8 = base + 20 from by bv_addr]; exact hc5)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4] at L1
  rw [show (base + 12) + 12 = base + 24 from by bv_addr] at L1
  have L1f := cpsTriple_frame_left code (base + 12) (base + 24) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L1
  -- Limb 2
  have L2 := not_limb_spec code 8 sp a2 (a1 ^^^ signExtend12 (-1)) (base + 24) hc6
    (by rw [show (base + 24) + 4 = base + 28 from by bv_addr]; exact hc7)
    (by rw [show (base + 24) + 8 = base + 32 from by bv_addr]; exact hc8)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at L2
  rw [show (base + 24) + 12 = base + 36 from by bv_addr] at L2
  have L2f := cpsTriple_frame_left code (base + 24) (base + 36) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L2
  -- Limb 3
  have L3 := not_limb_spec code 12 sp a3 (a2 ^^^ signExtend12 (-1)) (base + 36) hc9
    (by rw [show (base + 36) + 4 = base + 40 from by bv_addr]; exact hc10)
    (by rw [show (base + 36) + 8 = base + 44 from by bv_addr]; exact hc11)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at L3
  rw [show (base + 36) + 12 = base + 48 from by bv_addr] at L3
  have L3f := cpsTriple_frame_left code (base + 36) (base + 48) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L3
  -- Limb 4
  have L4 := not_limb_spec code 16 sp a4 (a3 ^^^ signExtend12 (-1)) (base + 48) hc12
    (by rw [show (base + 48) + 4 = base + 52 from by bv_addr]; exact hc13)
    (by rw [show (base + 48) + 8 = base + 56 from by bv_addr]; exact hc14)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at L4
  rw [show (base + 48) + 12 = base + 60 from by bv_addr] at L4
  have L4f := cpsTriple_frame_left code (base + 48) (base + 60) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) **
     ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L4
  -- Limb 5
  have L5 := not_limb_spec code 20 sp a5 (a4 ^^^ signExtend12 (-1)) (base + 60) hc15
    (by rw [show (base + 60) + 4 = base + 64 from by bv_addr]; exact hc16)
    (by rw [show (base + 60) + 8 = base + 68 from by bv_addr]; exact hc17)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at L5
  rw [show (base + 60) + 12 = base + 72 from by bv_addr] at L5
  have L5f := cpsTriple_frame_left code (base + 60) (base + 72) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) **
     ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) ** ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L5
  -- Limb 6
  have L6 := not_limb_spec code 24 sp a6 (a5 ^^^ signExtend12 (-1)) (base + 72) hc18
    (by rw [show (base + 72) + 4 = base + 76 from by bv_addr]; exact hc19)
    (by rw [show (base + 72) + 8 = base + 80 from by bv_addr]; exact hc20)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at L6
  rw [show (base + 72) + 12 = base + 84 from by bv_addr] at L6
  have L6f := cpsTriple_frame_left code (base + 72) (base + 84) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) **
     ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) ** ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 28) ↦ₘ a7))
    pcFree7 L6
  -- Limb 7
  have L7 := not_limb_spec code 28 sp a7 (a6 ^^^ signExtend12 (-1)) (base + 84) hc21
    (by rw [show (base + 84) + 4 = base + 88 from by bv_addr]; exact hc22)
    (by rw [show (base + 84) + 8 = base + 92 from by bv_addr]; exact hc23)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at L7
  rw [show (base + 84) + 12 = base + 96 from by bv_addr] at L7
  have L7f := cpsTriple_frame_left code (base + 84) (base + 96) _ _
    ((sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) **
     ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) ** ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ (a6 ^^^ signExtend12 (-1))))
    pcFree7 L7
  -- Canonicalize each limb: use cpsTriple_consequence with simp AC to permute
  -- assertions from frame_left form to flat canonical form.
  -- (simp-based AC is confluent regardless of Expr structure, unlike ac_rfl/ac_nf
  --  which use Expr.lt and can produce inconsistent orderings for semantically-equal
  --  but structurally-different leaves. 10 conjuncts is well within heartbeat limits.)
  have C0 : cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a0 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code base (base + 12) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L0f
  have C1 : cpsTriple code (base + 12) (base + 24)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a0 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a1 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 12) (base + 24) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L1f
  have C2 : cpsTriple code (base + 24) (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a1 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a2 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 24) (base + 36) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L2f
  have C3 : cpsTriple code (base + 36) (base + 48)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a2 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 36) (base + 48) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L3f
  have C4 : cpsTriple code (base + 48) (base + 60)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a4 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 48) (base + 60) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L4f
  have C5 : cpsTriple code (base + 60) (base + 72)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a4 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a5 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 60) (base + 72) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L5f
  have C6 : cpsTriple code (base + 72) (base + 84)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a5 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a6 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ (a6 ^^^ signExtend12 (-1))) ** ((sp + 28) ↦ₘ a7)) :=
    cpsTriple_consequence code (base + 72) (base + 84) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L6f
  have C7 : cpsTriple code (base + 84) (base + 96)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a6 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ (a6 ^^^ signExtend12 (-1))) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 ^^^ signExtend12 (-1))) **
       (sp ↦ₘ (a0 ^^^ signExtend12 (-1))) ** ((sp + 4) ↦ₘ (a1 ^^^ signExtend12 (-1))) ** ((sp + 8) ↦ₘ (a2 ^^^ signExtend12 (-1))) ** ((sp + 12) ↦ₘ (a3 ^^^ signExtend12 (-1))) **
       ((sp + 16) ↦ₘ (a4 ^^^ signExtend12 (-1))) ** ((sp + 20) ↦ₘ (a5 ^^^ signExtend12 (-1))) ** ((sp + 24) ↦ₘ (a6 ^^^ signExtend12 (-1))) ** ((sp + 28) ↦ₘ (a7 ^^^ signExtend12 (-1)))) :=
    cpsTriple_consequence code (base + 84) (base + 96) _ _ _ _
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by sep_perm hp) L7f
  -- Sequential composition (canonical forms match, no sep_perm needed)
  have c01 := cpsTriple_seq code base (base + 12) (base + 24) _ _ _ C0 C1
  have c012 := cpsTriple_seq code base (base + 24) (base + 36) _ _ _ c01 C2
  have c0123 := cpsTriple_seq code base (base + 36) (base + 48) _ _ _ c012 C3
  have c01234 := cpsTriple_seq code base (base + 48) (base + 60) _ _ _ c0123 C4
  have c012345 := cpsTriple_seq code base (base + 60) (base + 72) _ _ _ c01234 C5
  have c0123456 := cpsTriple_seq code base (base + 72) (base + 84) _ _ _ c012345 C6
  exact cpsTriple_seq code base (base + 84) (base + 96) _ _ _ c0123456 C7

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 32 := by
  native_decide

/-- Stack-level 256-bit EVM NOT: complements an EvmWord in-place. -/
theorem evm_not_stack_spec (code : CodeMem) (sp base : Addr)
    (a : EvmWord) (v7 : Word)
    (hc0 : code base = some (.LW .x7 .x12 0))
    (hc1 : code (base + 4) = some (.XORI .x7 .x7 (-1)))
    (hc2 : code (base + 8) = some (.SW .x12 .x7 0))
    (hc3 : code (base + 12) = some (.LW .x7 .x12 4))
    (hc4 : code (base + 16) = some (.XORI .x7 .x7 (-1)))
    (hc5 : code (base + 20) = some (.SW .x12 .x7 4))
    (hc6 : code (base + 24) = some (.LW .x7 .x12 8))
    (hc7 : code (base + 28) = some (.XORI .x7 .x7 (-1)))
    (hc8 : code (base + 32) = some (.SW .x12 .x7 8))
    (hc9 : code (base + 36) = some (.LW .x7 .x12 12))
    (hc10 : code (base + 40) = some (.XORI .x7 .x7 (-1)))
    (hc11 : code (base + 44) = some (.SW .x12 .x7 12))
    (hc12 : code (base + 48) = some (.LW .x7 .x12 16))
    (hc13 : code (base + 52) = some (.XORI .x7 .x7 (-1)))
    (hc14 : code (base + 56) = some (.SW .x12 .x7 16))
    (hc15 : code (base + 60) = some (.LW .x7 .x12 20))
    (hc16 : code (base + 64) = some (.XORI .x7 .x7 (-1)))
    (hc17 : code (base + 68) = some (.SW .x12 .x7 20))
    (hc18 : code (base + 72) = some (.LW .x7 .x12 24))
    (hc19 : code (base + 76) = some (.XORI .x7 .x7 (-1)))
    (hc20 : code (base + 80) = some (.SW .x12 .x7 24))
    (hc21 : code (base + 84) = some (.LW .x7 .x12 28))
    (hc22 : code (base + 88) = some (.XORI .x7 .x7 (-1)))
    (hc23 : code (base + 92) = some (.SW .x12 .x7 28))
    (hv0 : isValidMemAccess sp = true)
    (hv4 : isValidMemAccess (sp + 4) = true)
    (hv8 : isValidMemAccess (sp + 8) = true)
    (hv12 : isValidMemAccess (sp + 12) = true)
    (hv16 : isValidMemAccess (sp + 16) = true)
    (hv20 : isValidMemAccess (sp + 20) = true)
    (hv24 : isValidMemAccess (sp + 24) = true)
    (hv28 : isValidMemAccess (sp + 28) = true) :
    cpsTriple code base (base + 96)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ ((~~~a).getLimb 7)) ** evmWordIs sp (~~~a)) := by
  simp only [evmWordIs]
  -- First decompose (~~~a).getLimb i into ~~~(a.getLimb i)
  simp only [EvmWord.getLimb_not]
  -- Then rewrite 32-bit ~~~x to x ^^^ signExtend12 (-1)
  simp only [← BitVec.xor_allOnes, ← signExtend12_neg1_eq_allOnes]
  exact evm_not_spec code sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    v7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11
    hc12 hc13 hc14 hc15 hc16 hc17 hc18 hc19 hc20 hc21 hc22 hc23
    hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28

end EvmAsm
