/-
  EvmAsm.Evm64.ShrSemantic

  256-bit shift semantics: connect the RISC-V SHR implementation to
  EvmWord-level shift operations.

  Provides stack-level SHR specs using evmWordIs for the shift ≥ 256 case.
  The body case (shift < 256) requires bitvector lemmas connecting
  per-limb shift-merge operations to extractLsb' of a 256-bit shift.
-/

import EvmAsm.Evm64.ShrCompose

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: Helpers
-- ============================================================================

private theorem regIs_to_regOwn' (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Weaken: zero-result + frame regs → evmWordIs 0 + regOwn. -/
private theorem shr_zero_evmWord_weaken (sp : Addr) (s0 s1 s2 s3 r6 r7 r11 : Word) :
    ∀ h,
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) h →
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) h := by
  intro h hp
  -- Permute to bring r6/r7/r11 next to regOwn positions, then weaken
  have hp' := (congrFun (show _ = ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) from by xperm) h).mp hp
  have w1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn' .x6 _))))) h hp'
  have w2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn' .x7 _)))))) h w1
  have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_to_regOwn' .x11 _))))))) h w2
  exact w3

-- ============================================================================
-- Section 2: Zero-path stack-level specs
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Stack-level SHR for shift ≥ 256 (high limbs nonzero case):
    The result is zero. Uses evmWordIs for both pre and post. -/
theorem evm_shr_stack_zero_high (sp base : Addr)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (hvalid : ValidMemRange sp 8)
    (hhigh : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 ≠ 0) :
    cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) 0) := by
  -- Instantiate zero_high with individual limbs
  have hzero := evm_shr_zero_high_spec sp base
    (shift.getLimb 0) (shift.getLimb 1) (shift.getLimb 2) (shift.getLimb 3)
    (value.getLimb 0) (value.getLimb 1) (value.getLimb 2) (value.getLimb 3)
    r5 r10 hhigh hvalid
  -- Frame with r6/r7/r11
  have hframed := cpsTriple_frame_left base (base + 360) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
    (by pcFree) hzero
  -- Flatten the framed postcondition via explicit type annotation
  have hflat : cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ value.getLimb 0) ** ((sp + 40) ↦ₘ value.getLimb 1) **
       ((sp + 48) ↦ₘ value.getLimb 2) ** ((sp + 56) ↦ₘ value.getLimb 3) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hframed
  -- Fold evmWordIs and weaken regs
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_zero]
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56]
      have hq' : ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
         ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
         (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) h := by xperm_hyp hq
      have hw := shr_zero_evmWord_weaken sp _ _ _ _ r6 r7 r11 h hq'
      xperm_hyp hw)
    hflat

set_option maxHeartbeats 1600000 in
/-- Stack-level SHR for shift ≥ 256 (s0 ≥ 256 case):
    The result is zero. Uses evmWordIs for both pre and post. -/
theorem evm_shr_stack_zero_large (sp base : Addr)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (hvalid : ValidMemRange sp 8)
    (hlow : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 = 0)
    (hlarge : BitVec.ult (shift.getLimb 0) (signExtend12 (256 : BitVec 12)) = false) :
    cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) 0) := by
  have hzero := evm_shr_zero_large_spec sp base
    (shift.getLimb 0) (shift.getLimb 1) (shift.getLimb 2) (shift.getLimb 3)
    (value.getLimb 0) (value.getLimb 1) (value.getLimb 2) (value.getLimb 3)
    r5 r10 hlow hlarge hvalid
  have hframed := cpsTriple_frame_left base (base + 360) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
    (by pcFree) hzero
  have hflat : cpsTriple base (base + 360) (shrCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ value.getLimb 0) ** ((sp + 40) ↦ₘ value.getLimb 1) **
       ((sp + 48) ↦ₘ value.getLimb 2) ** ((sp + 56) ↦ₘ value.getLimb 3) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hframed
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_zero]
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56]
      have hq' : ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
         ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
         (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) h := by xperm_hyp hq
      have hw := shr_zero_evmWord_weaken sp _ _ _ _ r6 r7 r11 h hq'
      xperm_hyp hw)
    hflat

end EvmAsm.Rv64
