/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddback

  Named-postcondition wrappers for `divK_correction_addback_spec_within` and
  `divK_correction_addback_spec_within_noNop`. These expose the correction
  addback spec with 0 statement lets via `addbackFullPost`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeq

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Named-postcondition wrapper for `divK_correction_addback_spec_within`.
    0 statement-level lets; all addback intermediates are in `addbackFullPost`. -/
theorem divK_correction_addback_named_spec_within
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [addbackFullPost_unfold]; exact hp)
    (divK_correction_addback_spec_within sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
       v5Old v2Old base hb)

/-- Named-postcondition no-NOP wrapper for `divK_correction_addback_spec_within_noNop`.
    0 statement-level lets; all addback intermediates are in `addbackFullPost`. -/
theorem divK_correction_addback_named_spec_within_noNop
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [addbackFullPost_unfold]; exact hp)
    (divK_correction_addback_spec_within_noNop sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
       v5Old v2Old base hb)

end EvmAsm.Evm64
