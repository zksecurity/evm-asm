/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry

  Named loop-entry postcondition for the two-MUL saved-bit EXP prologue
  and pointer-advance boundary.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulBoundaryPre
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
      (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
     (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
   expTwoMulScratchFrame vOld v18)

theorem expTwoMulBoundaryPre_unfold
    {sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  delta expTwoMulBoundaryPre
  rw [expTwoMulScratchFrame_unfold]

theorem expTwoMulBoundaryPre_pcFree
    {sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest).pcFree := by
  rw [expTwoMulBoundaryPre_unfold]
  pcFree

instance pcFreeInst_expTwoMulBoundaryPre
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest) :=
  ⟨expTwoMulBoundaryPre_pcFree⟩

@[irreducible]
def expTwoMulLoopEntryPost
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) : Assertion :=
  (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
      evmWordIs sp (1 : EvmWord)) **
     (.x12 ↦ᵣ (evmSp + 64))) **
   evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
   expTwoMulScratchFrame vOld v18)

theorem expTwoMulLoopEntryPost_unfold
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  delta expTwoMulLoopEntryPost
  rw [expTwoMulScratchFrame_unfold]

theorem expTwoMulLoopEntryPost_pcFree
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest).pcFree := by
  rw [expTwoMulLoopEntryPost_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopEntryPost
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) :=
  ⟨expTwoMulLoopEntryPost_pcFree⟩

/-- Appended-MUL canonical-code prologue/pointer boundary with a named
    loop-entry postcondition. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_entry_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       expTwoMulScratchFrame vOld v18)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) := by
  unfold expTwoMulLoopEntryPost
  exact
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_full_stack_clean_regs_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

/-- Appended-MUL canonical-code prologue/pointer boundary with named pre and
    post assertions. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) := by
  rw [expTwoMulBoundaryPre_unfold]
  simpa [expTwoMulScratchFrame_unfold] using
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_entry_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

/-- Closed-form bound variant of
    `exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within`. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_closed_bound_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin 7 base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) :=
  exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

end EvmAsm.Evm64.Exp.Compose
