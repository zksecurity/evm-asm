/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed

  Boundary composition for the fixed x19 two-MUL saved-bit EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Fixed-x19 boundary precondition for the EXP prologue, including ownership
    of the exponent-cursor registers that the fixed prologue initializes. -/
@[irreducible]
def expTwoMulBoundaryPreFixed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
   (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
   (.x6 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
   expTwoMulScratchFrame vOld v18 **
   evmStackIs evmSp (baseWord :: exponentWord :: rest))

theorem expTwoMulBoundaryPreFixed_unfold
    {sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 baseWord exponentWord rest =
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x6 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       expTwoMulScratchFrame vOld v18 **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)) := by
  delta expTwoMulBoundaryPreFixed
  rfl

theorem expTwoMulBoundaryPreFixed_pcFree
    {sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 baseWord exponentWord rest).pcFree := by
  rw [expTwoMulBoundaryPreFixed_unfold]
  pcFree

instance pcFreeInst_expTwoMulBoundaryPreFixed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest) :=
  ⟨expTwoMulBoundaryPreFixed_pcFree⟩

/-- Fixed-code analogue of the general boundary composition: fixed prologue,
    caller-supplied loop proof, and fixed pointer-restore/epilogue. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin ((10 + 1 + nSteps) + (1 + 9)) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundary :
      cpsTripleWithin (10 + 1) base (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
          m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest) := by
    rw [expTwoMulBoundaryPreFixed_unfold]
    exact
      exp_prologue_fixed_then_pointer_advance_full_stack_evmExpMsbSavedBitTwoMulFixedWithMulCode_spec_within
        sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
        base (base + 336)
  have hPrefix := cpsTripleWithin_seq_same_cr hBoundary hLoop
  have hEpilogue :
      cpsTripleWithin (1 + 9) (base + 296) (base + 336)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
        (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
          baseWord rest exitCond) := by
    unfold expTwoMulLoopExitPost
    exact
      exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_appended_mul_spec_within
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond base
  exact cpsTripleWithin_seq_same_cr hPrefix hEpilogue

end EvmAsm.Evm64.Exp.Compose
