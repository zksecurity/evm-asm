/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedEntryExists

  Boundary wrappers that use the existential fixed first-iteration precondition
  produced by the fixed loop entry bridge.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryFixedIterPre
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedFirstIterCaseLoopPostWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) : Assertion :=
  expTwoMulFixedIterCaseLoopPost
    (256 : Word)
    (exponentWord.getLimbN 3)
    ((0 : Word) + signExtend12 (64 : BitVec 12))
    (evmSp + signExtend12 (56 : BitVec 12) +
      signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN 2)
    sp (evmSp + signExtend12 (64 : BitVec 12))
    ((1 : EvmWord).getLimbN 0)
    ((1 : EvmWord).getLimbN 1)
    ((1 : EvmWord).getLimbN 2)
    ((1 : EvmWord).getLimbN 3)
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    base **
  expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} :
    expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base =
      (expTwoMulFixedIterCaseLoopPost
        (256 : Word)
        (exponentWord.getLimbN 3)
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        base **
       expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) := by
  delta expTwoMulFixedFirstIterCaseLoopPostWithResidual
  rfl

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_pcFree
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} :
    (expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base).pcFree := by
  rw [expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedFirstIterCaseLoopPostWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    Assertion.PCFree
      (expTwoMulFixedFirstIterCaseLoopPostWithResidual
        sp evmSp baseWord exponentWord rest base) :=
  ⟨expTwoMulFixedFirstIterCaseLoopPostWithResidual_pcFree⟩

/-- Fixed full-loop boundary wrapper whose loop body starts from the named
    existential first-iteration precondition produced by the fixed loop entry
    post. This is the surface needed before destructing the chosen
    `x10`/`x7`/`x11` scratch values for concrete first-iteration body proofs. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord (dWord :: eWord :: rest) exitCond base
    (fun _ h =>
      expTwoMulLoopEntryPostFixed_to_firstIterPreWithResidual h)
    hBody

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond) := by
    rw [expTwoMulFixedFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3
      baseWord exponentWord dWord eWord rest exitCond base hBodyNamed

/-- Fixed full-loop boundary wrapper whose body proof is supplied for every
    concrete choice of the first-iteration scratch registers. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin expTwoMulFixedFullLoopBodyBound
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
            baseWord exponentWord dWord eWord **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual hBody)

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin 49408
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
            baseWord exponentWord dWord eWord **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual hBody)

/-- Fixed full-loop boundary wrapper whose body proof is phrased directly over
    the canonical `expTwoMulFixedIterPre` arguments for the first iteration. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin expTwoMulFixedFullLoopBodyBound
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3)
            ((0 : Word) + signExtend12 (64 : BitVec 12))
            (256 : Word)
            v10 v18
            (evmSp + signExtend12 (56 : BitVec 12) +
              signExtend12 (-8 : BitVec 12))
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (1 : Word) vOld
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
            (dWord.getLimbN 0) (dWord.getLimbN 1)
            (dWord.getLimbN 2) (dWord.getLimbN 3)
            (eWord.getLimbN 0) (eWord.getLimbN 1)
            (eWord.getLimbN 2) (eWord.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3)
            v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (fun v10 v7 v11 => by
      rw [expTwoMulFixedFirstIterPre_unfold]
      exact hBody v10 v7 v11)

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin 49408
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3)
            ((0 : Word) + signExtend12 (64 : BitVec 12))
            (256 : Word)
            v10 v18
            (evmSp + signExtend12 (56 : BitVec 12) +
              signExtend12 (-8 : BitVec 12))
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (1 : Word) vOld
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
            (dWord.getLimbN 0) (dWord.getLimbN 1)
            (dWord.getLimbN 2) (dWord.getLimbN 3)
            (eWord.getLimbN 0) (eWord.getLimbN 1)
            (eWord.getLimbN 2) (eWord.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3)
            v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (fun v10 v7 v11 => by
      rw [expTwoMulFixedFirstIterPre_unfold]
      exact hBody v10 v7 v11)

end EvmAsm.Evm64.Exp.Compose
