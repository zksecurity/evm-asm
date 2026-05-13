/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

  Consumer-facing pointer-restore and epilogue helpers for the corrected
  two-MUL saved-bit EXP code bundle. Base epilogue adapters live in
  SavedBitBoundaryEpilogueBase.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEpilogueBase
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

def expBoundaryExitControl (iterCountNew : Word) (exitCond : Prop) : Assertion :=
  (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝

def expBoundaryStackTail (evmSp : Word) (baseWord : EvmWord)
    (rest : List EvmWord) : Assertion :=
  evmWordIs evmSp baseWord ** evmStackIs (evmSp + 64) rest

/-- Full visible-post-stack view of pointer-restore followed by the EXP
    epilogue. This folds the preserved base operand and produced result word
    into the ordinary stack prefix at `evmSp`. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      expBoundaryExitControl iterCountNew exitCond
    let stackTail : Assertion :=
      expBoundaryStackTail evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail, expBoundaryExitControl,
        expBoundaryStackTail] at hp ⊢
      rw [evmStackIs_cons]
      xperm_hyp hp)
    (exp_pointer_restore_then_epilogue_stack_tail_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Full visible-post-stack view with the final EVM stack pointer exposed in
    plain consumer-facing form. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      expBoundaryExitControl iterCountNew exitCond
    let stackTail : Assertion :=
      expBoundaryStackTail evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  rw [← show evmSp + signExtend12 (32 : BitVec 12) = evmSp + 32 from by
    rw [signExtend12_32]]
  exact exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    squaringMulOff condMulOff skipOff backOff base mulTarget

/-- Full visible-stack view of pointer-restore followed by the EXP epilogue.
    The precondition exposes the preserved base operand, the old destination
    stack word, and the caller tail as one `evmStackIs` prefix; the
    postcondition replaces the destination word with the assembled result. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      expBoundaryExitControl iterCountNew exitCond
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (exitControl **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest))
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, expBoundaryExitControl,
        expBoundaryStackTail] at hp ⊢
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [← exp_epilogue_result_word_right evmSp d0 d1 d2 d3
        (evmStackIs (evmSp + 32 + 32) rest)] at hp
      rw [show evmSp + 32 + 32 = evmSp + 64#64 from by bv_addr] at hp
      xcancel_struct hp)
    (fun _ hp => hp)
    (exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Canonical-code view of the loop-exit boundary: pointer restore followed by
    EXP epilogue over `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      expBoundaryExitControl iterCountNew exitCond
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (exitControl **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest))
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  exact
    exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base mulTarget

/-- Appended-MUL canonical-code view of the loop-exit boundary: pointer restore
    followed by EXP epilogue over the canonical combined code shape. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (base : Word) :
    let exitControl : Assertion :=
      expBoundaryExitControl iterCountNew exitCond
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (exitControl **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest))
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) :=
  exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base (base + 304)

end EvmAsm.Evm64.Exp.Compose
