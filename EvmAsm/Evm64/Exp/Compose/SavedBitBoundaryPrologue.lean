/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue

  Boundary-block prologue and pointer-advance helpers for the corrected
  two-MUL saved-bit EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitWithMul
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- EXP prologue followed by the pointer-advance block, lifted to the
    two-MUL saved-bit EXP+MUL code bundle. This lands at the iteration-body
    entry with the EVM stack pointer advanced by one operand window. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
        (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
       (.x12 ↦ᵣ evmSp))
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
        (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        evmWordIs sp (1 : EvmWord)) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) := by
  have hPrologue :=
    exp_prologue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPrologueFramed :=
    cpsTripleWithin_frameR (.x12 ↦ᵣ evmSp) (by pcFree) hPrologue
  have hPointer :=
    exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      evmSp squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPointerFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord))
      (by pcFree)
      hPointer
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp)
      hPrologueFramed hPointerFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Stack-operand framed view of the two-MUL saved-bit EXP prologue followed
    by pointer advance. This preserves the visible EVM operand windows and
    caller-saved scratch ownership while the accumulator is initialized to one
    and `x12` advances to the loop-facing pointer. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_operand_frame_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let operandFrame : Assertion :=
      evmWordIs evmSp baseWord ** evmWordIs (evmSp + 32) exponentWord **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
         (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
        (.x12 ↦ᵣ evmSp)) ** operandFrame)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
         (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
         evmWordIs sp (1 : EvmWord)) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) ** operandFrame) := by
  intro operandFrame
  have hBase :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR operandFrame (by
    dsimp [operandFrame]
    pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Full visible-stack framed view of the two-MUL saved-bit EXP prologue
    followed by pointer advance. This folds the preserved base/exponent
    operands together with the untouched caller tail, while the accumulator is
    initialized to one and `x12` advances to the loop-facing pointer. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_frame_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
          (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  intro scratchFrame
  let operandFrame : Assertion :=
    evmWordIs evmSp baseWord ** evmWordIs (evmSp + 32) exponentWord **
    scratchFrame
  have hBase :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_operand_frame_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR (evmStackIs (evmSp + 64) rest)
    pcFree_evmStackIs hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [scratchFrame, operandFrame] at hp ⊢
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [show evmSp + 32 + 32 = evmSp + 64#64 from by bv_addr] at hp
      rw [show evmSp + 32#64 = evmSp + (32 : Word) from rfl]
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [scratchFrame, operandFrame] at hp ⊢
      rw [evmStackIs_cons, evmStackIs_cons]
      rw [show evmSp + 32#64 = evmSp + (32 : Word) from rfl] at hp
      rw [show evmSp + 64#64 = evmSp + 32 + 32 from by bv_addr] at hp
      xperm_hyp hp)
    hFramed

/-- Consumer-facing version of the full-stack prologue/pointer-advance view:
    expose the initialized loop counter, accumulator temp, and advanced EVM
    stack pointer as plain word constants. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  intro scratchFrame
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [show ((0 : Word) + signExtend12 (256 : BitVec 12)) = (256 : Word) from by
        unfold signExtend12
        bv_decide] at hp
      rw [show ((0 : Word) + signExtend12 (1 : BitVec 12)) = (1 : Word) from by
        rw [signExtend12_1]
        bv_decide] at hp
      rw [show evmSp + signExtend12 (64 : BitVec 12) = evmSp + 64 from by
        rw [signExtend12_64]] at hp
      exact hp)
    (exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_frame_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Canonical-code view of the full-stack prologue/pointer-advance boundary:
    the branch offsets are fixed by `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`,
    while the two external MUL-call offsets remain caller supplied. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  exact
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_clean_regs_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base mulTarget

/-- Appended-MUL canonical-code view of the full-stack
    prologue/pointer-advance boundary. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    let scratchFrame : Assertion :=
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) :=
  exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_full_stack_clean_regs_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base (base + 304)

end EvmAsm.Evm64.Exp.Compose
