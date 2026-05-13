/-
  EvmAsm.Evm64.Exp.Compose.SavedBitWithMul

  Code-bundle helpers and boundary block lifts for corrected saved-bit EXP
  programs combined with an external `mul_callable` body.
-/

import EvmAsm.Evm64.Exp.Compose.FullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Code required by the corrected saved-bit EXP program plus the external
    `mul_callable` body reached by the squaring and conditional-multiply JALs. -/
abbrev evmExpMsbSavedBitWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitCode base mulOff skipOff backOff).union
    (mul_callable_code mulTarget)

/-- Corrected saved-bit EXP program with independent JAL offsets for the
    squaring and conditional-multiply call sites, plus the external
    `mul_callable` body both sites target. -/
abbrev evmExpMsbSavedBitTwoMulWithMulCode (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitTwoMulCode
    base squaringMulOff condMulOff skipOff backOff).union
    (mul_callable_code mulTarget)

/-- Canonical-branch-offset two-MUL saved-bit EXP program plus the external
    `mul_callable` body targeted by both MUL call sites. -/
abbrev evmExpMsbSavedBitTwoMulCanonicalWithMulCode
    (base mulTarget : Word) (squaringMulOff condMulOff : BitVec 21) : CodeReq :=
  (evmExpMsbSavedBitTwoMulCanonicalCode
    base squaringMulOff condMulOff).union
    (mul_callable_code mulTarget)

theorem evmExpMsbSavedBitWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulWithMulCode_exp_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitWithMulCode_mul_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

theorem evmExpMsbSavedBitTwoMulWithMulCode_mul_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulCanonicalWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Lift a corrected saved-bit top-level EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a two-offset corrected saved-bit EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

/-- Lift a corrected saved-bit top-level EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a two-offset corrected saved-bit EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

/-- Lift a multiply-callable spec into the two-MUL saved-bit EXP+MUL code
    bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpMsbSavedBitTwoMulWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsTripleWithin nSteps entry exit_
      (mul_callable_code mulTarget) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_mul_sub
      (base := base) (mulTarget := mulTarget)
      (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
      (skipOff := skipOff) (backOff := backOff) hd)
    h

theorem evmExpMsbSavedBitTwoMulWithMulCode_block_subs {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i) := by
  rcases evmExpMsbSavedBitTwoMulCode_block_subs
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_prologue a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (h_pointer_advance a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_iter a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (h_pointer_restore a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i (h_epilogue a i h),
     evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd⟩

theorem evmExpMsbSavedBitTwoMulCanonicalWithMulCode_block_subs
    {base mulTarget : Word} {squaringMulOff condMulOff : BitVec 21}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCanonicalCode
        base squaringMulOff condMulOff)
      (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (expIterBodyFullMsbSavedBitTwoMulCode
      (base + 28) squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 268) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff) a = some i) := by
  rcases evmExpMsbSavedBitTwoMulCanonicalCode_block_subs
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_prologue a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_pointer_advance a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_iter a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_pointer_restore a i h),
     fun a i h =>
        evmExpMsbSavedBitTwoMulCanonicalWithMulCode_exp_sub a i
          (h_epilogue a i h),
     evmExpMsbSavedBitTwoMulCanonicalWithMulCode_mul_sub hd⟩

/-- Pointer advance lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_spec_within
      vOld squaringMulOff condMulOff skipOff backOff base)

/-- Pointer restore lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 264) (base + 268)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_spec_within
      vOld squaringMulOff condMulOff skipOff backOff base)

/-- EXP prologue lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_prologue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_prologue_evm_exp_msb_saved_bit_two_mul_spec_within
      sp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base)

/-- EXP epilogue lifted to the two-MUL saved-bit EXP+MUL code bundle. -/
theorem exp_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 268) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode
    (exp_epilogue_evm_exp_msb_saved_bit_two_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base)

end EvmAsm.Evm64.Exp.Compose
