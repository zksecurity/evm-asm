/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

  Code-bundle helpers for the fixed x19 two-MUL saved-bit EXP program plus
  the out-of-line `mul_callable` body.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologueFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Fixed saved-bit EXP code plus the external `mul_callable` body reached by
    both JALs in one loop iteration. -/
abbrev evmExpMsbSavedBitTwoMulFixedWithMulCode (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  (expMsbSavedBitTwoMulFixedCode
    base squaringMulOff condMulOff skipOff backOff).union
    (mul_callable_code mulTarget)

theorem expMsbSavedBitTwoMulFixedCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expIterBodyFullMsbSavedBitTwoMulFixedCode
      (base + 44) squaringMulOff condMulOff skipOff backOff) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  unfold expMsbSavedBitTwoMulFixedCode
  exact CodeReq.ofProg_mono_sub base (base + 44)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff) 11
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expMsbSavedBitTwoMulFixedCode
      base squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_mul_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Lift a whole fixed-EXP triple spec into the fixed EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

/-- Lift a whole fixed-EXP branch spec into the fixed EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_fixedCode_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_t exit_f base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q_t Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

/-- Lift a whole fixed-EXP N-branch spec into the fixed EXP+MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
    {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, ((expIterBodyFullMsbSavedBitTwoMulFixedCode
      (base + 44) squaringMulOff condMulOff skipOff backOff).union
      (mul_callable_code mulTarget)) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.union_sub
    (fun a i h =>
      evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub a i
        (expMsbSavedBitTwoMulFixedCode_iter_body_sub a i h))
    (evmExpMsbSavedBitTwoMulFixedWithMulCode_mul_sub hd)

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_disjoint_mul_of_fixed_disjoint
    {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    CodeReq.Disjoint
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget) := by
  intro a
  rcases hd a with h_fixed | h_mul
  · left
    cases h_body :
        (expIterBodyFullMsbSavedBitTwoMulFixedCode
          (base + 44) squaringMulOff condMulOff skipOff backOff) a with
    | none => rfl
    | some i =>
        have h_sub := expMsbSavedBitTwoMulFixedCode_iter_body_sub a i h_body
        rw [h_fixed] at h_sub
        contradiction
  · right
    exact h_mul

/-- Lift a fixed iteration-body branch spec into the whole fixed EXP+MUL code
    bundle. The fixed iteration body starts 44 bytes after the fixed EXP entry. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_t exit_f base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q_t Q_f : Assertion}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsBranchWithin nSteps entry
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (h := h)
    (hmono :=
      evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
        (base := base) (mulTarget := mulTarget)
        (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
        (skipOff := skipOff) (backOff := backOff) hd)

end EvmAsm.Evm64.Exp.Compose
