/-
  EvmAsm.Evm64.Exp.CondMulMarshalPairPost

  Bridge: fold the 8 limb-level memIs atoms produced by the post-state of
  `exp_loop_cond_mul_marshal_pair_spec_within` into the two `evmWordIs`
  predicates expected by `mul_callable_spec_within`.
-/

import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Fold the 8-atom post-state of `exp_loop_cond_mul_marshal_pair_spec_within`
    into two `evmWordIs` atoms: factor 1 is the running result `r0..r3`, and
    factor 2 is the fixed EXP base `a0..a3`. -/
theorem exp_cond_mul_marshal_pair_post_evmWordIs
    (evmSp r0 r1 r2 r3 a0 a1 a2 a3 : Word) :
    (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord a0 a1 a2 a3)) := by
  have h0  : (evmSp + signExtend12 (0  : BitVec 12) : Word) = evmSp       := by
    unfold signExtend12; bv_decide
  have h8  : (evmSp + signExtend12 (8  : BitVec 12) : Word) = evmSp + 8   := by
    unfold signExtend12; bv_decide
  have h16 : (evmSp + signExtend12 (16 : BitVec 12) : Word) = evmSp + 16  := by
    unfold signExtend12; bv_decide
  have h24 : (evmSp + signExtend12 (24 : BitVec 12) : Word) = evmSp + 24  := by
    unfold signExtend12; bv_decide
  have h32 : (evmSp + signExtend12 (32 : BitVec 12) : Word) = evmSp + 32  := by
    unfold signExtend12; bv_decide
  have h40 : (evmSp + signExtend12 (40 : BitVec 12) : Word) = evmSp + 40  := by
    unfold signExtend12; bv_decide
  have h48 : (evmSp + signExtend12 (48 : BitVec 12) : Word) = evmSp + 48  := by
    unfold signExtend12; bv_decide
  have h56 : (evmSp + signExtend12 (56 : BitVec 12) : Word) = evmSp + 56  := by
    unfold signExtend12; bv_decide
  rw [h0, h8, h16, h24, h32, h40, h48, h56]
  rw [evmWordIs_sp_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
        (expResultWord_getLimbN_0 r0 r1 r2 r3)
        (expResultWord_getLimbN_1 r0 r1 r2 r3)
        (expResultWord_getLimbN_2 r0 r1 r2 r3)
        (expResultWord_getLimbN_3 r0 r1 r2 r3)]
  rw [evmWordIs_sp32_limbs_eq evmSp (expResultWord a0 a1 a2 a3) a0 a1 a2 a3
        (expResultWord_getLimbN_0 a0 a1 a2 a3)
        (expResultWord_getLimbN_1 a0 a1 a2 a3)
        (expResultWord_getLimbN_2 a0 a1 a2 a3)
        (expResultWord_getLimbN_3 a0 a1 a2 a3)]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `exp_cond_mul_marshal_pair_post_evmWordIs`, for
    folding the cond-mul post bridge inside a longer sep-conjunction chain. -/
theorem exp_cond_mul_marshal_pair_post_evmWordIs_right
    (evmSp r0 r1 r2 r3 a0 a1 a2 a3 : Word) (Q : Assertion) :
    (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) ** Q) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord a0 a1 a2 a3) ** Q) := by
  rw [show
      (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) ** Q) =
      ((((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
        ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) ** Q) from by
      rw [sepConj_assoc', sepConj_assoc', sepConj_assoc', sepConj_assoc',
          sepConj_assoc', sepConj_assoc', sepConj_assoc']]
  rw [exp_cond_mul_marshal_pair_post_evmWordIs]
  rw [sepConj_assoc']

end EvmAsm.Evm64
