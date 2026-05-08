/-
  EvmAsm.Evm64.Exp.SquaringMarshalPairPost

  Bridge: fold the 8 limb-level memIs atoms produced by the post-state of
  `exp_loop_squaring_marshal_pair_spec_within` (4 atoms in the LP64 factor-1
  slot at `evmSp[0..24]` plus 4 atoms in the factor-2 slot at `evmSp[32..56]`,
  all carrying the same scratch limbs `r0..r3`) into the two `evmWordIs`
  predicates expected by `mul_callable_spec_within` (a = b at `evmSp` and
  `evmSp + 32`).

  The packed EVM word is `expResultWord r0 r1 r2 r3` — i.e.
  `EvmWord.fromLimbs` over the four limbs in little-endian order.

  Sub-slice of evm-asm-nrfpf (#92 slice 4-squaring-call-spec): downstream
  `evm-asm-ct3ti` (the JAL-into-mul_callable round-trip composition) needs
  this bridge to shrink `mul_callable`'s `(evmWordIs sp a ** evmWordIs (sp+32) b)`
  pre into the marshal-pair post's flat 8-atom shape.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs: GH #92, parent evm-asm-mtj3, immediate parent evm-asm-nrfpf.
-/

import EvmAsm.Evm64.Exp.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Fold the 8-atom post-state of `exp_loop_squaring_marshal_pair_spec_within`
    (factor-1 slot at `evmSp[0..24]` and factor-2 slot at `evmSp[32..56]`,
    both holding limbs `r0..r3`) into two `evmWordIs` atoms over
    `expResultWord r0 r1 r2 r3`. -/
theorem exp_squaring_marshal_pair_post_evmWordIs
    (evmSp r0 r1 r2 r3 : Word) :
    (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  -- Canonicalize all signExtend12 offsets to their literal Word values.
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
  -- Now the LHS is the eight literal-offset atoms. Re-associate so that the
  -- first four atoms (factor-1 slot) and the last four (factor-2 slot) form
  -- distinct sub-trees, then fold each via `evmWordIs_sp_limbs_eq` and
  -- `evmWordIs_sp32_limbs_eq` instantiated with `expResultWord`.
  rw [evmWordIs_sp_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
        (expResultWord_getLimbN_0 r0 r1 r2 r3)
        (expResultWord_getLimbN_1 r0 r1 r2 r3)
        (expResultWord_getLimbN_2 r0 r1 r2 r3)
        (expResultWord_getLimbN_3 r0 r1 r2 r3)]
  rw [evmWordIs_sp32_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
        (expResultWord_getLimbN_0 r0 r1 r2 r3)
        (expResultWord_getLimbN_1 r0 r1 r2 r3)
        (expResultWord_getLimbN_2 r0 r1 r2 r3)
        (expResultWord_getLimbN_3 r0 r1 r2 r3)]
  -- Re-associate the right-leaning 8-atom chain into two right-leaning
  -- 4-atom chains separated at the factor-1/factor-2 boundary.
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `exp_squaring_marshal_pair_post_evmWordIs`: thread a
    remainder `Q` so callers (`evm-asm-ct3ti`, `evm-asm-nrfpf`) can fold the
    8-limb sub-tree even when it sits in the middle of a longer sepConj
    chain alongside frame slots like `(.x12 ↦ᵣ evmSp)`, `(.x1 ↦ᵣ ra_val)`,
    or the local-scratch `sp[0..24]` group. -/
theorem exp_squaring_marshal_pair_post_evmWordIs_right
    (evmSp r0 r1 r2 r3 : Word) (Q : Assertion) :
    (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
     ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
     ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) ** Q) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) ** Q) := by
  rw [show
      (((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) ** Q) =
      ((((evmSp + signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
        ((evmSp + signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) ** Q) from by
      rw [sepConj_assoc', sepConj_assoc', sepConj_assoc', sepConj_assoc',
          sepConj_assoc', sepConj_assoc', sepConj_assoc']]
  rw [exp_squaring_marshal_pair_post_evmWordIs]
  rw [sepConj_assoc']

end EvmAsm.Evm64
