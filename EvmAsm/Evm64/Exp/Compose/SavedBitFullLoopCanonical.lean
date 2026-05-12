/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopCanonical

  Canonical-code views of saved-bit EXP full-loop prefix blocks.  These
  wrappers pin the skip and loop-back branches to the canonical offsets used
  by `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Canonical-code view of the saved-bit MSB bit-test block. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) :=
  exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Canonical-code view of the saved-bit copy block. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (bit v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    bit v18 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Canonical-code view of the bit-test plus saved-bit prefix. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    let bit := e >>> (63 : BitVec 6).toNat
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 v18 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Canonical-code view of the saved-bit conditional-multiply BEQ gate. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (v18 : Word)
    (base mulTarget target : Word)
    (htarget :
      (base + 148 : Word) + signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff =
        target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    v18 base mulTarget target htarget

/-- Canonical-code view of the saved-bit conditional-multiply BEQ gate,
    specialized to the canonical skip target. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_target_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (v18 : Word)
    (base mulTarget : Word) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 256) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    squaringMulOff condMulOff v18 base mulTarget (base + 256)
    (EvmAsm.Evm64.canonicalExpCondMulSkip_target base)

/-- Canonical-code view of the prefix plus squaring-call side of one saved-bit
    iteration. -/
theorem exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (w * w).getLimbN 3) **
       evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) :=
  exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v7 v11 mulTarget squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base hbase hmt hd

/-- Appended-MUL canonical-code view of the saved-bit prefix plus squaring call. -/
theorem exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (w * w).getLimbN 3) **
       evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) :=
  exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v7 v11 (base + 304)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base hbase
    (EvmAsm.Evm64.canonicalExpSquaringMul_target base).symm
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

/-- Canonical-code view of the saved-bit prefix, squaring call, and BEQ
    handoff before the optional conditional multiply. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (base target : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget))
    (htarget :
      (base + 148 : Word) + signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff =
        target) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) :=
  exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v7 v11 mulTarget squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base target hbase hmt hd htarget

/-- Canonical-code view of the saved-bit prefix, squaring call, and BEQ
    handoff, specialized to the canonical skip target. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_canonical_target_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      (base + 256)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) :=
  exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v7 v11 mulTarget squaringMulOff condMulOff base (base + 256)
    hbase hmt hd (EvmAsm.Evm64.canonicalExpCondMulSkip_target base)

/-- Appended-MUL canonical-code view of the saved-bit prefix, squaring call,
    and BEQ handoff, specialized to the canonical skip target. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_target_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      (base + 256)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) :=
  exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_canonical_target_with_mul_spec_within
    e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v7 v11 (base + 304)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base hbase
    (EvmAsm.Evm64.canonicalExpSquaringMul_target base).symm
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

end EvmAsm.Evm64.Exp.Compose
