/-
  EvmAsm.Evm64.Exp.CondMulPairThenMulCall

  Cond-mul sibling of `Exp/SquaringPairThenMulCall.lean`. Composes the
  17-instruction `exp_loop_cond_mul_marshal_pair_then_call_spec_within`
  (marshal pair + JAL into `mul_callable`) with `mul_callable_spec_within`
  at the JAL target, framing the local scratch slots and the EVM-stack
  base operand through the call, and shrinking the pair-post's 8-limb
  sub-tree at `evmSp[0..56]` to the two `evmWordIs` predicates expected
  by `mul_callable_spec_within`.

  After this composition: a single `cpsTripleWithin (17 + 64) base
  ((base + 68) &&& ~~~1)` over the disjoint `CodeReq.union` of
  `exp_cond_mul_call_block_code base mulOff` and `mul_callable_code mul_target`.
  Unlike the squaring case the two factors differ: factor1 is the running
  result `r := expResultWord r0..r3`, factor2 is the base operand
  `aw := expResultWord a0..a3`, so the post is `evmMulStackPost evmSp r aw`
  (`r * aw`, not a square).

  Refs: GH #92 (parent evm-asm-20z6), bead evm-asm-sgzf0.
  Authored by @pirapira; implemented by Hermes-bot (claude-c1).
-/

import EvmAsm.Evm64.Exp.CondMulCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Multiply.Callable

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compose the cond-mul marshal pair plus its trailing JAL (17 instr) with
    `mul_callable_spec_within` (64 instr) at the JAL target.

    Pre-state (entry, at `base`):
    * Local scratch frame: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3` (running
      result).
    * LP64 frame for `mul_callable`: `(.x12 ↦ᵣ evmSp)`, with
      `evmSp[0..56]` holding any prior values `d_i / e_i` (overwritten
      by the marshal pair).
    * EVM-stack-resident base operand `a` at `evmSp[-64..-40] = a0..a3`
      (read by `a_to_factor2`, preserved across the call).
    * Caller-saved registers consumed by `mul_callable`:
      `(.x5 ↦ᵣ tOld)`, `(.x6 ↦ᵣ v6)`, `(.x7 ↦ᵣ v7)`,
      `(.x10 ↦ᵣ v10)`, `(.x11 ↦ᵣ v11)`.
    * Return-address slot: `(.x1 ↦ᵣ vOld)` — JAL overwrites with
      `base + 68`.

    Post-state (exit, at `(base + 68) &&& ~~~1`):
    * Local scratch unchanged: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * Base operand preserved at `evmSp[-64..-40] = a0..a3`.
    * `mul_callable`'s `evmMulStackPost evmSp r aw` over
      `r := expResultWord r0..r3`, `aw := expResultWord a0..a3`:
      `(.x12 ↦ᵣ evmSp + 32)`, `regOwn` on caller-saved scratch,
      `memOwn` on the four below-sp bytes, and
      `evmWordIs (evmSp + 32) (r * aw)`.
    * `(.x1 ↦ᵣ (base + 68))` — `mul_callable` preserves `.x1`. -/
theorem exp_cond_mul_marshal_pair_then_mul_call_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_cond_mul_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
      ((exp_cond_mul_call_block_code base mulOff).union
        (mul_callable_code mul_target))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord a0 a1 a2 a3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Marshal pair + JAL: 17 instr, exit (base+64) + signExtend21 mulOff.
  have hpair := exp_loop_cond_mul_marshal_pair_then_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff base
  -- Frame the four extra registers `.x6/.x7/.x10/.x11` consumed by
  -- `mul_callable_spec_within`; the marshal pair never touches them and the
  -- JAL only touches `.x1`.
  have hpairFramed :=
    cpsTripleWithin_frameR
      ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      (by pcFree) hpair
  -- (2) `mul_callable_spec_within` at `mul_target` with factor1 = `r`,
  --     factor2 = `aw` (the EVM-stack base operand), and `ra_val = base+68`.
  have hmul := mul_callable_spec_within
    evmSp mul_target (base + 68)
    (expResultWord r0 r1 r2 r3) (expResultWord a0 a1 a2 a3)
    a3 v6 v7 v10 v11
  -- Frame the local scratch frame `(.x2 ↦ᵣ sp) ** sp[0..24]` AND the
  -- preserved EVM-stack base operand at `evmSp[-64..-40]` on the left;
  -- `mul_callable` does not touch any of those.
  have hmulFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      (by pcFree) hmul
  -- (3) Compose. The pair-then-JAL exits at `mul_target = (base+64) +
  --     signExtend21 mulOff` (rewrite via hmt to match the mul_callable
  --     entry). Midpoint permutation folds the 8-limb sub-tree at
  --     `evmSp[0..56]` into the two `evmWordIs` predicates.
  rw [← hmt] at hpairFramed
  have hseq :
      cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
        ((exp_cond_mul_call_block_code base mulOff).union
          (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hp => by
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
          rw [h0, h8, h16, h24, h32, h40, h48, h56] at hp
          have hL : evmWordIs evmSp (expResultWord r0 r1 r2 r3) = _ :=
            evmWordIs_sp_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
              (expResultWord_getLimbN_0 r0 r1 r2 r3)
              (expResultWord_getLimbN_1 r0 r1 r2 r3)
              (expResultWord_getLimbN_2 r0 r1 r2 r3)
              (expResultWord_getLimbN_3 r0 r1 r2 r3)
          have hR : evmWordIs (evmSp + 32) (expResultWord a0 a1 a2 a3) = _ :=
            evmWordIs_sp32_limbs_eq evmSp (expResultWord a0 a1 a2 a3) a0 a1 a2 a3
              (expResultWord_getLimbN_0 a0 a1 a2 a3)
              (expResultWord_getLimbN_1 a0 a1 a2 a3)
              (expResultWord_getLimbN_2 a0 a1 a2 a3)
              (expResultWord_getLimbN_3 a0 a1 a2 a3)
          rw [hL, hR]
          xperm_hyp hp)
        hpairFramed)
      hmulFramed
  -- Re-associate entry pre and exit post into the natural shapes declared.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
