/-
  EvmAsm.Evm64.Exp.SquaringPairThenMulCall

  Second prep step for `exp_squaring_call_block_spec_within` (#92 slice
  4-squaring-call, parent `evm-asm-nrfpf`): compose the existing
  `exp_loop_squaring_marshal_pair_then_square_spec_within` (16 marshal-pair
  instructions plus the 1-instruction JAL into `mul_callable`) with
  `mul_callable_spec_within` at the JAL target, framing the local scratch
  slots `sp[0..24]` and `(.x2 ↦ᵣ sp)` through the call (mul_callable does
  not touch them, since its LP64 frame pointer is `evmSp` carried in
  `x12`), and shrinking the pair-post's 8-limb sub-tree at `evmSp[0..56]`
  to the two `evmWordIs` predicates expected by `mul_callable_spec_within`
  via `exp_squaring_marshal_pair_post_evmWordIs`.

  After this composition: a single `cpsTripleWithin (16 + 1 + 64) base
  ((base + 68) &&& ~~~1)` over the disjoint `CodeReq.union` of
  `exp_squaring_call_block_code base mulOff` and `mul_callable_code mul_target`.
  The downstream slice (`evm-asm-nrfpf`) then only has to seq this with
  `exp_loop_un_marshal_and_restore_spec_within` to obtain
  `exp_squaring_call_block_spec_within`.

  Refs: GH #92, beads `evm-asm-ct3ti` (sub-slice of `evm-asm-nrfpf`).
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Multiply.Callable

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compose the squaring marshal pair (16 instr) plus its trailing JAL
    (1 instr) with `mul_callable_spec_within` (64 instr) at the JAL target.

    Pre-state (entry, at `base`):
    * Local scratch frame: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * LP64 frame for `mul_callable`: `(.x12 ↦ᵣ evmSp)`, with
      `evmSp[0..24]` and `evmSp[32..56]` holding any prior values
      `d_i / e_i` (overwritten by the marshal pair).
    * Caller-saved registers consumed by `mul_callable`:
      `(.x5 ↦ᵣ tOld)`, `(.x6 ↦ᵣ v6)`, `(.x7 ↦ᵣ v7)`,
      `(.x10 ↦ᵣ v10)`, `(.x11 ↦ᵣ v11)`.
    * Return-address slot: `(.x1 ↦ᵣ vOld)` — the JAL overwrites this
      with `base + 68`, which `mul_callable`'s `cc_ret` reads back.

    Post-state (exit, at `(base + 68) &&& ~~~1`):
    * Local scratch unchanged: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * `mul_callable`'s `evmMulStackPost evmSp w w` over
      `w := expResultWord r0 r1 r2 r3` (squaring of the limb-packed
      result word): `(.x12 ↦ᵣ evmSp + 32)`, `regOwn` on the
      caller-saved scratch registers, `memOwn` on the four bytes
      below the new LP64 sp, and `evmWordIs (evmSp + 32) (w * w)`.
    * `(.x1 ↦ᵣ (base + 68))` — `mul_callable` preserves `.x1`. -/
theorem exp_squaring_marshal_pair_then_mul_call_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_squaring_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
      ((exp_squaring_call_block_code base mulOff).union
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord r0 r1 r2 r3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Pair + JAL: 17 instructions, exit (base+64) + signExtend21 mulOff,
  --     code = exp_squaring_call_block_code base mulOff. Already proven.
  have hpair := exp_loop_squaring_marshal_pair_then_square_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff base
  -- Frame the four extra registers `(.x6, .x7, .x10, .x11)` consumed by
  -- `mul_callable_spec_within` on the right; the marshal pair never touches
  -- them, and the JAL only touches `.x1`.
  have hpairFramed :=
    cpsTripleWithin_frameR
      ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      (by pcFree) hpair
  -- (2) `mul_callable_spec_within` at `mul_target = (base+64)+signExtend21 mulOff`
  --     with `ra_val = base + 68`, working on the LP64 frame at `evmSp`,
  --     squaring `expResultWord r0..r3`.
  have hmul := mul_callable_spec_within
    evmSp mul_target (base + 68)
    (expResultWord r0 r1 r2 r3) (expResultWord r0 r1 r2 r3)
    r3 v6 v7 v10 v11
  -- Frame the local scratch frame `(.x2 ↦ᵣ sp) ** sp[0..24]` on the left;
  -- `mul_callable` does not touch any of those (its LP64 frame is `evmSp`
  -- via `x12`).
  have hmulFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))
      (by pcFree) hmul
  -- (3) Compose. The pair-then-JAL exits at `mul_target = (base+64) +
  --     signExtend21 mulOff` (rewrite via hmt to match the mul_callable
  --     entry). Midpoint permutation: re-associate the framed pair-post
  --     into the framed mul_callable pre, folding the 8-limb sub-tree at
  --     `evmSp[0..56]` into the two `evmWordIs` predicates.
  rw [← hmt] at hpairFramed
  have hseq :
      cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
        ((exp_squaring_call_block_code base mulOff).union
          (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hp => by
          -- The pair-post has 8 explicit memIs atoms at
          --   `evmSp + signExtend12 N` for N = 0,8,..,56.
          -- The mul_callable pre has
          --   `evmWordIs evmSp w ** evmWordIs (evmSp+32) w`
          -- with `w := expResultWord r0 r1 r2 r3`. Expand each `evmWordIs`
          -- to its 4-memIs form (which uses literal `evmSp`, `evmSp+8`, ...
          -- offsets, no `signExtend12` wrapper), canonicalize the pair-post
          -- offsets to match, and permute atom-by-atom.
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
          have hR : evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) = _ :=
            evmWordIs_sp32_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
              (expResultWord_getLimbN_0 r0 r1 r2 r3)
              (expResultWord_getLimbN_1 r0 r1 r2 r3)
              (expResultWord_getLimbN_2 r0 r1 r2 r3)
              (expResultWord_getLimbN_3 r0 r1 r2 r3)
          rw [hL, hR]
          xperm_hyp hp)
        hpairFramed)
      hmulFramed
  -- Re-associate entry pre and exit post into the natural shapes declared
  -- in the theorem's type.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
