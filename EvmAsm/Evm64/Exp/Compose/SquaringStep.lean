/-
  EvmAsm.Evm64.Exp.Compose.SquaringStep

  Small EXP full-loop building blocks around the squaring call path.
-/

import EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Squaring unmarshal word spec lifted to the top-level EXP code bundle
    unioned with the shared `mul_callable` code. -/
theorem exp_squaring_un_marshal_word_evm_exp_union_spec_within
    (sp evmSp tOld r0 r1 r2 r3 mulTarget : Word) (w : EvmWord)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) w)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  have h := exp_squaring_un_marshal_word_evm_exp_spec_within
    sp evmSp tOld r0 r1 r2 r3 w mulOff skipOff backOff base
  exact cpsTripleWithin_extend_code (h := h) (hmono := by
    intro a i hcode
    exact CodeReq.union_mono_left a i hcode)

/-- Ownership-form variant of the squaring unmarshal word spec.  This matches
    the `regOwn .x5` produced by `mul_callable` in the squaring path. -/
theorem exp_squaring_un_marshal_word_evm_exp_union_regOwn5_spec_within
    (sp evmSp r0 r1 r2 r3 mulTarget : Word) (w : EvmWord)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs (evmSp + 32) w) ** regOwn .x5)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn ?_
  intro tOld
  have h := exp_squaring_un_marshal_word_evm_exp_union_spec_within
    sp evmSp tOld r0 r1 r2 r3 mulTarget w mulOff skipOff backOff base
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      xperm_hyp hp)
    (fun _ hp => hp)
    h

/-- Sequence the squaring MUL-call path into the squaring unmarshal step. -/
theorem exp_squaring_mul_call_then_unmarshal_evm_exp_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hmt : mulTarget = (base + 104) + signExtend21 mulOff)
    (halign : ((base + 108) &&& ~~~(1 : Word)) = base + 108)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let w := expResultWord r0 r1 r2 r3
    let sq := w * w
    let frame :=
      ((.x1 ↦ᵣ (base + 108)) ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    cpsTripleWithin ((17 + 64) + 9) (base + 40) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
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
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ sq.getLimbN 3) **
        evmWordIs sp sq ** evmWordIs (evmSp + 32) sq) ** frame) := by
  intro w sq frame
  have hcall := exp_squaring_marshal_pair_then_mul_call_evm_exp_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff skipOff backOff base hmt hd
  rw [halign] at hcall
  have hunm := exp_squaring_un_marshal_word_evm_exp_union_regOwn5_spec_within
    sp evmSp r0 r1 r2 r3 mulTarget sq mulOff skipOff backOff base
  have hunmFramed :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      pcFree) hunm
  have hseq : cpsTripleWithin ((17 + 64) + 9) (base + 40) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget)) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp [frame, w, sq] at hp ⊢
        delta evmMulStackPost at hp
        sep_perm hp)
      hcall hunmFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      dsimp [frame, sq] at hp ⊢
      sep_perm hp)
    hseq

end EvmAsm.Evm64.Exp.Compose
