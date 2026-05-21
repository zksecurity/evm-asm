/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNop

  v4/no-NOP wrappers for the n=1 DIV loop-body j=0 exit paths.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.MaxAddbackV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.CallAddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 jpred_2 jpred_3 slt_jpos_1 slt_jpos_2 slt_jpos_3)

/-- DIV PhaseAB(n=1) + CLZ + PhaseC2(ntaken) + NormB over
    `divCode_noNop_v4`. This is the shift≠0 prefix that reaches NormA
    using the bundled n=1 no-NOP prefix pre/post shape. -/
theorem evm_div_phaseAB_n1_clz_c2_normB_spec_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_noNop_v4 base)
      (evmDivPhaseABN1ClzC2NormBPre sp v5 v6 v7 v10 b0 b1 b2 b3
        q0 q1 q2 q3 u5 u6 u7 nMem shiftMem)
      (evmDivPhaseABN1ClzC2NormBFullPost sp b0 b1 b2 b3) := by
  simp only [evmDivPhaseABN1ClzC2NormBPre_unfold,
             evmDivPhaseABN1ClzC2NormBFullPost_unfold]
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  have hC2 := evm_div_phaseAB_n1_clz_c2_spec_v4_noNop sp base
    b0 b1 b2 b3 v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1z hshift_nz
  have hNB := divK_normB_full_spec_within_v4_noNop sp b0 b1 b2 b3
    (clzResult b0).2 ((clzResult b0).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- Sp-relative n=1 max-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN1MaxSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld)

/-- Sp-relative n=1 call-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN1CallSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN1MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1

/-- n=1 max-skip j>0 precondition over `divCode_noNop_v4`.
    The address computations are hidden here to keep loop-back bridge statements small. -/
@[irreducible]
def loopBodyN1MaxSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

/-- n=1 call-skip j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN1CallSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN1MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1

/-- Loop body n=1, max+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n1_max_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n1_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu
  change (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopBodyN1SkipPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
  have raw0 := raw hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN1MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=1, max+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n1_max_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu
  change (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopBodyN1SkipPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
  have raw0 := raw hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN1MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=1, max path, j=3 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit while
    preserving concrete `x1`. -/
theorem divK_loop_body_n1_max_j3_exact_loopIter_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (3 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_jgt0_beq_v4_spec_within_noNop
      (3 : Word) slt_jpos_3
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu hcarry2_nz
    change (let uBase := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff)
        (sharedDivModCodeNoNop_v4 base)
        ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (3 : Word)) **
         (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
         (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
         (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
         ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
         ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
         ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
         ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
         ((uBase + signExtend12 4064) ↦ₘ uTop) **
         (qAddr ↦ₘ qOld))
        (loopBodyN1AddbackBeqPost sp (3 : Word) (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJgt0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop
      (3 : Word) sp base slt_jpos_3
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Loop body n=1, max path, j=2 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit while
    preserving concrete `x1`. -/
theorem divK_loop_body_n1_max_j2_exact_loopIter_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (2 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_jgt0_beq_v4_spec_within_noNop
      (2 : Word) slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu hcarry2_nz
    change (let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff)
        (sharedDivModCodeNoNop_v4 base)
        ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
         (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
         (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
         (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
         ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
         ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
         ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
         ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
         ((uBase + signExtend12 4064) ↦ₘ uTop) **
         (qAddr ↦ₘ qOld))
        (loopBodyN1AddbackBeqPost sp (2 : Word) (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJgt0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop
      (2 : Word) sp base slt_jpos_2
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Loop body n=1, max path, j=1 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit while
    preserving concrete `x1`. -/
theorem divK_loop_body_n1_max_j1_exact_loopIter_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (1 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_jgt0_beq_v4_spec_within_noNop
      (1 : Word) slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu hcarry2_nz
    change (let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff)
        (sharedDivModCodeNoNop_v4 base)
        ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
         (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
         (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
         (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
         ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
         ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
         ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
         ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
         ((uBase + signExtend12 4064) ↦ₘ uTop) **
         (qAddr ↦ₘ qOld))
        (loopBodyN1AddbackBeqPost sp (1 : Word) (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJgt0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop
      (1 : Word) sp base slt_jpos_1
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Loop body n=1, max path, j=0 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit while
    preserving concrete `x1`. -/
theorem divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hb : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hb]
      decide
    have raw := divK_loop_body_n1_max_addback_j0_beq_v4_spec_within_noNop
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      base hbltu hcarry2_nz
    change (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
      let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
      (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
       then (1 : Word) else 0) ≠ (0 : Word) →
      cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff)
        (sharedDivModCodeNoNop_v4 base)
        ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
         (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
         (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
         (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
         ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
         ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
         ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
         ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
         ((uBase + signExtend12 4064) ↦ₘ uTop) **
         (qAddr ↦ₘ qOld))
        (loopBodyN1AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop)) at raw
    have raw0 := raw hborrow
    have raw' := cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw0
    simp only [se12_32, se12_40, se12_48, se12_56,
               u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
               u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw'
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN1MaxSkipJ0NormPreV4 at hp
        xperm_hyp hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]
        exact hp)
      framed
  · have hborrow :
        (if BitVec.ult uTop
            (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have raw := divK_loop_body_n1_max_skip_j0_norm_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow
    have framed := cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) raw
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]
        exact hp)
      (cpsTripleWithin_mono_nSteps (by decide) framed)

/-- Exact-`x1` N1 two-iteration max/max path over `divCode_noNop_v4`.
    This composes the j=1 and j=0 max loop-body wrappers while keeping
    the caller's concrete return address outside the loop post. -/
theorem divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_1 : ¬BitVec.ult u1 v0)
    (hbltu_0 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter10PostNoX1 false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n1_max_j1_exact_loopIter_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop :
      isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J1
  have J0 := divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop
    sp base (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
      (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopBodyN1MaxSkipJ0NormPreV4 at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_n1_j1_0_eq_j0_4088, u_n1_j1_4088_eq_j0_4080,
          u_n1_j1_4080_eq_j0_4072, u_n1_j1_4072_eq_j0_4064] at hp
      dsimp only [u_base_0, u_base_1, q_addr_0, q_addr_1] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter10PostNoX1 loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- Exact-`x1` N1 three-iteration all-max path over `divCode_noNop_v4`.
    This composes the j=2 max loop body with the exact j=1/j=0 max/max
    iter10 wrapper while keeping the caller return address framed outside. -/
theorem divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let r2 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J2 := divK_loop_body_n1_max_j2_exact_loopIter_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal hbltu_2
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop :
      isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0Orig1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0Orig0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J2
  have H10 := divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop
    sp base (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0Orig0 q1Old q0Old
    retMem dMem dloMem scratch_un0 raVal hbltu_1 hbltu_0 hcarry2
  have H10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter10PreWithScratchNoX1 loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088, u_n1_j2_4088_eq_j1_4080,
          u_n1_j2_4080_eq_j1_4072, u_n1_j2_4072_eq_j1_4064] at hp
      dsimp only [u_base_0, u_base_1, u_base_2, q_addr_0, q_addr_1, q_addr_2] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      dsimp only [u_base_0, u_base_1, u_base_2, q_addr_0, q_addr_1, q_addr_2] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210PostNoX1 loopN1Iter10PostNoX1
        loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, if_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- Exact-`x1` N1 four-iteration all-max path over `divCode_noNop_v4`.
    This composes the j=3 max loop body with the exact j=2/j=1/j=0
    iter210 wrapper while keeping the caller return address framed outside. -/
theorem divK_loop_n1_maxmaxmaxmax_exact_x1_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 758 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1UnifiedPostNoX1 false false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  let r3 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_max_j3_exact_loopIter_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old raVal hbltu_3
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop :
      isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0Orig2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0Orig1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0Orig0) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J3
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop
    sp base (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0Orig1 u0Orig0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 raVal hbltu_2 hbltu_1 hbltu_0 hcarry2
  have H210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 loopExitPost at hp
      delta loopN1Iter210PreWithScratchNoX1 loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      dsimp only [u_base_0, u_base_1, u_base_2, u_base_3,
        q_addr_0, q_addr_1, q_addr_2, q_addr_3] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1PreWithScratchNoX1 loopN1Pre at hp
      delta loopBodyN1MaxSkipJgt0NormPreV4 at ⊢
      dsimp only [u_base_0, u_base_1, u_base_2, u_base_3,
        q_addr_0, q_addr_1, q_addr_2, q_addr_3] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPostNoX1 loopN1Iter210PostNoX1 loopN1Iter10PostNoX1
        loopIterPostN1NoX1 loopIterPostN1Max at hp ⊢
      simp only [iterN1_false, Bool.false_eq_true, if_false, sepConj_emp_right'] at hp ⊢
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    full

/-- Loop body n=1, call+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n1_call_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  unfold loopBodyN1CallSkipJ0PreV4 at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN1CallSkipJ0NormPreV4 loopBodyN1MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=1, call+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n1_call_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  change (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopBodyN1CallSkipJgt0PostV4 sp base j
        v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem)) at raw
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN1CallSkipJgt0NormPreV4 loopBodyN1MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=1, call+addback, j>0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n1_call_addback_jgt0_exact_loopIterScratch_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n1_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1_loopIterScratch j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Loop body n=1, call+skip, j=0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n1_call_skip_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n1_call_skip_j0_v4_spec_within_noNop_exact_x1_loopIterScratch
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- Loop body n=1, call+skip, j>0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n1_call_skip_jgt0_exact_loopIterScratch_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n1_call_skip_jgt0_v4_spec_within_noNop_exact_x1_loopIterScratch j hpos
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- Loop body n=1, call+addback, j=0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n1_call_addback_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_loop_body_n1_call_addback_j0_beq_v4_spec_within_noNop_exact_x1_loopIterScratch
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Loop body n=1, call path, j=0 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n1_call_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · have hborrow_nz :
        (if BitVec.ult uTop
            (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
          then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    exact divK_loop_body_n1_call_addback_j0_exact_loopIterScratch_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN1CallSkipJ0BorrowV4 mulsubN4NoBorrow
      dsimp only
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n1_call_skip_j0_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- Loop body n=1, call path, j>0 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n1_call_jgt0_exact_loopIterScratch_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · have hborrow_nz :
        (if BitVec.ult uTop
            (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
          then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    exact divK_loop_body_n1_call_addback_jgt0_exact_loopIterScratch_v4_noNop
      j sp base hpos jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n1_call_skip_jgt0_exact_loopIterScratch_v4_noNop
        j sp base hpos jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- Loop body n=1, call path, j=3 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n1_call_j3_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp (3 : Word)
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (3 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact divK_loop_body_n1_call_jgt0_exact_loopIterScratch_v4_noNop
    (3 : Word) sp base slt_jpos_3
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz

/-- Explicit no-`x1` precondition for the N1 path where j=3 uses the v4
    call path and j=2/j=1/j=0 all use max. It extends the ordinary no-X1
    loop precondition with the extra v4 div128 scratch cell. -/
@[irreducible]
def loopN1CallMaxmaxmaxScratchPreNoX1 (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratchUn0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- First j=3 call-body step for the N1 call/max/max/max path. This
    exposes the v4-call scratch post while framing the j=2/j=1/j=0 cells
    needed by the following all-max iter210 wrapper. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (3 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal) **
        ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig2) **
        ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q2Old) **
        ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig1) **
        ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old) **
        ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig0) **
        ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)) := by
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_call_j3_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J3f := cpsTripleWithin_frameR
    (((uBase2 + signExtend12 0) ↦ₘ u0Orig2) ** (qAddr2 ↦ₘ q2Old) **
     ((uBase1 + signExtend12 0) ↦ₘ u0Orig1) ** (qAddr1 ↦ₘ q1Old) **
     ((uBase0 + signExtend12 0) ↦ₘ u0Orig0) ** (qAddr0 ↦ₘ q0Old))
    (by pcFree) J3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN1CallMaxmaxmaxScratchPreNoX1 loopN1PreWithScratchNoX1 loopN1Pre at hp
      delta loopBodyN1CallSkipJgt0PreV4NoX1 at ⊢
      dsimp only [uBase2, qAddr2, uBase1, qAddr1, uBase0, qAddr0] at hp ⊢
      simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      dsimp only [uBase2, qAddr2, uBase1, qAddr1, uBase0, qAddr0] at hp
      rw [sepConj_assoc'] at hp
      exact hp)
    J3f

/-- Explicit no-`x1` post for the N1 path where j=3 uses the v4 call path
    and j=2/j=1/j=0 all use max. The extra v4 div128 scratch cell is
    retained as caller frame state. -/
@[irreducible]
def loopN1CallMaxmaxmaxScratchPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem : Word) : Assertion :=
  let r3 := iterWithDoubleAddback (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3
    u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0Orig1 u0Orig0
    (base + div128CallRetOff) v0 (divKTrialCallV4DLo v0) (divKTrialCallV4Un0 u0) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)

/-- Double-addback progress for the v4 n=1 call path, using the quotient
    selected by `divKTrialCallV4QHat`. -/
@[irreducible]
def isAddbackCarry2NzN1CallV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialize the universal double-addback carry hypothesis to the quotient
    selected by the v4 n=1 call path. -/
theorem isAddbackCarry2NzN1CallV4_of_carry2All
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold isAddbackCarry2NzN1CallV4
  exact hcarry2 (divKTrialCallV4QHat u1 u0 v0) u0 u1 u2 u3 uTop

/-- Expand the compact v4 n=1 call carry predicate into the raw
    double-addback progress hypothesis expected by the j=3 call-body spec. -/
theorem isAddbackCarry2NzN1CallV4_raw
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hcarry2 : isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let qHat := divKTrialCallV4QHat u1 u0 v0
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
  simpa [isAddbackCarry2NzN1CallV4, isAddbackCarry2Nz] using hcarry2

/-- Result of the j=3 v4 call iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (divKTrialCallV4QHat u1 u0 v0)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Result of the following j=2 all-max iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterN1Max v0 v1 v2 v3 u0Orig2
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

/-- Result of the following j=1 all-max iteration in the N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxR1
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  iterN1Max v0 v1 v2 v3 u0Orig1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

/-- Compact all-max branch facts after the j=3 v4 call iteration in the
    N1 call/max/max/max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxBranchFacts
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 : Word) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  ¬BitVec.ult r3.2.1 v0 ∧
  ¬BitVec.ult r2.2.1 v0 ∧
  ¬BitVec.ult r1.2.1 v0

/-- Build the compact all-max branch-fact bundle from the three branch
    conditions that follow the j=3 v4 call iteration. -/
theorem loopN1CallMaxmaxmaxBranchFacts_of_bltu
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1 v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1).2.1 v0) :
    loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  unfold loopN1CallMaxmaxmaxBranchFacts
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0)
  exact ⟨by simpa [r3] using hbltu2, by
    exact ⟨by simpa [r2] using hbltu1, by simpa [r1] using hbltu0⟩⟩

/-- The j=2 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r3] using hbranches'.1

/-- The j=1 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu1
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r2] using hbranches'.2.1

/-- The j=0 all-max branch fact packaged in
    `loopN1CallMaxmaxmaxBranchFacts`. -/
theorem loopN1CallMaxmaxmaxBranchFacts_hbltu0
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1).2.1 v0 := by
  let r3 := loopN1CallMaxmaxmaxR3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r2 := loopN1CallMaxmaxmaxR2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2
  let r1 := loopN1CallMaxmaxmaxR1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1
  have hbranches' := hbranches
  unfold loopN1CallMaxmaxmaxBranchFacts at hbranches'
  change (¬BitVec.ult r3.2.1 v0 ∧ ¬BitVec.ult r2.2.1 v0 ∧
      ¬BitVec.ult r1.2.1 v0) at hbranches'
  simpa [r1] using hbranches'.2.2

/-- The named scratch precondition is PC-free, so later composed call/max
    surfaces can use it under `cpsTripleWithin_frameR`. -/
theorem loopN1CallMaxmaxmaxScratchPreNoX1_pcFree (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    (loopN1CallMaxmaxmaxScratchPreNoX1 sp
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem).pcFree := by
  delta loopN1CallMaxmaxmaxScratchPreNoX1
  pcFree

instance pcFreeInst_loopN1CallMaxmaxmaxScratchPreNoX1 (sp : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion.PCFree
      (loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem) :=
  ⟨loopN1CallMaxmaxmaxScratchPreNoX1_pcFree sp
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
    retMem dMem dloMem scratchUn0 scratchMem⟩

/-- Opaque statement wrapper for the N1 path where j=3 uses the v4 call path
    and j=2/j=1/j=0 all use max. Keeping this triple behind a name avoids
    repeatedly elaborating the full pre/post shape at downstream theorem
    declarations. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactX1ScratchSpec (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word) : Prop :=
  cpsTripleWithin 780 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 sp
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
    (loopN1CallMaxmaxmaxScratchPostNoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem ** (.x1 ↦ᵣ raVal))

/-- Compact assumptions for the N1 call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactHypotheses
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word) : Prop :=
  BitVec.ult u1 v0 ∧
  loopN1CallMaxmaxmaxBranchFacts v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 ∧
  Carry2NzAll v0 v1 v2 v3 ∧
  isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Build the compact N1 call/max/max/max exact-path hypothesis bundle from
    the branch facts plus the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_of_branches
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (hbltu3 : BitVec.ult u1 v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses
  exact ⟨hbltu3, hbranches, hcarry2,
    isAddbackCarry2NzN1CallV4_of_carry2All
      v0 v1 v2 v3 u0 u1 u2 u3 uTop hcarry2⟩

/-- Project the j=3 BLTU-taken fact from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_hbltu3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    BitVec.ult u1 v0 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.1

/-- Project the all-max branch facts from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_branches
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    loopN1CallMaxmaxmaxBranchFacts
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.1

/-- Project the global carry2 condition from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_carry2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    Carry2NzAll v0 v1 v2 v3 := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.2.1

/-- Project the v4 N1 call carry condition from the compact N1 call/max/max/max hypotheses. -/
theorem loopN1CallMaxmaxmaxExactHypotheses_carry2Call
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 : Word)
    (h : loopN1CallMaxmaxmaxExactHypotheses
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1) :
    isAddbackCarry2NzN1CallV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.2.2

/-- Bundle the many scalar inputs to the N1 call/max/max/max exact path.
    This gives later theorem statements a single data parameter instead of a
    long spine of old-register, limb, scratch, and memory-cell arguments. -/
structure LoopN1CallMaxmaxmaxExactInputs where
  sp : Word
  base : Word
  jOld : Word
  v5Old : Word
  v6Old : Word
  v7Old : Word
  v10Old : Word
  v11Old : Word
  v2Old : Word
  v0 : Word
  v1 : Word
  v2 : Word
  v3 : Word
  u0 : Word
  u1 : Word
  u2 : Word
  u3 : Word
  uTop : Word
  u0Orig2 : Word
  u0Orig1 : Word
  u0Orig0 : Word
  q3Old : Word
  q2Old : Word
  q1Old : Word
  q0Old : Word
  retMem : Word
  dMem : Word
  dloMem : Word
  scratchUn0 : Word
  scratchMem : Word
  raVal : Word

/-- Canonical bundled inputs for the full-DIV n=1 branch where the j=3
    iteration uses the v4 call path and j=2/j=1/j=0 use all-max. -/
def fullDivN1CallMaxmaxmaxExactInputs (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    LoopN1CallMaxmaxmaxExactInputs :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  { sp := sp
    base := base
    jOld := jOld
    v5Old := v5Old
    v6Old := v6Old
    v7Old := v7Old
    v10Old := v10Old
    v11Old := v11Old
    v2Old := v2Old
    v0 := v.1
    v1 := v.2.1
    v2 := v.2.2.1
    v3 := v.2.2.2
    u0 := u.2.2.2.1
    u1 := u.2.2.2.2
    u2 := 0
    u3 := 0
    uTop := 0
    u0Orig2 := u.2.2.1
    u0Orig1 := u.2.1
    u0Orig0 := u.1
    q3Old := q3Old
    q2Old := q2Old
    q1Old := q1Old
    q0Old := q0Old
    retMem := retMem
    dMem := dMem
    dloMem := dloMem
    scratchUn0 := scratchUn0
    scratchMem := scratchMem
    raVal := raVal }

/-- The full-DIV n=1 j=3 trial predicate gives the j=3 taken branch fact
    for the canonical call/max/max/max bundled inputs. -/
theorem fullDivN1CallMaxmaxmaxExactInputs_hbltu3
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0) :
    BitVec.ult
      (fullDivN1CallMaxmaxmaxExactInputs sp base
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        a0 a1 a2 a3 b0 b1 b2 b3
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal).u1
      (fullDivN1CallMaxmaxmaxExactInputs sp base
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        a0 a1 a2 a3 b0 b1 b2 b3
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal).v0 := by
  unfold isTrialN1_j3 at hbltu3
  unfold fullDivN1CallMaxmaxmaxExactInputs fullDivN1NormU fullDivN1NormV
    fullDivN1AntiShift fullDivN1Shift
  simpa using hbltu3.symm

/-- Spec wrapper specialized to bundled N1 call/max/max/max inputs. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  loopN1CallMaxmaxmaxExactX1ScratchSpec I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal

/-- Final spec wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputSpec (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputSpec
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Compact hypotheses specialized to bundled N1 call/max/max/max inputs. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  loopN1CallMaxmaxmaxExactHypotheses
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1

/-- Build the bundled N1 call/max/max/max exact-path hypothesis wrapper
    from the bundled branch facts plus the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_of_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses
  exact loopN1CallMaxmaxmaxExactHypotheses_of_branches
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    hbltu3 hbranches hcarry2

/-- Build the bundled N1 call/max/max/max exact-path hypotheses directly
    from the four path branch facts and the universal carry2 assumption. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputHypotheses I := by
  exact loopN1CallMaxmaxmaxExactInputHypotheses_of_branches I hbltu3
    (loopN1CallMaxmaxmaxBranchFacts_of_bltu
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
      hbltu2 hbltu1 hbltu0)
    hcarry2

/-- Project the j=3 BLTU-taken fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_hbltu3
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the all-max branch facts from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_branches
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the global carry2 condition from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_carry2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    Carry2NzAll I.v0 I.v1 I.v2 I.v3 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_carry2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the v4 N1 call carry condition from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    isAddbackCarry2NzN1CallV4 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  exact loopN1CallMaxmaxmaxExactHypotheses_carry2Call
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 h

/-- Project the j=2 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Project the j=1 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Project the j=0 all-max branch fact from bundled N1 call/max/max/max inputs. -/
theorem loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxExactInputHypotheses_branches I h)

/-- Bundled alignment condition for the v4 div128 call return address. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputAligned
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  ((I.base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
    ~~~(1 : Word) = I.base + div128CallRetOff

/-- Unpack bundled alignment into the raw equality expected by the j=3 call step. -/
theorem loopN1CallMaxmaxmaxExactInputAligned_raw
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputAligned I) :
    ((I.base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
      ~~~(1 : Word) = I.base + div128CallRetOff := by
  unfold loopN1CallMaxmaxmaxExactInputAligned at h
  exact h

/-- Alignment wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputAligned (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputAligned
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Hypothesis wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputHypotheses (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputHypotheses
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Build the canonical full-DIV n=1 call/max/max/max hypothesis wrapper
    from the path branch facts and the universal carry2 assumption. -/
theorem fullDivN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses
  exact loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (fullDivN1CallMaxmaxmaxExactInputs_hbltu3 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3)
    hbltu2 hbltu1 hbltu0 hcarry2

/-- Bundled statement for the first j=3 call-body step of the N1
    call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxJ3ExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 224 (I.base + loopBodyOff) (I.base + loopBodyOff)
    (divCode_noNop_v4 I.base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
      I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))
    (loopIterPostN1CallScratchNoX1 I.sp I.base (3 : Word)
      (divKTrialCallV4QHat I.u1 I.u0 I.v0)
      (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0)
      (divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop **
      (.x1 ↦ᵣ I.raVal) **
      ((I.sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig2) **
      ((I.sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q2Old) **
      ((I.sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig1) **
      ((I.sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q1Old) **
      ((I.sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig0) **
      ((I.sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q0Old))

/-- Prove the bundled first j=3 call-body step from the bundled input
    alignment and branch/carry hypotheses. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec
  exact divK_loop_n1_call_j3_exact_x1_framed_v4_noNop I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call I hh))

/-- Bundled statement for the j=2/j=1/j=0 all-max tail after the first
    j=3 call-body step in the N1 call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210ExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_noNop_v4 I.base)
    (loopN1Iter210PreWithScratchNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
      (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))
    (loopN1Iter210PostNoX1 false false false I.sp I.base I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 (I.base + div128CallRetOff) I.v0
      (divKTrialCallV4DLo I.v0) (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))

/-- Prove the bundled all-max tail after the first j=3 call-body step. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (loopN1CallMaxmaxmaxExactInputHypotheses_carry2 I hh)

/-- Actual assertion produced by the bundled j=3 call-body step, including
    the cells framed for the following all-max tail. -/
@[irreducible]
def loopN1CallMaxmaxmaxJ3PostInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  loopIterPostN1CallScratchNoX1 I.sp I.base (3 : Word)
    (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0)
    (divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop **
  (.x1 ↦ᵣ I.raVal) **
  ((I.sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig2) **
  ((I.sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q2Old) **
  ((I.sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig1) **
  ((I.sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q1Old) **
  ((I.sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig0) **
  ((I.sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q0Old)

/-- Frame cells carried around the j=2/j=1/j=0 all-max tail after the
    bundled j=3 call-body step. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FrameInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  ((uBase3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) **
  (qAddr3 ↦ₘ r3.1) **
  (I.sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)

/-- The j=3 frame carried around the all-max tail is PC-free. -/
theorem loopN1CallMaxmaxmaxIter210FrameInput_pcFree
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    (loopN1CallMaxmaxmaxIter210FrameInput I).pcFree := by
  delta loopN1CallMaxmaxmaxIter210FrameInput
  pcFree

instance pcFreeInst_loopN1CallMaxmaxmaxIter210FrameInput
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    Assertion.PCFree (loopN1CallMaxmaxmaxIter210FrameInput I) :=
  ⟨loopN1CallMaxmaxmaxIter210FrameInput_pcFree I⟩

/-- Bundled framed all-max tail from the actual j=3 post to the final
    N1 call/max/max/max scratch post. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_noNop_v4 I.base)
    (loopN1CallMaxmaxmaxJ3PostInput I)
    (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))

/-- The precondition required by the framed all-max tail after the actual
    bundled j=3 call-body step. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedPreInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  (loopN1Iter210PreWithScratchNoX1 I.sp
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal)) **
  loopN1CallMaxmaxmaxIter210FrameInput I

/-- Rearrange the actual bundled j=3 post into the framed all-max tail
    precondition. -/
theorem loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    ∀ h,
      loopN1CallMaxmaxmaxJ3PostInput I h →
      loopN1CallMaxmaxmaxIter210FramedPreInput I h := by
  intro h hp
  delta loopN1CallMaxmaxmaxJ3PostInput loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FrameInput at hp ⊢
  delta loopIterPostN1CallScratchNoX1 loopN1Iter210PreWithScratchNoX1
    loopN1Iter210Pre loopExitPostN1 loopExitPost at hp ⊢
  dsimp only at hp ⊢
  have hj' := jpred_3
  rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
      u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
  unfold loopN1CallMaxmaxmaxR3
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- The post produced by framing the bundled all-max tail with the j=3
    q/top/scratch cells. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedPostInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  (loopN1Iter210PostNoX1 false false false I.sp I.base I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 (I.base + div128CallRetOff) I.v0
    (divKTrialCallV4DLo I.v0) (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal)) **
  loopN1CallMaxmaxmaxIter210FrameInput I

/-- Rearrange the framed all-max tail post into the final bundled N1
    call/max/max/max scratch post. -/
theorem loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    ∀ h,
      loopN1CallMaxmaxmaxIter210FramedPostInput I h →
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) h := by
  intro h hp
  delta loopN1CallMaxmaxmaxIter210FramedPostInput
    loopN1CallMaxmaxmaxIter210FrameInput loopN1CallMaxmaxmaxScratchPostNoX1 at hp ⊢
  unfold loopN1CallMaxmaxmaxR3 at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- The framed all-max tail over the compact pre/post assertions that sit
    between the j=3 call-body step and the final scratch post. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_noNop_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (loopN1CallMaxmaxmaxExactInputHypotheses_carry2 I hh)
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210FramedExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input I hh)

/-- Full bundled N1 call/max/max/max exact path: j=3 uses the v4 call
    path and j=2/j=1/j=0 all use the all-max path. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxExactInputSpec
  unfold loopN1CallMaxmaxmaxExactX1ScratchSpec
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at Htail
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Final bundled N1 call/max/max/max exact path, with hypotheses supplied
    directly as path branch facts plus the universal carry2 assumption. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_bltu
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop I halign
    (loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu I
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpec
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs, with hypotheses supplied directly as path branch facts
    plus the universal carry2 assumption. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop_of_bltu
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    halign
    (fullDivN1CallMaxmaxmaxExactInputHypotheses_of_bltu sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

end EvmAsm.Evm64
