/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop

  v4/no-NOP wrappers for the n=2 DIV loop-body j=0 exit paths.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Sp-relative n=2 max-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2MaxSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld)

/-- Sp-relative n=2 call-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  regOwn .x1 ** (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- n=2 max-skip j>0 precondition over `divCode_noNop_v4`.
    The j-dependent address lets stay behind this irreducible boundary. -/
@[irreducible]
def loopBodyN2MaxSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  loopBodyN2MaxJgt0Pre j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld

/-- n=2 call-skip j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1

/-- n=2 call-addback j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallAddbackJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem

/-- Loop body n=2, max+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_max_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=2, max+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_max_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, max+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n2_max_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, call+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN2CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN2CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n2_call_skip_jgt0_v4_spec_within_noNop j hpos
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
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
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
      (loopBodyN2CallSkipJgt0PostV4 sp base j
        v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem)) at raw
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, call+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n2_call_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow hcarry2_nz
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, max+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n2_max_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_j0_beq_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=2, call+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_addback_j0_beq_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  rw [loopBodyN2CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN2CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

end EvmAsm.Evm64
