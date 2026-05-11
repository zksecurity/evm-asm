/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1NoNop

  No-NOP prefix composition for the b[3]=b[2]=b[1]=0 (n=1) DIV path.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseABNoNop
import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.Norm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- DIV PhaseAB(n=1) + CLZ over `divCode_noNop`.
    b≠0, b[3]=b[2]=b[1]=0; base → base+212. -/
theorem evm_div_phaseAB_n1_clz_spec_within_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b0).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b0).1) ** (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word))) := by
  have hAB := evm_div_phaseAB_n1_spec_within_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2z hb1z
  have hCLZ := divK_clz_spec_within_noNop b0 b1 b2 base
  have hCLZf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)))
    (by pcFree) hCLZ
  have hABCLZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

/-- DIV PhaseAB(n=1) + CLZ + PhaseC2(ntaken) over `divCode_noNop`.
    This is the shift≠0 prefix that reaches NormB. -/
theorem evm_div_phaseAB_n1_clz_c2_spec_within_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4) base (base + normBOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b0).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b0).1) **
       (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b0).1)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)) := by
  have hABCLZ := evm_div_phaseAB_n1_clz_spec_within_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2z hb1z
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) ** ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_noNop sp (clzResult b0).1
    ((clzResult b0).2 >>> (63 : Nat)) shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b0).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABC2

/-- Precondition for the DIV `n=1` no-NOP prefix through `PhaseAB → CLZ →
    PhaseC2(ntaken) → NormB`: entry registers/scratch carrying the
    original `b[]` and `u/q/nMem/shiftMem` workspace. Wrapped
    `@[irreducible]` so downstream proofs do not re-reduce the 20-atom
    sepConj at each use site. -/
@[irreducible]
def evmDivPhaseABN1ClzC2NormBPre
    (sp v5 v6 v7 v10 b0 b1 b2 b3
      q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
  ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
  ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
  ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
  ((sp + signExtend12 3992) ↦ₘ shiftMem)

theorem evmDivPhaseABN1ClzC2NormBPre_unfold
    {sp v5 v6 v7 v10 b0 b1 b2 b3
      q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word} :
    evmDivPhaseABN1ClzC2NormBPre sp v5 v6 v7 v10 b0 b1 b2 b3
        q0 q1 q2 q3 u5 u6 u7 nMem shiftMem =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem)) := by
  delta evmDivPhaseABN1ClzC2NormBPre
  rfl

/-- Postcondition: shifted `b[]` written back to the scratch limbs,
    `x5`/`x6`/`x7`/`x2` carry the working scratch (`b0'`, `shift`,
    high-anti-shifted `b0`, `antiShift`), and `q[]`/`u[]` slots cleared,
    `nMem ← 1`, `shiftMem ← shift`. Wrapped `@[irreducible]`. -/
@[irreducible]
def evmDivPhaseABN1ClzC2NormBPost
    (sp b0 b3 shift antiShift b0' b1' b2' b3' : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift)

theorem evmDivPhaseABN1ClzC2NormBPost_unfold
    {sp b0 b3 shift antiShift b0' b1' b2' b3' : Word} :
    evmDivPhaseABN1ClzC2NormBPost sp b0 b3 shift antiShift b0' b1' b2' b3' =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) ** (.x2 ↦ᵣ antiShift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  delta evmDivPhaseABN1ClzC2NormBPost
  rfl

theorem evm_div_phaseAB_n1_clz_c2_normB_spec_within_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    let shift := (clzResult b0).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_noNop base)
      (evmDivPhaseABN1ClzC2NormBPre sp v5 v6 v7 v10 b0 b1 b2 b3
        q0 q1 q2 q3 u5 u6 u7 nMem shiftMem)
      (evmDivPhaseABN1ClzC2NormBPost sp b0 b3 shift antiShift
        b0' b1' b2' b3') := by
  intro shift antiShift b3' b2' b1' b0'
  rw [evmDivPhaseABN1ClzC2NormBPre_unfold,
      evmDivPhaseABN1ClzC2NormBPost_unfold]
  have hC2 := evm_div_phaseAB_n1_clz_c2_spec_within_noNop sp base
    b0 b1 b2 b3 v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1z hshift_nz
  have hNB := divK_normB_full_spec_within_noNop sp b0 b1 b2 b3
    (clzResult b0).2 ((clzResult b0).2 >>> (63 : Nat))
    shift antiShift base
  intro_lets at hNB
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

end EvmAsm.Evm64
