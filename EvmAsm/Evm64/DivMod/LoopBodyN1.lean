/-
  EvmAsm.Evm64.DivMod.LoopBodyN1

  Fixed loop body compositions for n=1 (1-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v0 overlaps in the generic spec.

  For n=1, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4088  (both refer to u[j+1])
  2. uAddr + 8 = uBase + signExtend12 0  (both refer to u[j+0])
  3. vtopBase + signExtend12 32 = sp + signExtend12 32  (both refer to v[0])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting uAddr and vtopBase to canonical uBase-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoop
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq
import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=1 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=1: uAddr = uBase + signExtend12 4088 -/
theorem u_addr_eq_n1 {sp j : Word} :
    sp + signExtend12 4056 - (j + (1 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- For n=1: (uBase + signExtend12 4088) + 8 = uBase + signExtend12 0 -/
theorem u_addr8_eq_n1 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0 := by
  divmod_addr

/-- For n=1: vtopBase + signExtend12 32 = sp + signExtend12 32 -/
theorem vtop_eq_v0_n1 {sp : Word} :
    (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 32 := by
  divmod_addr

-- ============================================================================
-- Trial wrappers for n=1 with addresses rewritten to canonical uBase-relative form
-- ============================================================================

/-- Trial max full spec specialized for n=1, with addresses rewritten. -/
theorem divK_trial_max_full_spec_n1_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old u1 u0 v0 : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 16 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((uBase + signExtend12 4088) ↦ₘ u1) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 32) ↦ₘ v0))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ u1) ** (.x10 ↦ᵣ v0) ** (.x11 ↦ᵣ signExtend12 4095) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((uBase + signExtend12 4088) ↦ₘ u1) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 32) ↦ₘ v0)) := by
  intro uBase vtopBase
  have TF := divK_trial_max_full_spec_within sp j (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  exact TF

theorem divK_trial_call_full_spec_n1_within
    (sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old u1 u0 v0 : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let dHi := v0 >>> (32 : BitVec 6).toNat
    let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u0 >>> (32 : BitVec 6).toNat
    let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u1 dHi
    let rhat := u1 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dLo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
    let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTripleWithin 66 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((uBase + signExtend12 4088) ↦ₘ u1) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 32) ↦ₘ v0) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ x1Exit) **
       (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1') ** (.x11 ↦ᵣ qHat) **
       (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((uBase + signExtend12 4088) ↦ₘ u1) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 32) ↦ₘ v0) **
       (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
       (sp + signExtend12 3960 ↦ₘ v0) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro uBase
        dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0Dlo rhat2Un0
        rhat2cHi q0' x7Exit x1Exit qHat
  have TF := divK_trial_call_full_spec_within sp j (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  exact TF

end EvmAsm.Evm64
