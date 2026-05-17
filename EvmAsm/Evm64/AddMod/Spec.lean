/-
  EvmAsm.Evm64.AddMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_addmod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  The general `evm_addmod_stack_spec_within` theorem lands in slice
  evm-asm-sord and is composed from the verified shared bridge with
  the boundary blocks. The addmod-correctness lemma
  `EvmWord.addmod_correct` is added in an earlier slice (see
  parent task evm-asm-z7qm).

  Architecture notes for N=0 case (bead evm-asm-a32mz):
  - When N=0, the mod callable follows the zeroPath: stores zeros at
    x12+32..x12+56 WITHOUT advancing x12.
  - cc_ret preserves x1=(base+128) through the zeroPath.
  - After cc_ret, the epilogue at base+128 advances x12 by 32.
  - Net: x12 goes sp → sp+32 (prologue) → sp+32 (zeroPath) → sp+64 (epilogue).
  - Result (zero) sits at sp+64 = final x12. Correct for ADDMOD pop-3-push-1.
  - Infrastructure available: evm_mod_callable_bzero_preserving_x1_spec
    (from DivMod/Callable.lean, PR #4616) enables the proof.
-/

import EvmAsm.Evm64.AddMod.Compose.Base
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.LiftSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.AddMod.Compose

/-! ## ADDMOD N=0 dispatch bridge

The bridge lemma connects the prologue postcondition
`evmAddModPhase1Phase2LimbPost` (for b=N=0) to the mod callable
precondition `divModStackDispatchPre`. This is the key step enabling
the N=0 end-to-end proof (bead evm-asm-a32mz).

Key simplification: when b=0 (the second ADDMOD operand = N = 0),
all carry computations yield 0, so sum = a (the first operand
unchanged), and the prologue POST has concrete zero carries.
-/

/-- When b=0, the carry chain in `evmAddModPhase1Phase2LimbPost` is trivial.
    All carries are 0, so `sum = a` (all limbs). -/
private theorem evmAddModPhase1Phase2LimbPost_b0_simp
    (base sp a0 a1 a2 a3 : Word) :
    evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 0 0 0 0 =
    (((.x12 ↦ᵣ (sp + 32)) **
      (.x7 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + 32) ↦ₘ a0) ** ((sp + 40) ↦ₘ a1) **
      ((sp + 48) ↦ₘ a2) ** ((sp + 56) ↦ₘ a3)) **
     (.x1 ↦ᵣ ((base + 124) + 4))) := by
  simp [evmAddModPhase1Phase2LimbPost_unfold, BitVec.ult]
  simp [signExtend12, BitVec.signExtend]

/-- Dispatch bridge for ADDMOD N=0: from the prologue POST (b=0 simplified)
    plus register/memory frame, to the mod callable dispatch PRE.

    The prologue POST carries:
    - x12=sp+32, x1=base+128 (= raVal)
    - Carry registers = 0 (since b=0 means no carry anywhere)
    - Sum at sp+32..sp+56 = a (same as original, since a+0=a)
    - Original a at sp..sp+24

    Combined with the frame (x2, x10, x0=0, N=0 at sp+64..sp+88, scratch),
    this gives exactly `divModStackDispatchPre (sp+32) a 0 (base+128) ...`. -/
private theorem evm_addmod_n0_dispatch_bridge
    (sp base : Word) (a : EvmWord)
    (a0 a1 a2 a3 v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (s : PartialState)
    (hpre :
      (evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 0 0 0 0 **
       (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 64) ↦ₘ (0 : Word)) ** ((sp + 72) ↦ₘ (0 : Word)) **
       ((sp + 80) ↦ₘ (0 : Word)) ** ((sp + 88) ↦ₘ (0 : Word)) **
       divScratchValuesCall (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0) s) :
    (divModStackDispatchPre (sp + 32) a (0 : EvmWord) ((base + 124) + 4)
       v2 0 0 0 v10 0
       q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
     (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) s := by
  rw [divModStackDispatchPre_unfold]
  rw [evmAddModPhase1Phase2LimbPost_b0_simp] at hpre
  -- Expand evmWordIs (sp+32) a → atoms at sp+32..sp+56
  simp only [evmWordIs_sp32_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3]
  -- Expand evmWordIs (sp+32+32) 0 → atoms at sp+64..sp+88
  simp only [evmWordIs_sp_limbs_eq (sp + 32 + 32) (0 : EvmWord) 0 0 0 0
    (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
    (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)]
  -- Normalize addresses and reduce concrete sums
  simp only [BitVec.add_assoc] at hpre ⊢
  simp only [show (32 : Word) + 8 = 40 from by bv_omega,
    show (32 : Word) + 16 = 48 from by bv_omega,
    show (32 : Word) + 24 = 56 from by bv_omega,
    show (32 : Word) + 32 = 64 from by bv_omega,
    show (32 : Word) + 40 = 72 from by bv_omega,
    show (32 : Word) + 48 = 80 from by bv_omega,
    show (32 : Word) + 56 = 88 from by bv_omega,
    show (124 : Word) + 4 = 128 from by bv_omega] at hpre ⊢
  -- All atoms match between hpre and the goal
  xperm_hyp hpre

-- Placeholder: full `evm_addmod_stack_spec_within` lands in slice evm-asm-sord.
-- The N=0 case (dispatch-bridge proved above) is tracked in bead evm-asm-a32mz.

end EvmAsm.Evm64
