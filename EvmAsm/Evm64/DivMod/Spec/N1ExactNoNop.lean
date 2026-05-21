/-
  EvmAsm.Evm64.DivMod.Spec.N1ExactNoNop

  Exact-x1 no-NOP DIV n=1 stack wrapper split out from `Spec.Dispatcher`
  to keep the dispatcher file under the size cap.
-/

import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Exact-x1 no-NOP form of `evm_div_n1_stack_spec_within_word`. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 946 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  have hFull := evm_div_n1_noNop_full_unified_spec
    bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN1UnifiedPost_to_divStackDispatchPostNoX1
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

/-- No-NOP n=1 DIV stack spec weakened to the callable post surface with
    separate `x1` ownership and exact `x9`. -/
theorem evm_div_n1_stack_spec_within_word_noNop_callableOwnPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 946 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hp =>
      divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
        sp a b (signExtend12 4095 : Word) h hp)
    (evm_div_n1_stack_spec_within_word_exact_x1_noNop
      bltu_3 bltu_2 bltu_1 bltu_0 sp base
      a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z hshift_nz
      halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

theorem fullDivN1UnifiedPostNoX1_to_divConcretePostNoX1Frame
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
      raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1) :
    ∀ h,
      (fullDivN1UnifiedPostNoX1 bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 **
        (.x1 ↦ᵣ raVal)) h →
      let shift := fullDivN1Shift b0
      let antiShift := signExtend12 (0 : BitVec 12) - shift
      let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
      let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
      let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
      let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
      let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
      let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
      let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
      let v := fullDivN1NormV b0 b1 b2 b3
      let u := fullDivN1NormU a0 a1 a2 a3 b0
      let scratch_ret3 := if bltu_3 then (base + div128CallRetOff) else retMem
      let scratch_d3 := if bltu_3 then v.1 else dMem
      let scratch_dlo3 := if bltu_3 then div128DLo v.1 else dloMem
      let scratch_un03 := if bltu_3 then div128Un0 u.2.2.2.1 else scratch_un0
      let scratch_ret2 := if bltu_2 then (base + div128CallRetOff) else scratch_ret3
      let scratch_d2 := if bltu_2 then v.1 else scratch_d3
      let scratch_dlo2 := if bltu_2 then div128DLo v.1 else scratch_dlo3
      let scratch_un02 := if bltu_2 then div128Un0 u.2.2.1 else scratch_un03
      let scratch_ret1 := if bltu_1 then (base + div128CallRetOff) else scratch_ret2
      let scratch_d1 := if bltu_1 then v.1 else scratch_d2
      let scratch_dlo1 := if bltu_1 then div128DLo v.1 else scratch_dlo2
      let scratch_un01 := if bltu_1 then div128Un0 u.2.1 else scratch_un02
      divConcretePostNoX1Frame sp a b (signExtend12 4095) raVal antiShift
        r1.1 r2.1 r0.1
        r0.1 r1.1 r2.1 r3.1 u0' u1' u2' u3'
        r0.2.2.2.2.2 r1.2.2.2.2.2 r2.2.2.2.2.2 r3.2.2.2.2.2
        shift 1 0
        (if bltu_0 then (base + div128CallRetOff) else scratch_ret1)
        (if bltu_0 then v.1 else scratch_d1)
        (if bltu_0 then div128DLo v.1 else scratch_dlo1)
        (if bltu_0 then div128Un0 u.1 else scratch_un01) h := by
  intro h hq
  dsimp
  let shift := fullDivN1Shift b0
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  delta fullDivN1UnifiedPostNoX1 fullDivN1DenormPost fullDivN1FrameNoX1
    fullDivN1ScratchNoX1 at hq
  simp only [denormDivPost_unfold] at hq
  rw [divConcretePostNoX1Frame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ r0.1) ** ((sp + 40) ↦ₘ r1.1) **
       ((sp + 48) ↦ₘ r2.1) ** ((sp + 56) ↦ₘ r3.1))
      from by
        subst r0
        subst r1
        subst r2
        subst r3
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [word_add_zero] at hq
  let outExact : Assertion :=
    ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x10 ↦ᵣ r3.1) **
      (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32 ↦ₘ r0.1) ** (sp + 40 ↦ₘ r1.1) **
       (sp + 48 ↦ₘ r2.1) ** (sp + 56 ↦ₘ r3.1)))
  let outOwned : Assertion :=
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) **
      ((sp + 32 ↦ₘ r0.1) ** (sp + 40 ↦ₘ r1.1) **
       (sp + 48 ↦ₘ r2.1) ** (sp + 56 ↦ₘ r3.1)))
  let frame : Assertion :=
    ((.x9 ↦ᵣ (signExtend12 4095 : Word)) ** (.x1 ↦ᵣ raVal) **
      (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - fullDivN1Shift b0)) **
      (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ r2.1) **
      (.x11 ↦ᵣ r0.1) **
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
      ((sp + signExtend12 4088 ↦ₘ r0.1) **
       (sp + signExtend12 4080 ↦ₘ r1.1) **
       (sp + signExtend12 4072 ↦ₘ r2.1) **
       (sp + signExtend12 4064 ↦ₘ r3.1) **
       (sp + signExtend12 4056 ↦ₘ
          (r0.2.1 >>> (shift.toNat % 64)) |||
          (r0.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) **
       (sp + signExtend12 4048 ↦ₘ
          (r0.2.2.1 >>> (shift.toNat % 64)) |||
          (r0.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) **
       (sp + signExtend12 4040 ↦ₘ
          (r0.2.2.2.1 >>> (shift.toNat % 64)) |||
          (r0.2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) **
       (sp + signExtend12 4032 ↦ₘ
          (r0.2.2.2.2.1 >>> (shift.toNat % 64))) **
       (sp + signExtend12 4024 ↦ₘ r0.2.2.2.2.2) **
       (sp + signExtend12 4016 ↦ₘ r1.2.2.2.2.2) **
       (sp + signExtend12 4008 ↦ₘ r2.2.2.2.2.2) **
       (sp + signExtend12 4000 ↦ₘ r3.2.2.2.2.2) **
       (sp + signExtend12 3992 ↦ₘ shift) **
       (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word))) **
      (sp + signExtend12 3968 ↦ₘ
        (if bltu_0 then (base + div128CallRetOff) else
          if bltu_1 then (base + div128CallRetOff) else
          if bltu_2 then (base + div128CallRetOff) else
          if bltu_3 then (base + div128CallRetOff) else retMem)) **
      (sp + signExtend12 3960 ↦ₘ
        (if bltu_0 then (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_1 then (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_2 then (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_3 then (fullDivN1NormV b0 b1 b2 b3).1 else dMem)) **
      (sp + signExtend12 3952 ↦ₘ
        (if bltu_0 then div128DLo (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_1 then div128DLo (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_2 then div128DLo (fullDivN1NormV b0 b1 b2 b3).1 else
          if bltu_3 then div128DLo (fullDivN1NormV b0 b1 b2 b3).1 else dloMem)) **
      (sp + signExtend12 3944 ↦ₘ
        (if bltu_0 then div128Un0 (fullDivN1NormU a0 a1 a2 a3 b0).1 else
          if bltu_1 then div128Un0 (fullDivN1NormU a0 a1 a2 a3 b0).2.1 else
          if bltu_2 then div128Un0 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 else
          if bltu_3 then div128Un0 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 else scratch_un0)))
  change (outOwned ** frame) h
  have hExact : (outExact ** frame) h := by
    dsimp [outExact, frame]
    dsimp [r0, r1, r2, r3, shift, antiShift] at hq
    xperm_hyp hq
  refine sepConj_mono_left (fun hLeft hpLeft => ?_) h hExact
  · dsimp [outExact, outOwned] at hpLeft ⊢
    apply sepConj_mono_right
    apply sepConj_mono (regIs_implies_regOwn .x5 (v := r0.1))
    apply sepConj_mono (regIs_implies_regOwn .x10 (v := r3.1))
    exact fun _ hp => hp
    exact hpLeft

/-- Recombine the split no-`x1` full-path post with separate `x1` ownership. -/
theorem fullDivN1UnifiedPostNoX1_frame_to_fullDivN1UnifiedPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    ∀ h,
      (fullDivN1UnifiedPostNoX1 bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 **
        regOwn .x1) h →
      fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h := by
  intro h hq
  delta fullDivN1UnifiedPost fullDivN1Frame fullDivN1Scratch
    fullDivN1UnifiedPostNoX1 fullDivN1FrameNoX1 fullDivN1ScratchNoX1 at hq ⊢
  xperm_hyp hq

/-- No-NOP n=1 DIV stack spec with the callable precondition shape. The
    precondition keeps caller-framed `x1`/`x9` exact; the current full-path
    proof preserves `x1` ownership, so the postcondition exposes the split
    `fullDivN1UnifiedPostNoX1 ** regOwn .x1` surface. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_fullPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))) :
    cpsTripleWithin 946 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN1UnifiedPostNoX1 bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 ** regOwn .x1) := by
  have hFull := evm_div_n1_noNop_full_unified_spec_noX1_post
    bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [divModStackDispatchPreNoX1_unfold] at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      have hpOwn :
          ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) **
            regOwn .x1 ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
            (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
            (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
            ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
             ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) **
            (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
             ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) **
            (((sp + signExtend12 4088) ↦ₘ q0) **
             ((sp + signExtend12 4080) ↦ₘ q1) **
             ((sp + signExtend12 4072) ↦ₘ q2) **
             ((sp + signExtend12 4064) ↦ₘ q3) **
             ((sp + signExtend12 4056) ↦ₘ u0Old) **
             ((sp + signExtend12 4048) ↦ₘ u1Old) **
             ((sp + signExtend12 4040) ↦ₘ u2Old) **
             ((sp + signExtend12 4032) ↦ₘ u3Old) **
             ((sp + signExtend12 4024) ↦ₘ u4Old) **
             ((sp + signExtend12 4016) ↦ₘ u5) **
             ((sp + signExtend12 4008) ↦ₘ u6) **
             ((sp + signExtend12 4000) ↦ₘ u7) **
             ((sp + signExtend12 3992) ↦ₘ shiftMem) **
             ((sp + signExtend12 3984) ↦ₘ nMem) **
             ((sp + signExtend12 3976) ↦ₘ jMem)) **
            ((sp + signExtend12 3968) ↦ₘ retMem) **
            ((sp + signExtend12 3960) ↦ₘ dMem) **
            ((sp + signExtend12 3952) ↦ₘ dloMem) **
            ((sp + signExtend12 3944) ↦ₘ scratch_un0)) h := by
        apply sepConj_mono_right
        apply sepConj_mono_right
        apply sepConj_mono (regIs_implies_regOwn .x1 (v := raVal))
        exact fun _ hp => hp
        exact hp
      xperm_hyp hpOwn)
    (fun _ hq => hq)
    hFull

/-- No-NOP n=1 DIV stack spec from the callable precondition shape to the
    public callable post, with separate `x1` ownership and exact `x9`. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 946 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hp =>
      divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
        sp a b (signExtend12 4095 : Word) h
        (fullDivN1UnifiedPost_to_divStackDispatchPostNoX1
          bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
          a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
          ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h
          (fullDivN1UnifiedPostNoX1_frame_to_fullDivN1UnifiedPost
            bltu_3 bltu_2 bltu_1 bltu_0 sp base
            a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h hp)))
    (evm_div_n1_stack_spec_within_word_noNop_preNoX1_fullPost
      bltu_3 bltu_2 bltu_1 bltu_0 sp base
      a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z hshift_nz
      halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2)

end EvmAsm.Evm64
