/-
  EvmAsm.Evm64.SDiv.Compose.DivCallDispatch

  Defines the post-shape directly consumed by
  `evm_div_callable_spec_in_sdivCode`: the `divModStackDispatchPre` bundle
  (the dispatcher's pre, which the callable consumes) paired with the
  SDIV-wrapper-private sign frame (`.x8 = resultSign`, `.x9 = divisorSign`,
  `.x18 = vRa + signExtend12 0`). Infrastructure-only — the proof that
  `saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode`'s
  post equals this shape is a separate sub-slice (evm-asm-2long).

  Slice 4 micro evm-asm-mnva9. Authored by @pirapira; implemented by
  Hermes-bot (claude-c1).
-/

import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.Bridges

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Absolute-value word produced by the SDIV dividend sign/absolute-value
    prefix, packaged as a named expression so downstream callable-composition
    proofs do not duplicate the expanded `fromLimbs` term. -/
def sdivAbsDividendWord
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) : EvmWord :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let dividendMask := (0 : Word) - dividendSign
  let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
  let dividendCarry0 :=
    if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
  let dividendCarry1 :=
    if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
  let dividendCarry2 :=
    if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => dividendSum0 | 1 => dividendSum1 | 2 => dividendSum2 | 3 => dividendSum3

/-- Absolute-value word produced by the SDIV divisor sign/absolute-value
    prefix, paired with `sdivAbsDividendWord` for downstream composition
    statements that consume `divModStackDispatchPre`. -/
def sdivAbsDivisorWord
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmWord :=
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => divisorSum0 | 1 => divisorSum1 | 2 => divisorSum2 | 3 => divisorSum3

/-- Post-shape consumed by `evm_div_callable_spec_in_sdivCode`: the
    `divModStackDispatchPre` bundle (the dispatcher's pre, which the
    callable consumes) paired with the SDIV-wrapper-private sign frame
    (`.x8 = resultSign`, `.x9 = divisorSign`, `.x18 = vRa + signExtend12 0`).
    The ~30-line let-chain (signs / masks / sums / carries / fromLimbs)
    is hidden inside this `@[irreducible]` def so callers see a flat
    assertion. -/
@[irreducible]
def saveRaDivCallDispatchReadyPost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) : Assertion :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let dividendAbsWord : EvmWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  EvmAsm.Evm64.divModStackDispatchPre sp dividendAbsWord divisorAbsWord
      ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
    ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
     (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))))

theorem saveRaDivCallDispatchReadyPost_unfold
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    {v2 v5 v6 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 =
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultSign := dividendSign ^^^ divisorSign
       let divisorMask := (0 : Word) - divisorSign
       let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       let dividendAbsWord : EvmWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       EvmAsm.Evm64.divModStackDispatchPre sp dividendAbsWord divisorAbsWord
           ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
           q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))))) := by
  delta saveRaDivCallDispatchReadyPost; rfl

/-- Prefix through the SDIV `divCall`, weakened to the exact dispatch-ready
    postcondition consumed by `evm_div_callable_spec_in_sdivCode`. -/
theorem saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    cpsTripleWithin 49 base
      ((base + divCallOff) + signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    rw [saveRaSignsAbsSignXorThenDivCallPost_unfold] at hq
    rw [saveRaDivCallDispatchReadyPost_unfold]
    dsimp only at hq ⊢
    rw [divModStackDispatchPre_unfold_explicit_sdiv]
    simp [sdivAbsDividendWord, sdivAbsDivisorWord, EvmWord.getLimbN,
      EvmWord.getLimb_fromLimbs] at hq ⊢
    xperm_hyp hq) hPrefix

end EvmAsm.Evm64.SDiv.Compose
