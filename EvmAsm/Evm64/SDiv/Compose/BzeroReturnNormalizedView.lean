/-
  EvmAsm.Evm64.SDiv.Compose.BzeroReturnNormalizedView

  Normalized return-target view of the SDIV zero-divisor path.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroReturn
import EvmAsm.Evm64.SDiv.Compose.DispatchViews

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- Normalized return-target view of the SDIV zero-divisor path. This hides
    the two `signExtend12 0` artifacts introduced by the saved-RA move and
    the final `JALR`, leaving downstream callers with the ordinary masked
    saved return address. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_normalized_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCode base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ vRa) **
       (resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  have hExit :
      (((vRa + signExtend12 (0 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [signExtend12_0]
    bv_decide
  rw [← hExit]
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      simp only [signExtend12_0] at hp ⊢
      have hRa : (vRa + (0 : Word)) = vRa := by bv_decide
      rw [hRa] at hp
      exact hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_spec_in_sdivCode
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

end EvmAsm.Evm64.SDiv.Compose
