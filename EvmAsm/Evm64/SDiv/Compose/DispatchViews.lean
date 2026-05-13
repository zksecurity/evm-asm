/-
  EvmAsm.Evm64.SDiv.Compose.DispatchViews

  Stack/result-sign view lemmas used by the SDIV div-call dispatch
  composition.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Entry assertion view for stack-level SDIV callers: when the raw limb
    parameters are instantiated from two EVM words, the operand memory atoms
    in `saveRaSignsAbsSignXorThenDivCallPre` fold into a two-word stack. -/
theorem saveRaSignsAbsSignXorThenDivCallPre_stack_pair
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord) :
    saveRaSignsAbsSignXorThenDivCallPre
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       evmStackIs sp [dividend, divisor]) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_unfold, evmStackIs_pair]
  rw [evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56]
  rw [show (sp + 0 : Word) = sp by bv_decide]
  xperm

/-- Tail-stack companion to `saveRaSignsAbsSignXorThenDivCallPre_stack_pair`:
    folds the two SDIV operands together with the untouched stack tail. -/
theorem saveRaSignsAbsSignXorThenDivCallPre_stack_pair_rest
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (saveRaSignsAbsSignXorThenDivCallPre
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
      evmStackIs (sp + 64) rest) =
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       evmStackIs sp (dividend :: divisor :: rest)) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_stack_pair]
  have h_stack :
      evmStackIs sp (dividend :: divisor :: rest) =
        (evmStackIs sp [dividend, divisor] ** evmStackIs (sp + 64) rest) := by
    change evmStackIs sp ([dividend, divisor] ++ rest) =
      (evmStackIs sp [dividend, divisor] ** evmStackIs (sp + 64) rest)
    rw [evmStackIs_append sp [dividend, divisor] rest]
    rfl
  rw [h_stack]
  rw [sepConj_assoc']

/-- Postcondition view for the SDIV zero-divisor branch after result-sign
    fixup: conditional negation of the zero quotient is still the zero EVM
    word, with the sign-fix scratch registers exposed explicitly. -/
theorem resultSignFixPost_sdivResultSign_zero_word
    (sp dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    resultSignFixPost sp resultSign 0 0 0 0 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ resultSign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
       evmWordIs sp (0 : EvmWord)) := by
  dsimp only
  obtain h_sign | h_sign := sdivResultSign_bool dividendTop divisorTop
  · rw [h_sign]
    rw [resultSignFixPost_unfold, evmWordIs_zero]
    dsimp only
    simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24]
    simp
  · rw [h_sign]
    rw [resultSignFixPost_unfold, evmWordIs_zero]
    dsimp only
    simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24]
    simp

end EvmAsm.Evm64.SDiv.Compose
