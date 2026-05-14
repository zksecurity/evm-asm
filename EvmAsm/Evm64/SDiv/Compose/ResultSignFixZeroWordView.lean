/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView

  Zero-word result-sign-fix view used by the SDIV zero-divisor path.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

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
