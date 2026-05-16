import EvmAsm.Evm64.EvmWordArith.Div
import EvmAsm.Evm64.SDiv.Compose.BzeroFrames
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SDiv.Compose.Words
import EvmAsm.Evm64.SDiv.Compose.DispatchViews

namespace EvmAsm.Evm64.SDiv.Compose

@[irreducible]
def saveRaDivCallCallableReturnPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  (.x18 ↦ᵣ vRa) **
  (resultSignFixPost (sp + 32) resultSign
    (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
    (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
   saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)

theorem saveRaDivCallCallableReturnPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (.x18 ↦ᵣ vRa) **
       (resultSignFixPost (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnPost
  rfl

theorem saveRaDivCallCallableReturnPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallCallableReturnPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallCallableReturnPost_unfold]
  dsimp
  rw [resultSignFixPost_unfold, saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallCallableReturnPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallCallableReturnPost_pcFree⟩

/-- Callable-return postcondition after SDIV result-sign fixup, with the
    produced result slot folded as a named sign-fixed quotient word. -/
@[irreducible]
def saveRaDivCallCallableReturnSignFixedWordPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultWord :=
    sdivSignFixedWord resultSign
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
  let mask := (0 : Word) - resultSign
  let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x18 ↦ᵣ vRa) **
  (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    evmWordIs (sp + 32) resultWord) **
   saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)

theorem saveRaDivCallCallableReturnSignFixedWordPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultWord :=
         sdivSignFixedWord resultSign
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmWordIs (sp + 32) resultWord) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  delta saveRaDivCallCallableReturnSignFixedWordPost
  rfl

theorem saveRaDivCallCallableReturnSignFixedWordPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    (saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).pcFree := by
  rw [saveRaDivCallCallableReturnSignFixedWordPost_unfold]
  dsimp
  rw [saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallCallableReturnSignFixedWordPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  ⟨saveRaDivCallCallableReturnSignFixedWordPost_pcFree⟩

/-- Exact-callable return postcondition view with the result slot folded as the
    named sign-fixed SDIV word. -/
theorem saveRaDivCallCallableReturnPost_evmWordIs
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    saveRaDivCallCallableReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      saveRaDivCallCallableReturnSignFixedWordPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop := by
  rw [saveRaDivCallCallableReturnPost_unfold,
    saveRaDivCallCallableReturnSignFixedWordPost_unfold]
  dsimp only
  rw [resultSignFixPost_evmWordIs]

end EvmAsm.Evm64.SDiv.Compose
