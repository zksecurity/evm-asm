/-
  EvmAsm.Evm64.SDiv.Compose.BzeroCallablePost

  Named postcondition and unfold views for the SDIV zero-divisor div-call
  path after the unsigned DIV callable returns.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.SDiv.Compose.BaseOffsets
import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SDiv.Compose

/-- Named postcondition after the SDIV prefix has called the unsigned DIV
    callable along the zero-divisor branch. This keeps the sign frame and the
    concrete return address bundled for the following result-sign-fix step. -/
@[irreducible]
def saveRaDivCallBzeroCallablePost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp
      (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
    (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
   ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
    (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))

theorem saveRaDivCallBzeroCallablePost_unfold
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp
           (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
           (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
         (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
        ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))) := by
  delta saveRaDivCallBzeroCallablePost
  rfl

/-- Zero-divisor view of `saveRaDivCallBzeroCallablePost`: the unsigned DIV
    callable's quotient word in the EVM stack result slot is concretely zero. -/
theorem saveRaDivCallBzeroCallablePost_unfold_zero_quotient
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (((.x12 ↦ᵣ (sp + 32)) ** EvmAsm.Rv64.regOwn .x2 **
         EvmAsm.Rv64.regOwn .x5 ** EvmAsm.Rv64.regOwn .x6 ** EvmAsm.Rv64.regOwn .x7 **
         EvmAsm.Rv64.regOwn .x10 ** EvmAsm.Rv64.regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
         evmWordIs sp dividendAbsWord ** evmWordIs (sp + 32) (0 : EvmWord) **
         EvmAsm.Evm64.divScratchOwnCall sp) **
        (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
       ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  rw [saveRaDivCallBzeroCallablePost_unfold,
    EvmAsm.Evm64.divStackDispatchPostNoX1_unfold]
  dsimp only
  rw [hbz, EvmWord.div_zero_right]

end EvmAsm.Evm64.SDiv.Compose
