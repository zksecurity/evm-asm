/-
  EvmAsm.Evm64.SDiv.Compose.DivCallViews

  Named pre/postcondition bundles for the SDIV wrapper prefix through the
  near call into `evm_div_callable`.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallPreView

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Postcondition for the SDIV save-ra/signs/dividendAbs/divisorAbs/signXor
    /divCall block: `x1` holds the post-JAL return PC (`base + divCallOff
    + 4`), `x8` holds the result sign, the rest matches the signXor
    postcondition. Wrapped `@[irreducible]` to hide the 23-atom sepConj
    from downstream proofs. -/
@[irreducible]
def saveRaSignsAbsSignXorThenDivCallPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Assertion :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  ((.x1 ↦ᵣ ((base + divCallOff) + 4)) **
   (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
    ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
     ((dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))))

theorem saveRaSignsAbsSignXorThenDivCallPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultSign := dividendSign ^^^ divisorSign
       let dividendMem0 := sp + signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let dividendMask := (0 : Word) - dividendSign
       let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
       let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
       let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
       let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
       let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
       let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
       let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
       let divisorMask := (0 : Word) - divisorSign
       let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       ((.x1 ↦ᵣ ((base + divCallOff) + 4)) **
        (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
         ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
          ((dividendMem0 ↦ₘ dividendSum0) **
           (dividendMem1 ↦ₘ dividendSum1) **
           (dividendMem2 ↦ₘ dividendSum2) **
           (dividendMem3 ↦ₘ dividendSum3) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
           (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
           (.x11 ↦ᵣ divisorCarry3) **
           (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
           (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))))) := by
  delta saveRaSignsAbsSignXorThenDivCallPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
