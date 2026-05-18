/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts

  Named case postconditions for the fixed x19 merged EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expTwoMulFixedIterBaseFrame (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)

abbrev expTwoMulFixedIterPointerPost (ptr nextLimb : Word) : Assertion :=
  (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)

abbrev expTwoMulFixedIterSkipCondFrame (e c6 : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

abbrev expTwoMulFixedIterSkipRest
    (e c6 sp evmSp r0 r1 r2 r3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

abbrev expTwoMulFixedIterSkipCondRest
    (sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ rw.getLimbN 3) **
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
  evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 140) + 68))

abbrev expTwoMulFixedIterReloadCondFrame
    (e c6 ptr nextLimb : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x19 ↦ᵣ nextLimb) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
  ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

abbrev expTwoMulFixedIterReloadSkipRest
    (e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ nextLimb) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

abbrev expTwoMulFixedIterSkipCondCountPost
    (iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
      a0 a1 a2 a3 base) **
    expTwoMulFixedIterSkipCondFrame e c6

abbrev expTwoMulFixedIterSkipCountPost
    (iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipRest e c6 sp evmSp r0 r1 r2 r3 base) **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

abbrev expTwoMulFixedIterReloadCondCountPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) (exitCond : Prop) :
    Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
      a0 a1 a2 a3 base) **
    expTwoMulFixedIterReloadCondFrame e c6 ptr nextLimb

abbrev expTwoMulFixedIterReloadSkipCountPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) (exitCond : Prop) :
    Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 base) **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

abbrev expTwoMulFixedIterSkipLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  (fun ps =>
    expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps) **
  expTwoMulFixedIterPointerPost ptr nextLimb

abbrev expTwoMulFixedIterReloadLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps

abbrev expTwoMulFixedIterSkipExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  (fun ps =>
    expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps) **
  expTwoMulFixedIterPointerPost ptr nextLimb

abbrev expTwoMulFixedIterReloadExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps

abbrev expTwoMulFixedIterCaseLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps

abbrev expTwoMulFixedIterCaseExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps

end EvmAsm.Evm64.Exp.Compose
