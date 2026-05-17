/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterExitBridge

  Exit bridge theorems: from the final-iteration exit post-condition
  (`expTwoMulIterExitPost 0 ...`) plus an "exponent frame" atom
  (`evmWordIs (evmSp + signExtend12 (-32)) exponentWord`), prove
  `expTwoMulLoopExitFullStackPreFrame` with `rest = []`.

  Key insight: the original exponent word at `evmSp_orig + 32` (= LP64_base - 32)
  is NEVER written by the loop iterations (which use LP64_base + 0..56 as scratch).
  Carrying it as a sep-conj frame atom allows closing the gap between the abstract
  loop postcondition and the FullStackPreFrame required by the epilogue theorem.

  Bead: evm-asm-w5mk.1.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Exit bridge for the COND path (bit ≠ 0, result = rwW).

    Given `expTwoMulIterCondPost 0 bit sp evmSp base a0..a3 rwW (0=0)` and
    the exponent frame `evmWordIs (evmSp + signExtend12 (-32)) exponentWord`,
    prove `expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0 ...` with `rest = []`. -/
theorem expTwoMulIterCondExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterCondPost 0 bit sp evmSp base a0 a1 a2 a3 rwW (0 = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
      (rwW.getLimbN 3)
      (rwW.getLimbN 0) (rwW.getLimbN 1) (rwW.getLimbN 2) (rwW.getLimbN 3)
      (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
      (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
      (expResultWord a0 a1 a2 a3) [] (0 = 0) ps := by
  sorry

/-- Exit bridge for the SKIP path (bit = 0, result = squarW).

    Given `expTwoMulIterSkipPost 0 bit sp evmSp base a0..a3 squarW (0=0)` and
    the exponent frame `evmWordIs (evmSp + signExtend12 (-32)) exponentWord`,
    prove `expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0 ...` with `rest = []`. -/
theorem expTwoMulIterSkipExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterSkipPost 0 bit sp evmSp base a0 a1 a2 a3 squarW (0 = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
      (squarW.getLimbN 3)
      (squarW.getLimbN 0) (squarW.getLimbN 1) (squarW.getLimbN 2) (squarW.getLimbN 3)
      (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
      (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
      (expResultWord a0 a1 a2 a3) [] (0 = 0) ps := by
  sorry

/-- Combined exit bridge: from `expTwoMulIterExitPost 0 ...` (either cond or skip)
    and the exponent frame `evmWordIs (evmSp + signExtend12 (-32)) exponentWord`,
    prove `∃ tOld r0..r3, expTwoMulLoopExitFullStackPreFrame ...` with `rest = []`.

    This is the `hExitUniv` ingredient for `exp_loop_from_looppost_induction_general`.

    The d0..d3 output values are the four limbs of the original exponent word.
    The baseWord output is `expResultWord a0 a1 a2 a3` (the EXP base operand). -/
theorem expTwoMulIterExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterExitPost 0 bit sp evmSp base a0 a1 a2 a3 squarW rwW **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ tOld r0 r1 r2 r3,
      expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0 tOld r0 r1 r2 r3
        (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
        (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
        (expResultWord a0 a1 a2 a3) [] (0 = 0) ps := by
  obtain ⟨ps1, ps2, hd12, hu12, h1, h_frame⟩ := h
  -- expTwoMulIterExitPost 0 ... ps1 = (CondPost 0 ... ps1 ∨ SkipPost 0 ... ps1)
  have h1_or : expTwoMulIterCondPost 0 bit sp evmSp base a0 a1 a2 a3 rwW (0 = 0) ps1 ∨
               expTwoMulIterSkipPost 0 bit sp evmSp base a0 a1 a2 a3 squarW (0 = 0) ps1 := by
    delta expTwoMulIterExitPost at h1
    rcases h1 with hcond | hskip
    · left; convert hcond using 2; decide
    · right; convert hskip using 2; decide
  rcases h1_or with hcond | hskip
  · exact ⟨rwW.getLimbN 3, rwW.getLimbN 0, rwW.getLimbN 1, rwW.getLimbN 2, rwW.getLimbN 3,
      expTwoMulIterCondExitPost_to_FullStackPreFrame
        ⟨ps1, ps2, hd12, hu12, hcond, h_frame⟩⟩
  · exact ⟨squarW.getLimbN 3, squarW.getLimbN 0, squarW.getLimbN 1, squarW.getLimbN 2, squarW.getLimbN 3,
      expTwoMulIterSkipExitPost_to_FullStackPreFrame
        ⟨ps1, ps2, hd12, hu12, hskip, h_frame⟩⟩

end EvmAsm.Evm64.Exp.Compose
