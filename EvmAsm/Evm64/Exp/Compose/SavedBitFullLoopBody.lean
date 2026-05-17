/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopBody

  Full-loop body composition for the 256-iteration EXP loop.

  The loop always runs exactly 256 iterations (one per bit of the exponent),
  counting down from `iterCount = 256` to 0. Each iteration:
    - Reads the current MSB of the saved exponent register `e`
    - Squares the accumulator `r`
    - If the bit is 1, also multiplies by the base `a`
    - Decrements `iterCount`

  The semantic invariant after k iterations:
    expResultWord r0..r3 = EvmWord.exp base (top k bits of exponent)
  This holds at k=0 (r = 1 = base^0) and is maintained by each iteration.
  After 256 iterations, r = EvmWord.exp base exponent.

  Architecture:
  - `expFullLoopBodyNSpec`: structural peel wrapper (sorry-free)
  - `expTwoMulLoopBodyCorrect`: named sorry for the 256-iteration invariant
  - `expFullLoopBodySpec`: full boundary spec, proved using the above

  The single `sorry` in `expTwoMulLoopBodyCorrect` encapsulates the
  MSB-first square-and-multiply algorithm correctness:
    ∀ baseWord exponentWord, the 256-iteration loop starting from r=1
    produces r = EvmWord.exp baseWord exponentWord.
  This is a semantic proof obligation separate from the structural
  composition (which is `expFullLoopBodySpec`).

  Note: `expResultWord r.getLimbN 0..3 = r` holds by
  `expResultWord_getLimbN_self`, so the exitCond in expFullLoopBodySpec
  is a tautology — the loop needs only to produce the correct r values.

  Refs: GH #92, parent evm-asm-20z6, bead evm-asm-w5mk.
  Authored by @pirapira; implemented by Claude Code.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry
import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond
import EvmAsm.Evm64.EvmWordArith.Exp
import EvmAsm.Evm64.Exp.LimbSpec

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64 (Assertion CodeReq
  cpsTripleWithin cpsTripleWithin_extend_code cpsTripleWithin_weaken
  cpsTripleWithin_seq_same_cr cpsTripleWithin_mono_nSteps
  memOwn regOwn signExtend12 signExtend21)

-- ============================================================================
-- Structural peeling lemma for one iteration
-- ============================================================================

/-- Peel one iteration from an `(n+1)`-iteration body spec.  A thin wrapper
    around `exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within`
    exposing the canonical shape used in `expFullLoopBodySpec`. -/
theorem expFullLoopBodyNSpec
    (n : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin (n * 189) (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond)) :
    cpsTripleWithin ((n + 1) * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) :=
  exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within
    n e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
    base baseWord rest exitCond hbase hCondExit hSkipExit hTail

-- ============================================================================
-- Key semantic correctness lemma (sorry)
-- ============================================================================

/-- The 256-iteration MSB-first square-and-multiply loop body is correct:
    starting from `expTwoMulLoopEntryPost` (r = 1, iterCount = 256),
    the loop terminates with `expTwoMulLoopExitPre` (r = base^exp, iterCount = 0).

    This is the ONLY sorry in `expFullLoopBodySpec`. Its proof requires:
    1. An invariant: after k iterations, r = baseWord^(exponentWord >> (256-k)).
    2. 256 applications of `expFullLoopBodyNSpec` threading this invariant.
    3. Connection: the MSB-first bit processing of `exponentWord` gives base^exp.

    The invariant proof is the core of the EXP algorithm correctness.
    Steps 1-2 are purely structural (RISC-V operational).
    Step 3 is mathematical (binary square-and-multiply is correct).

    Note: `tOld` is the x5 value at loop exit (determined by the loop).
    `expResultWord_getLimbN_self` ensures exitCond is trivially True. -/
theorem expTwoMulLoopBodyCorrect
    (sp evmSp vOld tOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0) :
    let result := EvmWord.exp baseWord exponentWord
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPre sp evmSp 0 tOld
        (result.getLimbN 0) (result.getLimbN 1) (result.getLimbN 2) (result.getLimbN 3)
        baseWord rest
        (expResultWord (result.getLimbN 0) (result.getLimbN 1)
          (result.getLimbN 2) (result.getLimbN 3) = result)) := by
  intro result
  -- exitCond = expResultWord result.getLimbN 0..3 = result = True (by getLimbN_self)
  -- The loop maintains r = base^(top k bits of exp) after k iterations.
  -- After 256 iterations: r = base^exp, stored in scratch at sp+0..sp+24.
  sorry

-- ============================================================================
-- Full 256-iteration boundary spec
-- ============================================================================

/-- The full 256-iteration EXP boundary spec (bead evm-asm-w5mk, GH #92).

    Reduces to `expTwoMulLoopBodyCorrect` (the semantic loop correctness)
    via `exp_two_mul_full_loop_boundary_of_bounded_body_spec_within`.

    Key facts used:
    - `expResultWord_getLimbN_self`: exitCond is a tautology.
    - The boundary framework wraps prologue/epilogue around hLoop. -/
theorem expFullLoopBodySpec
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0) :
    let result := EvmWord.exp baseWord exponentWord
    let r0 := result.getLimbN 0
    let r1 := result.getLimbN 1
    let r2 := result.getLimbN 2
    let r3 := result.getLimbN 3
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp 0 r0 r1 r2 r3
        baseWord rest (expResultWord r0 r1 r2 r3 = result)) := by
  intro result
  -- Use expTwoMulLoopBodyCorrect with tOld = tOld (outer parameter)
  -- to get hLoop with matching tOld in BoundaryPre and LoopExitPre.
  have hLoop := expTwoMulLoopBodyCorrect sp evmSp vOld tOld v18
    baseWord exponentWord rest base hbase
  -- Apply the boundary wrapper
  exact exp_two_mul_full_loop_boundary_of_bounded_body_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 0
    (result.getLimbN 0) (result.getLimbN 1)
    (result.getLimbN 2) (result.getLimbN 3)
    baseWord exponentWord rest
    (expResultWord (result.getLimbN 0) (result.getLimbN 1)
       (result.getLimbN 2) (result.getLimbN 3) = result)
    base (le_refl _) hLoop

end EvmAsm.Evm64.Exp.Compose
