/-
  EvmAsm.Evm64.DivMod.Spec.CallAddback

  Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0).
  Split from the call-skip stack-spec surface to isolate the addback branch.

  Contents:
  - `n4CallAddbackBeqSemanticHolds` predicate.
  - n=4 call+addback BEQ DIV/MOD stack specs.
  - Sub-stub: qHat = a/b + 1 (single-addback) and qHat ≥ 2 (double-addback).
  - Pure-Nat algebra (post1_val_eq_amod_pow_s_pure_nat,
    abPrime_val_eq_amod_pow_s_pure_nat, qHat_ge_two_abstract).
  - Irreducible bundles for the algorithm's intermediate Word/Nat values
    (algCallAddbackBeqCarry, algCallAddbackBeqMsC3, algCallAddbackBeqU4,
    algCallAddbackBeqMsLowVal, algCallAddbackBeqPost1Val,
    algCallAddbackBeqPost1Limb{0..3}, algCallAddbackBeqUn{0..3}Out,
    algCallAddbackBeqAbPrimeLimb{0..3}, algCallAddbackBeqAbPrimeVal).
  - Word-level wrappers (post1_val_eq_amod_pow_s_of_single_addback,
    abPrime_val_eq_amod_pow_s_of_double_addback).
  - Adapter / parent + final stack specs.

  The trailing leaf cluster (qHat = a/b + k sub-stubs and the
  algCallAddbackBeq_* Word-level Euclideans / val256 bounds) lives in
  `Spec/CallAddbackSubStubs.lean` (#1078 sub-slice).
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Spec.CallAddbackPureNat
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgEuclideans
import EvmAsm.Evm64.DivMod.Shift0Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Call+addback BEQ semantic predicates and stack specs (n=4, shift ≠ 0)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+addback-BEQ sub-path:
    the final `q_out` (= `qHat - 1` single-addback or `qHat - 2` double-addback)
    equals `⌊val256(a)/val256(b)⌋`.

    Unlike `n4CallSkipSemanticHolds` which states a lower-bound on the raw
    `div128Quot`, this predicate directly states that the post-addback
    corrected quotient is the true quotient. Proving it from first
    principles requires the Knuth TAOCP Theorem B overestimate bound
    (`q̂ ≤ q_true + 2`) plus the algorithm's addback-correction semantics,
    which combine to ensure q_out is exactly correct. Deferred to a future
    task; the stack spec delegates the proof to callers.

    **🚨 STATUS (2026-04-27, updated): real correctness bug in algorithm**.

    Verified via `lean_run_code`: with
    `a3 = 2^63 + 2^33, a2 = a1 = a0 = 0, b3 = 1, b2 = 2^33 - 1,
    b1 = b0 = 0`, the input satisfies ALL runtime preconditions for
    the call-addback-BEQ branch (hbnz, hb3nz, hshift_nz, hbltu,
    hborrow, hcarry2_nz), but the algorithm computes
    `q_out = qHat - 1 = 2^63 + 2^33 - 4 = 9223372045444710396` while
    `q_true = val256(a) / val256(b) = 2^63 + 2^32 - 2 = 9223372041149743102`.
    The discrepancy is `2^32 - 2` ≈ 4.3 × 10⁹.

    **Root cause**: our `div128Quot` does only 1 Phase 1b correction
    (vs Knuth classical 2-correction loop), so qHat can overshoot at
    val256 level by up to ~2^33. The actual RISC-V program at
    `Program.lean:386` has an addback LOOP (`BEQ x7 x0` jumps back if
    x7 = 0), but the loop-exit heuristic "limb-3 carry of addback ≠ 0"
    fires after 1 addback in this case — leaving q_out = qHat - 1,
    still ~2^32 too large.

    **Implication**: the algorithm is genuinely buggy on this input
    class. The `n4CallAddbackBeqSemanticHolds` predicate is provably
    FALSE on runtime-reachable inputs. Closure
    (`n4CallAddbackBeqSemanticHolds_of_*`) cannot be proven; the
    user-facing `evm_div_n4_full_call_addback_beq_stack_pre_spec` and
    its relatives are vacuous on this input class.

    See `memory/project_n4callbeq_addback_overshoot_2pow32.md` and
    `memory/project_knuth_d_one_correction_design.md` for the full
    analysis.

    **Remediation options**:
    1. Modify `div128Quot` to do 2 Phase 1b corrections (matching Knuth
       classical D3 loop). Restores Knuth Theorem B's per-digit ≤ 2
       overshoot bound. Requires changing both Lean abstraction and
       RISC-V code.
    2. Modify the addback loop's exit condition to detect 2^32-scale
       overshoots (e.g., bound iteration count by some explicit limit
       and re-check). Non-trivial.
    3. Document the input class as out-of-scope and gate it externally.
       Pragmatically blocks complete EVM-level verification.

    Mirror of `n4CallSkipSemanticHolds` for the call+addback branch. -/
def n4CallAddbackBeqSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

-- The v1 counterexample, v2 fix-verification, v2-buggy-confirmation and
-- the v2 mirror predicate `n4CallAddbackBeqSemanticHolds_v2` (plus its
-- sanity check on the v1 counterexample input) live in
-- `EvmAsm/Evm64/DivMod/Spec/CallAddbackCounterexamples.lean` (extracted
-- 2026 toward the #1078 file-size cap; see beads evm-asm-b5i).




theorem n4CallAddbackBeqSemanticHolds_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **Call+addback BEQ n=4 div getLimbN bridge.** Under the runtime conditions
    + `n4CallAddbackBeqSemanticHolds`, the post-addback corrected quotient
    `q_out` equals `(EvmWord.div a b).getLimbN 0`, and the upper three
    quotient limbs are zero.

    Simpler than the call-skip bridge: hsem directly gives the tight equality
    `q_out.toNat = val256(a)/val256(b)`, so we don't need to combine with T3.
    From that, `(EvmWord.div a b).toNat = q_out.toNat` via `BitVec.toNat_udiv`,
    and `q_out : Word` bounds pin the limbs.

    **VACUITY note (2026-04-27)**: per
    `n4CallAddbackBeqSemanticHolds_counterexample` (below), the `hsem`
    hypothesis is FALSE on a class of runtime-reachable inputs — the
    algorithm overshoots q_true by ~2^32 in those cases. So this bridge
    cannot be applied to derive correctness on the full input space;
    callers must restrict to inputs where `hsem` is independently
    discharged (currently impossible without algorithm fix). -/
theorem n4_call_addback_beq_div_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_out : Word :=
      if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
      else qHat + signExtend12 4095
    (EvmWord.div a b).getLimbN 0 = q_out ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  change q_out.toNat = val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem : q_out.toNat = a.toNat / b.toNat
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => q_out | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = q_out.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level DIV spec on the n=4 call+addback BEQ sub-path.**

    Mirror of `evm_div_n4_call_skip_stack_spec` for the addback BEQ branch.
    Consumes runtime conditions, shift-nonzero, alignment, validity, and
    the semantic-correctness fact `n4CallAddbackBeqSemanticHolds`. Output
    shape is `divN4CallSkipStackPost` (same as call-skip — both paths
    produce identical stack layouts on success). -/
theorem evm_div_n4_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_addback_beq_div_mod_getLimbN a b hbnz hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallAddbackBeqPost_unfold, denormDivPost_unfold] at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) = _
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
