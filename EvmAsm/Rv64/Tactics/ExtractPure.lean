/-
  EvmAsm.Rv64.Tactics.ExtractPure

  STUB / DESIGN DOC for the `extract_pure` tactic.

  Tracking issue: GH #1432
  Beads parent:   evm-asm-lsv
  Beads slice 1:  evm-asm-bx7 (this file)
  Beads slice 2:  evm-asm-455 (implementation lands here)
  Beads slice 3:  evm-asm-8f5 (apply at call sites)

  This file currently contains NO tactic — slice 2 will replace the body
  below with the real implementation. Keeping a stub now lets us register
  the import path (`EvmAsm.Rv64.Tactics.ExtractPure`) and the design intent
  in-tree so that the slice-2 PR is purely additive on the API contract
  documented here.

  ─────────────────────────────────────────────────────────────────────────
  PROBLEM
  ─────────────────────────────────────────────────────────────────────────

  Several proofs end up with a hypothesis whose type is a deeply nested
  separating conjunction `A1 ** A2 ** ... ** An` where one or more of the
  `Ai` are pure assertions of the shape `⌜P⌝` (see `EvmAsm.Rv64.pure`).
  The only way to recover the underlying `P : Prop` is to peel through the
  resource-bearing tail with a chain of `obtain ⟨_, _, _, _, _, hrest⟩`
  destructures, one per `**` layer, until the pure cell is reached.

  Reference site (canonical):
    EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean line 109
    — six consecutive `obtain ⟨_, _, _, _, _, hpost⟩ := hpost` lines that
    only exist to navigate to a trailing `⌜P⌝`.

  ─────────────────────────────────────────────────────────────────────────
  CALL-SITE SURVEY (slice-1 deliverable)
  ─────────────────────────────────────────────────────────────────────────

  Found via `grep` for ≥3 consecutive `obtain ⟨` lines on a single hypothesis.
  Eleven chains total; the tactic should make all of these collapse to a
  single line.

    File                                                       Line  Depth
    ----                                                       ----  -----
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean             399   9
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean             439   9
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2.lean               455   8
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2.lean               499   8
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2v4.lean             918   7
    EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2v4.lean             807   6
    EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean                     109   6
    EvmAsm/Rv64/SyscallSpecs.lean                                47   4
    EvmAsm/Rv64/SepLogic.lean                                  1376   3
    EvmAsm/Rv64/RLP/Phase1.lean                                 173   3
    EvmAsm/Rv64/RLP/Phase1.lean                                 195   3

  Three sites picked as slice-3 acceptance targets (one short, one medium,
  one deep), spread across two top-level subtrees so we exercise both the
  `Rv64/RLP` and the `Evm64/DivMod` proof styles:

    1. EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean:109   (depth 6, canonical)
    2. EvmAsm/Rv64/RLP/Phase1.lean:173               (depth 3, smallest win)
    3. EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean:399 (depth 9, largest)

  ─────────────────────────────────────────────────────────────────────────
  DEFINITION OF "PURE"
  ─────────────────────────────────────────────────────────────────────────

  A sub-assertion is "pure" iff it is syntactically `EvmAsm.Rv64.pure P` (the
  `⌜P⌝` notation defined in `EvmAsm.Rv64.SepLogic`):

      def pure (P : Prop) : Assertion := fun h => h = PartialState.empty ∧ P

  We do NOT treat the following as "pure" for slice 2:
    - `empAssertion`           — carries no information; nothing to extract.
    - `Assertion.PCFree` instances — too broad; would cross resource bdry.
    - decidable Prop atoms living outside `⌜·⌝` — not addressable from the
      sepConj structure alone.

  Future extension (out of scope for slice 2): allow user-provided
  pure-detectors via a `register_simp_attr` style attribute. Not needed for
  the 11 known call sites, all of which use literal `⌜P⌝`.

  ─────────────────────────────────────────────────────────────────────────
  TACTIC SHAPE
  ─────────────────────────────────────────────────────────────────────────

  Slice 2 will provide ONE tactic with TWO surface forms.

    (a) `extract_pure h`
        Walks the type of `h : (A1 ** … ** An) σ` (for any associativity),
        finds every immediate `⌜Pi⌝` factor, introduces one fresh hypothesis
        per pure factor named `h_pure_<i>` (or `h_pureN` if anonymous), and
        REPLACES `h` with the residual sep-conj of the non-pure factors.
        If there is no residual, `h` becomes `True` (and is cleared).

    (b) `extract_pure h => ⟨h1, h2, …, hk⟩`
        Same as (a) but the user supplies explicit names for each extracted
        pure hypothesis, in left-to-right order of appearance.  k must equal
        the number of detected pure factors; mismatch is a tactic error.

  Both forms preserve the resource tail in a hypothesis re-bound to the
  original name `h`.  This matters for downstream `xperm_hyp` / `sep_perm`
  calls that key off that name.

  ─────────────────────────────────────────────────────────────────────────
  IMPLEMENTATION SKETCH (slice 2 will refine)
  ─────────────────────────────────────────────────────────────────────────

  The cleanest implementation is a `macro_rules` / `elab` wrapper around the
  existing `sepConj_pure_left` / `sepConj_pure_right` rewrites already
  proven in `EvmAsm/Rv64/SepLogic.lean`:

      sepConj_pure_left  : (⌜P⌝ ** Q) h ↔ P ∧ Q h
      sepConj_pure_right : (P ** ⌜Q⌝) h ↔ P h ∧ Q

  Pseudo-algorithm:
    1. Inspect the type of `h`. Strip the outer state argument.
    2. Re-associate the conjunction to a flat right-nested list of factors
       via `sepConj_assoc'` (already in SepLogic).
    3. For each factor that is `⌜·⌝`, apply `sepConj_pure_left` (or `_right`
       for the trailing position) to peel it; bind the resulting `P` to a
       fresh fvar.
    4. Reassemble the residual factors back into a single `**` chain and
       rebind to `h`.

  This avoids the brittle "count the layers" approach and relies only on
  the AC equalities already used by `sep_perm`.

  ─────────────────────────────────────────────────────────────────────────
  ACCEPTANCE FOR SLICE 2 (evm-asm-455)
  ─────────────────────────────────────────────────────────────────────────

  - This file replaced with the real tactic + ≥3 `example` smoke tests
    covering: depth-1 chain, mixed pure/resource, all-pure, all-resource.
  - `lake build` green; no new sorries.
  - Tactic exported under namespace `EvmAsm.Rv64.Tactics`.

  ─────────────────────────────────────────────────────────────────────────
  ACCEPTANCE FOR SLICE 3 (evm-asm-8f5)
  ─────────────────────────────────────────────────────────────────────────

  - The three target sites above each have their `obtain` chain replaced by
    a single `extract_pure` invocation.
  - Net diff: at least −15 lines across the three sites.
  - `lake build` green; no new sorries.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

namespace EvmAsm.Rv64.Tactics

-- Intentionally empty. See module-level doc for the full design.
-- Slice 2 (beads evm-asm-455 / GH #1432) replaces this section with the
-- `extract_pure` tactic implementation and its smoke tests.

end EvmAsm.Rv64.Tactics
