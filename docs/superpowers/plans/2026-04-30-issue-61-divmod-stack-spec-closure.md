# Issue 61 DIV/MOD Stack Spec Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close GitHub issue #61 by landing bounded, imported, user-facing DIV/MOD limb and stack specs.

**Architecture:** Finish this as a chain of small PRs. Keep arithmetic correctness lemmas separate from CPS composition, keep limb-level full dispatch separate from `evmWordIs` stack adapters, and finish with import/docs cleanup. All new executable specs should use `cpsTripleWithin` / `cpsBranchWithin`; do not introduce unbounded wrappers or `10000` placeholder bounds.

**Tech Stack:** Lean 4, Lake, `EvmAsm.Rv64.CPSSpec`, DivMod composition specs, `evmWordIs`, Beads.

---

## Current State

GitHub issue #61 asks for:

- `Evm64/DivMod/Spec.lean`
- limb-level `evm_div_spec` / `evm_mod_spec`
- stack-level `evm_div_stack_spec` / `evm_mod_stack_spec`
- `EvmWord.div_correct` / `EvmWord.mod_correct`
- DivMod index importing `Spec`

As of PR #1431:

- `EvmAsm/Evm64/DivMod/Spec.lean` exists and includes zero-divisor plus n=4 max-path stack wrappers.
- `SpecCall.lean`, `SpecCallAddbackBeq.lean`, and `SpecCallV4.lean` cover much of the n=4 call-path stack surface.
- `Div128V4` and `Div128Step2v4` are imported and migrated to bounded verification.
- `DivMod.lean` imports `Shift0Dispatcher` and other closure files transitively, but does not clearly import the final `Spec` surface as the issue requests.
- There are no active `sorry`/`admit` proof terms in the searched DivMod/EvmWordArith surface, only comments referring to former proof gaps.

## PR Sequence

### PR 1: Add User-Facing EvmWord DIV/MOD Correctness Surface

**Purpose:** Make the arithmetic target explicit before composing stack specs.

**Files:**
- Create or modify: `EvmAsm/Evm64/EvmWordArith/DivCorrect.lean`
- Modify: `EvmAsm/Evm64/EvmWordArith.lean`
- Read: `EvmAsm/Evm64/EvmWordArith/DivAccumulate.lean`
- Read: `EvmAsm/Evm64/EvmWordArith/DivN4Overestimate.lean`
- Read: `EvmAsm/Evm64/EvmWordArith/Div128Shift0.lean`
- Read: `EvmAsm/Evm64/EvmWordArith/ModBridgeAssemble.lean`

**Deliverables:**
- Add exported theorem names for the issue, preferably:
  - `EvmWord.div_correct`
  - `EvmWord.mod_correct`
- These should cover zero divisor and nonzero divisor cases at the `EvmWord` level, delegating to existing normalized/no-shift/shift0/n4 bridge lemmas.
- If a fully unconditional theorem is still too broad, add the exact staged theorem names needed by stack dispatch and document the remaining dispatcher hypotheses in the theorem statement.

**Steps:**
- [ ] Add a small failing import/check file or local `#check EvmWord.div_correct` while developing.
- [ ] Prove zero-divisor cases from `EvmWord.div_zero_right` / `EvmWord.mod_zero_right`.
- [ ] Wire nonzero cases through existing DivAccumulate and bridge lemmas without duplicating arithmetic.
- [ ] Import the new file from `EvmAsm/Evm64/EvmWordArith.lean`.
- [ ] Verify with `lake build EvmAsm.Evm64.EvmWordArith.DivCorrect` and full `lake build`.

**PR acceptance:**
- `#check EvmAsm.Evm64.EvmWord.div_correct` and `#check EvmAsm.Evm64.EvmWord.mod_correct` succeed from downstream imports.
- Full build passes with no new unimported modules.

### PR 2: Normalize and Split the Stack Spec Surface

**Purpose:** Reduce the risk of closing issue #61 inside very large files.

**Files:**
- Split from: `EvmAsm/Evm64/DivMod/Spec.lean`
- Split from: `EvmAsm/Evm64/DivMod/SpecCall.lean`
- Split from: `EvmAsm/Evm64/DivMod/SpecCallAddbackBeq.lean`
- Split from: `EvmAsm/Evm64/DivMod/SpecCallV4.lean`
- Create as needed under: `EvmAsm/Evm64/DivMod/Spec/`
- Modify: `EvmAsm/Evm64/DivMod/Spec.lean`

**Suggested modules:**
- `Spec/Base.lean`: shared pre/post bundles, `pcFree` instances, scratch ownership weakeners.
- `Spec/Zero.lean`: `evm_div_bzero_stack_spec_within`, `evm_mod_bzero_stack_spec_within`.
- `Spec/Max.lean`: max skip/addback stack wrappers.
- `Spec/CallSkip.lean`: call-skip stack wrappers.
- `Spec/CallAddback.lean`: call-addback BEQ stack wrappers.
- `Spec/V4.lean`: V4 semantic predicates and V4-only bridges.
- `Spec.lean`: lightweight re-export.

**Steps:**
- [ ] Move only definitions first; do not change theorem statements.
- [ ] Keep import order acyclic: `Base` first, path files next, `Spec.lean` last.
- [ ] Preserve existing theorem names for downstream users.
- [ ] Add direct imports to `Spec.lean` and verify downstream `DivMod.lean` still builds.
- [ ] Run `scripts/check-file-size.sh --report`; avoid new file-size exceptions unless a file is intentionally a proof bundle.

**PR acceptance:**
- Public theorem names still compile.
- `lake build EvmAsm.Evm64.DivMod.Spec` passes.
- File-size guardrail passes without adding broad exceptions.

### PR 3: Finish Bounded Limb-Level Full Dispatchers

**Purpose:** Produce the issue-level limb specs `evm_div_spec` and `evm_mod_spec`.

**Files:**
- Modify/create: `EvmAsm/Evm64/DivMod/Compose/Dispatcher.lean`
- Modify: `EvmAsm/Evm64/DivMod/Compose.lean`
- Read: `Compose/PhaseAB.lean`
- Read: `Compose/FullPathN1.lean`
- Read: `Compose/FullPathN2Full.lean`
- Read: `Compose/FullPathN3.lean`
- Read: `Compose/FullPathN4.lean`
- Read: `Compose/ModFullPath*.lean`
- Read: `Shift0Dispatcher.lean`

**Deliverables:**
- `evm_div_spec_within`
- `evm_mod_spec_within`
- Optional compatibility aliases only if needed, but avoid new unbounded `cpsTriple` theorems.

**Steps:**
- [ ] State the final limb dispatcher over `divCode base` / `modCode base`.
- [ ] Case split in the same order as the program: zero divisor, n dispatch, shift0/nonzero shift, max/call, skip/addback.
- [ ] Compose only existing bounded path specs; replace any `10000` bounds encountered on the critical path with exact or defensible bounds before using them.
- [ ] Use `cpsTripleWithin_mono_nSteps` only to align smaller exact paths to a documented dispatcher bound.
- [ ] Add `CodeReq` subsumption lemmas structurally using `CodeReq.unionAll`, `skipBlock`, `ofProg_mono_sub`, and `bv_addr`.
- [ ] Verify `lake build EvmAsm.Evm64.DivMod.Compose.Dispatcher`.

**PR acceptance:**
- `#check evm_div_spec_within` and `#check evm_mod_spec_within` succeed.
- No new unbounded CPS theorem is introduced.
- No new `10000` placeholder bound appears in new dispatcher code.

### PR 4: Finish Stack-Level DIV/MOD Dispatchers

**Purpose:** Produce the final issue-level `evmWordIs` specs.

**Files:**
- Modify/create: `EvmAsm/Evm64/DivMod/Spec/Dispatcher.lean`
- Modify: `EvmAsm/Evm64/DivMod/Spec.lean`
- Read: all path modules from PR 2.
- Read: `EvmAsm/Evm64/EvmWordArith/DivCorrect.lean`

**Deliverables:**
- `evm_div_stack_spec_within`
- `evm_mod_stack_spec_within`
- Optional aliases `evm_div_stack_spec` / `evm_mod_stack_spec` only if they are still bounded or are naming aliases that do not reintroduce unbounded CPS.

**Steps:**
- [ ] State the public precondition with `(.x12 ↦ᵣ sp)`, input `evmWordIs sp a`, input `evmWordIs (sp + 32) b`, register ownership, and scratch ownership/value assumptions matching existing path specs.
- [ ] State the public postcondition with `(.x12 ↦ᵣ (sp + 32))`, `evmWordIs sp a`, `evmWordIs (sp + 32) (EvmWord.div a b)` / `EvmWord.mod a b`, register ownership, scratch ownership.
- [ ] Compose zero-divisor, max, call-skip, call-addback, shift0, and V4-backed call paths through the limb dispatcher or existing stack path wrappers.
- [ ] Use path-specific semantic predicates only internally; discharge or package them with the new `EvmWord.div_correct` / `EvmWord.mod_correct` lemmas where possible.
- [ ] Keep final permutation callbacks syntactically stable: use `getLimbN`, irreducible post bundles, and standalone `_weaken` lemmas for large postconditions.
- [ ] Verify `lake build EvmAsm.Evm64.DivMod.Spec.Dispatcher`.

**PR acceptance:**
- `#check evm_div_stack_spec_within` and `#check evm_mod_stack_spec_within` succeed from `EvmAsm.Evm64.DivMod.Spec`.
- Final specs mention `evmWordIs` over `EvmWord.div` and `EvmWord.mod`, not only path-specific limb formulas.

### PR 5: Index, CI, and Issue Closure Cleanup

**Purpose:** Make issue #61 visibly complete for downstream users and CI.

**Files:**
- Modify: `EvmAsm/Evm64/DivMod.lean`
- Modify: `EvmAsm/Evm64.lean` only if needed.
- Modify: `scripts/unimported-allow.txt` only to remove newly reachable files.
- Optional docs: `TACTICS.md` or a short DivMod note if new dispatcher usage deserves documentation.

**Steps:**
- [ ] Add a clear direct `import EvmAsm.Evm64.DivMod.Spec` in `EvmAsm/Evm64/DivMod.lean`.
- [ ] Remove any DivMod spec/dispatcher files from `scripts/unimported-allow.txt`.
- [ ] Run `scripts/check-unimported.sh`.
- [ ] Run `scripts/check-file-size.sh`.
- [ ] Run `lake build`.
- [ ] Update GitHub issue #61 with the final theorem names and PR links, then close it.

**PR acceptance:**
- Full `lake build` passes.
- CI `build` and `summarize` pass.
- Issue #61 checklist items are all satisfied by named declarations/imports.

## Dependency Order

1. PR 1 blocks PR 4.
2. PR 2 blocks PR 4 and makes PR 3/PR 4 reviewable.
3. PR 3 blocks PR 4 if stack dispatch chooses to compose through final limb dispatchers.
4. PR 4 blocks PR 5.
5. PR 5 closes issue #61.

## Verification Commands

Run these at each PR boundary:

```bash
scripts/check-unimported.sh
scripts/check-file-size.sh
lake build EvmAsm.Evm64.DivMod.Spec
lake build
```

For dispatcher PRs, also run the narrow target first:

```bash
lake build EvmAsm.Evm64.DivMod.Compose.Dispatcher
lake build EvmAsm.Evm64.DivMod.Spec.Dispatcher
```
