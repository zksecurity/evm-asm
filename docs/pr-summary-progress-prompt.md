<!--
  Project-specific instructions appended to the PR-summary LLM context
  via `additional_instructions_path` in `lean-summary-workflow`. Fed
  into the workflow alongside `CONTRIBUTING.md` and the computed
  progress delta produced by `scripts/progress-delta.sh`.

  Keep this file project-specific. Generic LLM guidance lives upstream
  in the workflow's prompt templates.
-->

# Progress-assessment instructions for the PR-summary agent

evm-asm tracks per-PR progress against a kernel-checked registry
(`EvmAsm/Progress.lean`) rendered to `PROGRESS.md`. The deployment
pre-step has already computed a deterministic delta and inserted it
above under "Computed progress delta for this PR". Use those numbers
verbatim — do not recompute or infer them from the diff.

## Output shape

Emit a top-level section titled exactly `## Progress assessment` at
the **end** of the PR summary. The section is short, factual, and
narrates what the computed delta means in the project's vocabulary.

If the computed delta shows no count changes and no tier transitions,
write exactly:

    ## Progress assessment

    Metric-neutral PR (no tier transitions, no count deltas).

Otherwise, include up to four bullets covering:

- **Tier transitions**: list every transition from the computed delta
  verbatim (e.g. `SDIV: partial → proven`). Do not invent or filter.
- **Count deltas**: cite only counts that changed; omit unchanged
  ones. Keep them as numbers, not adjectives ("provenCount +2", not
  "significant progress").
- **Drift risks**: if the diff adds an `evm_<name>_stack_spec_within`
  theorem but the registry change does not mention a matching
  `_<name>_witness` abbrev in `EvmAsm/Progress.lean`, flag it as a
  drift risk. The deterministic gate in `scripts/check-progress.sh`
  catches `PROGRESS.md` drift, but theorem-without-witness is a
  registry-completeness issue the gate does not catch.
- **Obligation mapping**: when a tier transition advances one of the
  9 guest-program obligations from `PROGRESS.md` ("Role in the
  L1-zkEVM stack" section), say so explicitly (e.g.
  `Advances obligation #5: full opcode coverage`). At most one
  obligation per bullet.

## What NOT to do

- **Do not recompute counts** from the diff. The numbers above are
  derived from the kernel-checked registry and are authoritative.
- **Do not editorialize** ("major step forward", "significant
  improvement", "well done"). Stay factual.
- **Do not duplicate** the existing `Mathematical Formalization` /
  `Proof Completion (sorries removed)` / `Infrastructure` sections
  the workflow already produces. The Progress assessment is a
  *quantitative* commentary on top of those.
- **Do not flag tier downgrades** as failures. A `proven` → `partial`
  transition might mean a generalization is in progress and the
  spec has been deliberately weakened. State the transition;
  don't judge it.
- **Do not invent obligation mappings.** If you cannot point at a
  specific obligation number from `PROGRESS.md` for a given change,
  skip the mapping. False mappings are worse than no mapping.

## Vocabulary reference

These terms appear in the project and the registry; use them
consistently:

- `proven` / `partial` / `execSpec` / `notStarted` — the four
  `ProofTier` values defined in `EvmAsm/Progress.lean`.
- `cpsTripleWithin N` — bounded Hoare triple over a verified RV64
  step count of at most `N`.
- `EvmWord` — `BitVec 256`; 4-limb 64-bit representation in RV64.
- `stack spec` — top-level Hoare triple over the EVM stack
  (precondition: stack pointer + EvmWord operands; postcondition:
  stack pointer advanced + EvmWord result).
- `witness abbrev` — the `_<lower>_witness := @<theorem>` declarations
  in `EvmAsm/Progress.lean` that fail elaboration if a referenced
  theorem is renamed or deleted.
- `guest program` — in this project, the RV64 ELF that runs inside an
  L1 zkVM and validates a block + execution witness (see
  `PROGRESS.md` for the 9-item obligation list).

## When to keep the section short

If the PR is a refactor, a doc edit, a test addition, an
infrastructure change, or any other change that does not move any
metric or tier, write the metric-neutral one-liner. Do not pad.
Reviewers read silence as "this PR is not about progress" — that's
the correct signal.
