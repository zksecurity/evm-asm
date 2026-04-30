/-
# `extract_pure` — design stub (slice 1 of #1432, beads evm-asm-bx7)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file is a DESIGN-ONLY stub. It does NOT yet implement the tactic; that is
slice 2 (beads evm-asm-455). Slice 3 (beads evm-asm-8f5) will rewrite call
sites to use the new tactic.

## Motivation

Across the codebase we have repeated `obtain ⟨_, _, _, _, _, h⟩ := h` chains
whose only purpose is to drag a pure proposition (`⌜P⌝`, a decidable Prop, or
a sep-conjoined `Prop`) out of the trailing position of a long `**` chain so
that the body of a proof can use `P`. The chain is otherwise discarded.

Concrete reference site (slice 3 will rewrite this):

  EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean:107-115
    -- 6 obtains drilling through 6 layers of `**`, just to get `hpost.2 : P`.

## Survey of call sites (≥3 required by acceptance criterion)

The pattern "≥3 consecutive `obtain ⟨…⟩ := <name>` lines on a single
sep-conj hypothesis, all named after the same hypothesis" appears in
(line numbers approximate, found 2026-04-30):

1. EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean:109   (6 obtains, target = `hpost`)
   Goal: extract the trailing `⌜P⌝` after 6 layers of associated `**`.

2. EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean:400   (7 obtains, target = `hrest`)
   Goal: extract `rhatHi2 ≠ 0` from a deep sep-conj.

3. EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean:440   (7 obtains, target = `hrest`)
   Same pattern, sibling lemma.

4. EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2.lean:456   (6 obtains, target = `hrest`)
5. EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2.lean:500   (6 obtains, target = `hrest`)

All five sites unfold a `cpsTriple` postcondition (or a manual closure body)
via `intro hp hP` and then traverse the `sepConj` chain by hand. Slice 3
rewrites these.

## Proposed syntax

  extract_pure h
    -- introduces hypotheses `h_pure_1, h_pure_2, …` for each pure atom
    -- found in the `sepConj` chain pointed to by `h`, and replaces `h`
    -- itself with the resource-only tail.

  extract_pure h with ⟨hP, hQ⟩
    -- like the unnamed form, but lets the user name the extracted purities
    -- in the order they appear (left-to-right in the flattened `**` chain).

  extract_pure h using P
    -- short form when the user only wants ONE specific pure atom matching
    -- syntactic shape `P` (or `⌜P⌝`) — closes the goal `⊢ P` directly if
    -- that's the goal, otherwise introduces it as `h_pure : P`.

## What counts as "pure"

The tactic recognises the following atoms as pure (extractable):

* `⌜P⌝`         — the canonical separation-logic `pureAssertion` wrapper.
* `sep_pure P`  — alias if it exists in the codebase.
* `↑P`          — coercion of a `Prop` into an assertion (`PropAsAssertion`
  or similar).
* Any nullary `Assertion` that unfolds (with `simp only [reducible]` /
  `unfold`) to one of the above.

The tactic is purely syntactic on the *type* of the hypothesis after a
single `simp only [pureAssertion, sepConj, …]` normalisation pass; it does
not invoke `decide` or attempt to evaluate `P`.

## What is left in place ("the tail")

After all pure atoms are extracted, the remaining `**`-chain of resource
assertions (`↦ᵣ`, `↦ₘ`, `regOwn`, etc.) is reassembled into a single
re-bound hypothesis with the original name. If every atom was pure the
original hypothesis becomes `True` and is cleared.

## Implementation sketch (slice 2)

1. Inspect the type of `h`: walk it as a right-associated `sepConj` tree,
   classifying each leaf as pure or resource.
2. Use `obtain` (under the hood) once per layer to split into
   `(left, right)` pairs, but generated programmatically rather than
   hand-written.
3. For each pure leaf, generate a fresh hypothesis `h_pure_k` (or use the
   user-provided name pattern).
4. Re-conjoin the resource leaves with `And.intro` / `sepConj.intro` to
   restore the original name `h`.
5. Implement as a `macro` over `Lean.Elab.Tactic`, in this file.

## Acceptance criteria for slice 1 (this file)

* [x] Stub file exists at this path with full design.
* [x] Survey lists ≥3 candidate sites (this file lists 5).
* [x] No `sorry`, no `admit`, no semantic content yet.
* [x] File is registered in `EvmAsm/Rv64/Tactics.lean` umbrella so it builds.
-/

namespace EvmAsm.Rv64.Tactics.ExtractPure

/-- Placeholder — real tactic lands in slice 2 (beads evm-asm-455). -/
def designStubPlaceholder : Unit := ()

end EvmAsm.Rv64.Tactics.ExtractPure
