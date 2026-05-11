# AI Agent Guide for EvmAsm

This document provides guidance for AI agents working on the EvmAsm project.

## Project Overview

EvmAsm is a verified macro assembler for RISC-V in Lean 4, inspired by "Coq: The world's best macro assembler?" (Kennedy et al., PPDP 2013). The project demonstrates using Lean 4 as both a macro language and verification framework for assembly code.

## Build System

- **Build tool**: Lake (Lean 4's build system)
- **Toolchain**: Lean 4.28.0-nightly-2026-01-22 (specified in `lean-toolchain`)
- **Build command**: `lake build`
- **Clean build**: `lake clean && lake build`

### Important Lake Configuration Notes

- The `lakefile.toml` uses Lake 5.0 format (root-level package fields, no `[package]` section)
- `defaultTargets = ["EvmAsm"]` is required for `lake build` to work
- The library name is `EvmAsm` and sources are in `EvmAsm/` directory

## Project Structure

```
EvmAsm/
  Rv64/                -- RV64IM machine model + infrastructure
    Basic.lean         -- Machine state: registers, memory, PC
    Instructions.lean  -- RV64IM instruction semantics (incl. ECALL)
    Program.lean       -- Programs as instruction lists, sequential composition
    Execution.lean     -- Step execution, code memory, ECALL dispatch
    SepLogic.lean      -- Separation logic assertions and combinators
    CPSSpec.lean       -- CPS-style Hoare triples, branch specs, structural rules
    GenericSpecs.lean  -- Generic instruction spec templates
    InstructionSpecs.lean -- Concrete instruction specs
    SyscallSpecs.lean  -- Spec database (@[spec_gen_rv64])
    ControlFlow.lean   -- if_eq macro, symbolic proofs
    ByteOps.lean       -- Byte-level: extractByte algebra, LBU/SB specs
    Tactics/           -- Automation: xperm, runBlock, liftSpec, etc.
  Evm64/               -- 256-bit EVM opcodes on RV64IM (4×64-bit limbs)
    Basic.lean         -- EvmWord (BitVec 256), getLimb/fromLimbs
    Stack.lean         -- evmWordIs, evmStackIs assertions
    Add/, Sub/, ...    -- Individual opcode implementations (30+ files)
  EL/                  -- Pure Ethereum Execution Layer specs
    RLP/               -- RLP encoding/decoding (no RISC-V dependency)
      Basic.lean       -- RLPItem type, encode
      Decode.lean      -- decode with canonical enforcement
      Properties.lean  -- Round-trip proofs (native_decide)
EvmAsm.lean            -- Root module: imports Rv64, Evm64, EL
```

## Key Lean 4 API Compatibility Notes

When working with this codebase, be aware of these Lean 4 nightly API changes:

1. **Logic lemmas**: Use lowercase names (`and_assoc`, `and_comm` instead of `And.assoc`, `And.comm`)
2. **Doc comments**: Cannot place `/-- ... -/` doc comments immediately before `#eval` commands (use regular `--` comments)
3. **Proof tactics**: `simp` may need explicit lemma lists or `rw` for manual rewriting
4. **Namespace**: Most theorems are in `namespace MachineState`, so use full names like `MachineState.getReg_setPC`

## Verification Workflow

When adding or modifying proofs:

1. **Build first**: Always run `lake build` to see current errors
2. **Use MCP tools**: The lean-lsp MCP server provides:
   - `lean_goal`: Check proof state at a position
   - `lean_diagnostic_messages`: Get compiler errors
   - `lean_hover_info`: Get type information
   - `lean_completions`: Get IDE completions
   - `lean_local_search`: Search for declarations locally
   - `lean_leansearch`: Natural language search in mathlib
   - `lean_loogle`: Type-based search in mathlib
3. **Test concretely**: Verify specific cases with `native_decide` before generalizing
4. **Incremental development**: Prove helper lemmas before the main theorem

## Critical Rules

- **Naming convention (Mathlib-aligned):**
  - **camelCase** for *value* identifiers: `let`-bound locals, theorem/lemma parameters, function arguments, definitions (e.g. `let qAddr := ...`, `theorem foo (carryNat : Nat)`).
  - **snake_case** for *hypothesis* names — proof bindings introduced by `have h_… : Prop`, `obtain ⟨h_lt, h_eq⟩`, `intro h_pos`, etc. Mathlib keeps these snake_case (e.g. `h_pos`, `h_le`, `h_zero`, `h_eq`). Do **NOT** rename `h_*`-style hypothesis names to camelCase as part of #189 cleanup — that's the wrong direction. PR #1497 made this mistake.
  - When in doubt: if it names a `Prop`-typed term used in a proof, leave snake_case; if it names data (a `Nat`, `Word`, `BitVec`, etc.), use camelCase.

- **Do NOT add `set_option maxHeartbeats` to any file** unless you are in `Evm64/Shift/` composition files (Compose, ShlCompose, SarCompose) for body/path composition proofs. Heartbeat limits are configured globally in `lakefile.toml`.
- **Do NOT add `set_option maxRecDepth` to any file.** Recursion depth is configured globally in `lakefile.toml`.
- If a proof times out or hits recursion limits, restructure the proof (e.g., split into smaller lemmas, use intermediate `have` bindings) rather than increasing limits. Increasing `maxRecDepth`/`maxHeartbeats` is almost always a waste of time — the real issue is typically a unification mismatch, wrong argument order, or missing address canonicalization.
- **Do not bump `maxHeartbeats` to make a slow proof compile.** Large heartbeat budgets just slow experiments — and the effect compounds: every retry, every edit, every CI run pays the cost. Needing monitors or `sleep` loops to wait for a build is itself a symptom that `maxHeartbeats` is too big. If a proof legitimately needs more than the default, it is too complicated — diagnose what is actually slow (a failing `rfl`, a stuck `xperm_hyp`, an accidentally false goal, or an `xperm` target with too many conjuncts) and simplify by:
  1. Splitting the proof into smaller named lemmas.
  2. Marking expensive intermediate definitions `@[irreducible]` and proving a small set of lemmas about them, so later proofs unfold via those lemmas instead of re-reducing the body each time.
  3. Breaking up large `have`s into separate lemmas so the core composition step has fewer atoms to permute.
- **Exception for Shift composition files**: `set_option maxHeartbeats` up to 6400000 is acceptable for body/path composition proofs (Section 4+) which are bottlenecked by `xperm_hyp` permutation on large atom chains. Subsumption lemmas (Section 2) should NOT need heartbeat overrides — they use structural `unionAll` reasoning.

## Common Pitfalls

1. **Notation issues**: Custom notations (like `↦ᵣ ?`) may not parse correctly; use functions directly
2. **Simp lemmas**: Mark key lemmas with `@[simp]` for automatic application
3. **List operations**: Be careful with `execProgram` and list append - may need explicit `execProgram_append`
4. **Register inequality**: Use `decide` tactic for concrete register inequality proofs
5. **Program type**: `Program = List Instr` is a `def`, not `abbrev` — use `simp only [..., Program]` to unfold before `List.length_append` etc.
6. **New `.lean` files must be imported by the umbrella module**: `lake build` will compile every file it can reach from `EvmAsm.lean` via the transitive `import` graph, which goes `EvmAsm.lean → Rv64.lean / Evm64.lean / EL.lean → individual modules`. Leaf files that are **not** imported still get built by `lake build` (Lake discovers them via the directory-scoped library), but they are **invisible to downstream consumers** — proofs in other files cannot `open` or reference their declarations. When you add a file, register it in the corresponding umbrella:
   - `EvmAsm/Rv64/Foo.lean` → add `import EvmAsm.Rv64.Foo` to `EvmAsm/Rv64.lean`.
   - `EvmAsm/Evm64/Foo/Bar.lean` → add `import EvmAsm.Evm64.Foo.Bar` to `EvmAsm/Evm64.lean` (or to an intermediate umbrella like `EvmAsm/Evm64/Foo.lean` if one exists).
   - `EvmAsm/EL/Foo.lean` → add `import EvmAsm.EL.Foo` to `EvmAsm/EL.lean`.

   If your new file declares an attribute via `register_simp_attr`, place the attribute-declaration file **before** any consumer file in the umbrella's import list so the attribute exists when the consumer is elaborated. Typical pattern: split into `FooAttr.lean` (declares the attribute) + `Foo.lean` (uses the attribute, imports `FooAttr`), then import both from the umbrella, attr first. See `Rv64/RegOpsAttr.lean` + `Rv64/RegOps.lean` or `Evm64/DivMod/AddrNormAttr.lean` + `Evm64/DivMod/AddrNorm.lean` for the canonical shape.

   CI enforces this via `scripts/check-unimported.sh` (issues #1209 / #1440): a `.lean` file under `EvmAsm/` that is not transitively reachable from `EvmAsm.lean` will fail the build. The grandfathering allow-list (`scripts/unimported-allow.txt`) was drained and removed in #1440 — there is no escape hatch, so wire new files into the appropriate umbrella when you add them.

## Testing

All concrete examples should pass with no sorries:

```bash
lake build  # Should succeed with 0 errors and 0 sorries
```

The project includes concrete test cases using `native_decide`:
- Multiply by constants: 0, 1, 3, 6, 10, 255
- Swap macro correctness
- Zero and triple macros
- ECALL/halt termination examples
- COMMIT-then-halt examples

## Import Hygiene (`lake exe shake`)

We use Mathlib's `shake` tool to flag unused imports. Configuration lives in
`scripts/noshake.json` (curated entries for known false positives — e.g.
files that use `IntervalCases` / `FinCases` / `Fintype` instances, the
`Init` / `Lean` modules referenced by Word notation, and tactic-registry
attributes that shake doesn't track).

Reproduction recipe:

```bash
lake build           # required: shake reads .olean metadata
lake exe shake EvmAsm
```

Pitfalls:

- `shake` does **not** track tactic registries / `@[spec_gen_*]` attributes
  that elaborate via tactics, term-elaborator macros, or `notation`-only
  references (`notation "Word" => BitVec 64` in `EvmAsm.Rv64.Basic`). Many
  of its suggestions are false positives — see the audit in beads
  `evm-asm-o6y` (parent `evm-asm-6qj`) before acting on raw shake output.
  Filter via `scripts/shake-filter.py` / `scripts/shake-filter.md` and
  verify each removal with `lake build` before committing.
- When in doubt, prefer adding a `noshake.json` entry over removing the
  import.

## Git Workflow

- Main branch: `main`
- Create feature branches for new work
- Use meaningful commit messages with Co-Authored-By line for AI contributions
- **PR titles must follow conventional commit format**: `type[(scope)]: subject`
  (e.g. `refactor: extract shared Shift Compose helpers`,
  `fix(shr): address canonicalization in sign-fill path`). The PR summary bot
  flags titles that don't match this format.

## Bead closure rules (`bd close`)

The beads tracker is the source of truth for outstanding work. Closing a bead
incorrectly hides unfinished obligations and bumping its priority later does
nothing because the bead is no longer in the queue. Before running
`bd close <id>`, satisfy **all** of the following:

1. **The named deliverable must exist on `origin/main`.** If the bead title
   says "prove `foo_spec_within`", "define `evm_foo`", or "lift X to Y", that
   exact declaration has to be present on `origin/main` — not on a feature
   branch, not in an unmerged stacked PR. Verify with:
   `git fetch origin && git grep -n '<decl name>' origin/main -- '<expected path>'`.
   If the grep is empty, **do not close the bead**.

2. **A "related" PR merging is not the same as the deliverable shipping.** A
   PR titled similarly, or that adds scaffolding, wrappers, or preparation
   lemmas around the deliverable, does not satisfy the bead. If the named
   theorem is still a `placeholder`, `sorry`, or absent, the bead stays open.

3. **Stacked PRs into feature branches don't count.** A PR merged into
   `feat/foo` instead of `main` has not landed. Wait for the bottom of the
   stack to merge into `main`, then verify per (1) before closing the
   dependent beads.

4. **`close_reason` must be truthful.** `"shipped in PR #N"` is only valid
   when PR #N's merge commit is an ancestor of `origin/main` *and* the named
   deliverable is grep-visible there. Otherwise use
   `"superseded by <bead-id>"` or `"duplicate of <bead-id>"`. Never close as
   "shipped" against a PR that merged into a feature branch.

5. **If you finished real work but the named theorem isn't done yet**,
   prefer adding a `bd comment` with status, or filing a follow-up bead, or
   updating the existing bead's description — instead of closing the wrong
   thing.

Recent violations to learn from: `evm-asm-01uh` (SDIV), `evm-asm-6snn` and
`evm-asm-w5mk` (EXP) — all closed as "shipped in PR #…" while the named
theorem was still a placeholder on `main` (and in the EXP cases the PR was
merged into a feature branch, not `main`). All three had to be reopened.

## References

- **Accelerator C ABI (source of truth)**:
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  is the canonical interface for cryptographic precompiles, KECCAK256, and
  secp256k1 verification. See [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)
  for how it maps to ECALL syscall IDs (which use SP1 transport conventions)
  and to EVM precompile addresses.
- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **zkvm_accelerators.h**: `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  is the source of truth for accelerator function signatures, argument
  layouts, and `zkvm_status` framing used by all EVM precompile and
  KECCAK256 bridges. See [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md).
- **Host I/O C ABI**: `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`
  defines the canonical host-I/O surface (`read_input` / `write_output`).
  See [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md)
  for the decision record and SP1 `HINT_LEN` / `HINT_READ` / `COMMIT` →
  zkvm-standards mapping. Migration tracked under beads parent
  `evm-asm-96ysd` (GH #114 / #116).
- **SP1 zkVM**: https://github.com/succinctlabs/sp1 (RISC-V `ECALL`
  framing only; function set follows `zkvm_accelerators.h`)
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/
- **Notable Specs Index**: [`docs/notable-specs.md`](docs/notable-specs.md) —
  curated index of proven specifications (per-opcode stack specs, EvmWord
  correctness theorems, RLP/ByteOps/calling-convention helpers) with
  commit-pinned permalinks. Use it to find a spec without grepping. Refresh
  procedure is documented at the bottom of that page; trigger is closure of a
  `#61`-class umbrella issue, or quarterly.

## Deep references

Detailed material has been split out of this file to keep the agent guide compact. **Load each
doc only when its trigger applies** — they are reference material, not required reading.

- [`docs/agents/tactics-deep.md`](docs/agents/tactics-deep.md) — Frame-automation tactics,
  separation-conjunction permutation (`xperm`), LP64 calling convention, three-level opcode
  proof architecture, Compose file splitting, file-size guardrail, benchmark-history branch.
  **Load when:** writing/restructuring `runBlock`/`seqFrame`/`xperm`/`xcancel`, designing a
  callable shim, working on a new opcode's three-level proof, or interpreting benchmark history.
- [`docs/agents/proof-patterns.md`](docs/agents/proof-patterns.md) — Bundling postconditions
  with `let` + `@[irreducible]`, adapter signatures with deep let-chains, `linarith` vs
  `omega`, pure-Nat sub-lemmas for `maxRecDepth` avoidance, end-to-end composition with
  existentials, `xperm` scaling, double-addback (`_da`) postcondition pattern.
  **Load when:** a specific proof symptom matches a section heading (use the index at the top
  of that file). Do not read top-to-bottom — these are deep recipes for narrow situations.

Companion files (already separate, unchanged):
- [`TACTICS.md`](TACTICS.md) — user-facing tactic reference.
- [`GRIND.md`](GRIND.md) — domain-specific grindset definitions.
- [`PLAN.md`](PLAN.md) — roadmap.
- [`docs/OPCODE_TEMPLATE.md`](docs/OPCODE_TEMPLATE.md) — new-opcode conventions (referenced below).

## Roadmap (PLAN.md)

The project roadmap is maintained in `PLAN.md`. See `CLAUDE.md` for the
maintenance protocol (when and how to update it).

## Scratchpad Layout (#334)

Routines that need `sp`-relative internal scratch cells (DivMod today, EXP /
Multiply with internal scratch later) must take their scratchpad layout as a
**parameter**, not bake offsets into the spec. Hardcoding offsets like
`sp + signExtend12 4056` makes the routine impossible to compose from a
non-trivial caller frame and forces every call site to use the same fixed
placement.

Convention (per `docs/scratchpad-layout-design.md`):

- One `XxxScratchpadLayout` structure per routine, with named fields for
  each scratch cell (e.g. `dividendNorm`, `divisorNorm`, `quotientHi`).
- A companion `XxxScratchpadLayout.Valid (L : XxxScratchpadLayout) : Prop`
  bundling per-cell validity (`isValidDwordAccess`) plus disjointness from
  the caller frame and from each other.
- A `canonicalXxxScratchpadLayout : XxxScratchpadLayout` matching today's
  hardcoded offsets, and a `canonicalXxxScratchpadLayout_valid` instance.
- Specs take `(L : XxxScratchpadLayout) (hL : L.Valid)` as parameters and
  reference `L.fieldName` instead of `sp + signExtend12 N` literals.
- The routine's existing fixed-offset spec stays as a thin shim that
  instantiates the canonical layout, so existing call sites keep compiling.

The naming convention is fixed: `EvmAsm/Evm64/<Routine>/Layout.lean`,
`<Routine>ScratchpadLayout`, `.Valid`, `canonical<Routine>ScratchpadLayout`,
`canonical<Routine>ScratchpadLayout_valid`. Slice 3 (`EvmAsm/Evm64/Multiply/Layout.lean`)
is the canonical empty-layout pilot — copy its file shape when adding scratch
to a new routine.

When introducing a new opcode subtree that will carry internal scratch
(EXP-class routines, future precompiles), define the layout struct from day
one — even if it starts empty — to avoid the retrofit tax. See `docs/scratchpad-layout-design.md`
for the full design and `docs/scratchpad-layout-survey.md` for the
hardcoded-offset inventory that motivated the change.

## New opcode conventions (OPCODE_TEMPLATE.md)

Before starting a new opcode subtree (SDIV, SMOD, ADDMOD, MULMOD, EXP, …),
read **[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md)**.
It codifies the directory layout, unified-dispatch-first rule, named offset
constants, address grindset, validity bundling, and review checklist
distilled from the DivMod retrofit work. Landing a new opcode on this
substrate from day one avoids the retrofit tax documented in issues
#262 / #263 / #264 / #265 / #266 / #283 / #301 / #312.
