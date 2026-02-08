# AI Agent Guide for RiscVMacroAsm

This document provides guidance for AI agents working on the RiscVMacroAsm project.

## Project Overview

RiscVMacroAsm is a verified macro assembler for RISC-V in Lean 4, inspired by "Coq: The world's best macro assembler?" (Kennedy et al., PPDP 2013). The project demonstrates using Lean 4 as both a macro language and verification framework for assembly code.

## Build System

- **Build tool**: Lake (Lean 4's build system)
- **Toolchain**: Lean 4.28.0-nightly-2026-01-22 (specified in `lean-toolchain`)
- **Build command**: `lake build`
- **Clean build**: `lake clean && lake build`

### Important Lake Configuration Notes

- The `lakefile.toml` uses Lake 5.0 format (root-level package fields, no `[package]` section)
- `defaultTargets = ["RiscVMacroAsm"]` is required for `lake build` to work
- The library name is `RiscVMacroAsm` and sources are in `RiscVMacroAsm/` directory

## Project Structure

```
RiscVMacroAsm/
  Basic.lean         -- Machine state: registers, memory, PC
  Instructions.lean  -- RV32I instruction subset and semantics (incl. ECALL)
  Program.lean       -- Programs as instruction lists, sequential composition, HALT/COMMIT macros
  Execution.lean     -- Branch-aware execution, code memory, step/stepN, ECALL dispatch
  SepLogic.lean      -- Separation logic assertions and combinators
  Spec.lean          -- Hoare triples, frame rule, structural rules
  CPSSpec.lean       -- CPS-style Hoare triples, branch specs, structural rules
  ControlFlow.lean   -- if_eq macro, symbolic proofs, pcIndep
  MulMacro.lean      -- The add_mulc macro with correctness proofs
  Examples.lean      -- Swap, zero, triple, halt, commit, and other macro examples
RiscVMacroAsm.lean   -- Root module importing all submodules
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

## Common Pitfalls

1. **Notation issues**: Custom notations (like `↦ᵣ ?`) may not parse correctly; use functions directly
2. **Simp lemmas**: Mark key lemmas with `@[simp]` for automatic application
3. **List operations**: Be careful with `execProgram` and list append - may need explicit `execProgram_append`
4. **Register inequality**: Use `decide` tactic for concrete register inequality proofs
5. **Program type**: `Program = List Instr` is a `def`, not `abbrev` — use `simp only [..., Program]` to unfold before `List.length_append` etc.

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

## Git Workflow

- Main branch: `main`
- Create feature branches for new work
- Use meaningful commit messages with Co-Authored-By line for AI contributions

## References

- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SP1 zkVM**: https://github.com/succinctlabs/sp1
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/

## Separation Conjunction Permutation Tactic

The `sep_perm` tactic (defined in `SepLogic.lean`) closes goals that require rearranging `sepConj` (`**`) chains. It works by AC-normalizing both the hypothesis and goal using `simp` with three equality lemmas:

- `sepConj_assoc'` : `((P ** Q) ** R) = (P ** (Q ** R))`
- `sepConj_comm'` : `(P ** Q) = (Q ** P)`
- `sepConj_left_comm'` : `(P ** (Q ** R)) = (Q ** (P ** R))`

**Usage**: Given a hypothesis `h : (A ** B ** C) s` and goal `⊢ (C ** A ** B) s`:
```lean
sep_perm h
```

This handles arbitrary permutations of any number of assertions in a `sepConj` chain.

## Next Steps

Potential future work:
1. More control flow macros (loops, function calls)
2. More SP1 syscalls (e.g. LWA, WRITE)
3. Connect to sail-riscv-lean for full ISA semantics
4. Add more verified macros (e.g., division, modulo)
5. Prove frame rule instances for more instructions
