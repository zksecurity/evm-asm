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
  Instructions.lean  -- RV32I instruction subset and semantics
  Program.lean       -- Programs as instruction lists, sequential composition
  SepLogic.lean      -- Separation logic assertions and combinators
  Spec.lean          -- Hoare triples, frame rule, structural rules
  MulMacro.lean      -- The add_mulc macro with correctness proofs ⭐
  Examples.lean      -- Swap, zero, triple, and other macro examples
RiscVMacroAsm.lean   -- Root module importing all submodules
```

## Key Lean 4 API Compatibility Notes

When working with this codebase, be aware of these Lean 4 nightly API changes:

1. **Logic lemmas**: Use lowercase names (`and_assoc`, `and_comm` instead of `And.assoc`, `And.comm`)
2. **Doc comments**: Cannot place `/-- ... -/` doc comments immediately before `#eval` commands (use regular `--` comments)
3. **Proof tactics**: `simp` may need explicit lemma lists or `rw` for manual rewriting
4. **Namespace**: Most theorems are in `namespace MachineState`, so use full names like `MachineState.getReg_setPC`

## Main Theorem to Prove

The primary open problem is **`add_mulc_correct`** in `RiscVMacroAsm/MulMacro.lean:131`:

```lean
theorem add_mulc_correct (nbits : Nat) (rd rs : Reg)
    (hne : rd ≠ rs) (hrd : rd ≠ .x0) (hrs : rs ≠ .x0)
    (m : Nat) (hm : m < 2 ^ nbits) :
    ∀ s : MachineState,
      (execProgram s (add_mulc nbits rd rs m)).getReg rd =
        s.getReg rd + s.getReg rs * BitVec.ofNat 32 m := by
  sorry
```

### Proof Strategy

The theorem requires proving that the shift-and-add multiplication macro is correct. Key elements needed:

1. **Induction on `nbits`**: Natural number induction
2. **Case analysis**: Whether `m % 2 == 1` (m is odd) or `m % 2 == 0` (m is even)
3. **Loop invariant**: `rd = v + w * (m % 2^k)` and `rs = w * 2^k` where k is the number of bits processed
4. **Register file lemmas**: Use `MachineState.getReg_setReg_eq`, `MachineState.getReg_setReg_ne`, `MachineState.getReg_setPC`
5. **BitVector arithmetic**: Lemmas relating shift operations (`shiftLeft`) to multiplication and division

### Available Lemmas

- `execProgram_nil`: Executing empty program is identity
- `execProgram_cons`: Executing `i :: is` = execute instruction then rest
- `execProgram_append`: Program composition theorem
- `MachineState.getReg_setPC`: Setting PC doesn't affect register reads
- `MachineState.getReg_setReg_eq`: Reading a register just set
- `MachineState.getReg_setReg_ne`: Reading a different register

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

## Testing

All concrete examples should pass:

```bash
lake build  # Should succeed with only 1 sorry (add_mulc_correct)
```

The project includes concrete test cases using `native_decide`:
- Multiply by constants: 0, 1, 3, 6, 10, 255
- Swap macro correctness
- Zero and triple macros

## Git Workflow

- Main branch: `main`
- Create feature branches for new work
- Use meaningful commit messages with Co-Authored-By line for AI contributions

## References

- **Original paper**: Kennedy et al., "Coq: The world's best macro assembler?" PPDP 2013
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **RISC-V ISA**: https://riscv.org/technical/specifications/
- **sail-riscv-lean**: https://github.com/opencompl/sail-riscv-lean (same toolchain)
- **Lean 4 docs**: https://lean-lang.org/documentation/

## Next Steps

Potential future work:
1. Complete `add_mulc_correct` proof
2. Connect to sail-riscv-lean for full ISA semantics
3. Add more verified macros (e.g., division, modulo)
4. Prove frame rule instances for more instructions
5. Extend to more RISC-V instructions (branches, loads/stores)
