# RiscVMacroAsm: A Verified Macro Assembler for RISC-V in Lean 4

A prototype implementation of a verified macro assembler for RISC-V, inspired by:

> Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
> **"Coq: The world's best macro assembler?"**
> *Proceedings of the 15th International Symposium on Principles and Practice
> of Declarative Programming (PPDP 2013)*, September 2013, ACM.
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

The original paper uses Coq to formalize x86 assembly with separation logic
specifications. This project adapts the same ideas to **RISC-V** (RV32I subset)
using **Lean 4** as both the macro language and the verification language.

## Key Idea

Lean 4 serves simultaneously as:

1. **An assembler**: Instructions are an inductive type; programs are lists of
   instructions with sequential composition (`;;`).
2. **A macro language**: Lean functions that produce programs act as macros,
   using all of Lean's facilities (recursion, pattern matching, conditionals).
3. **A specification language**: Hoare triples with separation logic assertions
   express correctness properties.
4. **A proof assistant**: Lean's kernel verifies that macros meet their
   specifications.

## The `add_mulc` Macro

The flagship example is `add_mulc`, a macro that multiplies a register by a
compile-time constant using the shift-and-add algorithm:

```lean
def add_mulc (nbits : Nat) (rd rs : Reg) (m : Nat) : Program :=
  match nbits with
  | 0 => prog_skip
  | nbits' + 1 =>
    if m % 2 == 1 then
      ADD rd rd rs ;;
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)
    else
      SLLI rs rs 1 ;;
      add_mulc nbits' rd rs (m / 2)
```

The specification (in the style of Kennedy et al.) uses separating conjunction:

```lean
theorem add_mulc_spec (m nbits : Nat) (hm : m < 2 ^ nbits)
    (rd rs : Reg) (hne : rd ≠ rs) (hrd : rd ≠ .x0) (hrs : rs ≠ .x0)
    (v w : Word) :
    ⦃(rd ↦ᵣ v) ** (rs ↦ᵣ w)⦄
    add_mulc nbits rd rs m
    ⦃fun s => s.getReg rd = v + w * BitVec.ofNat 32 m⦄
```

Concrete instances are verified by `native_decide`:

```lean
example : (execProgram (testState 10 7) (add_mulc 4 .x10 .x11 3)).getReg .x10
    = 10 + 7 * 3 := by native_decide
```

## Project Structure

```
RiscVMacroAsm/
  Basic.lean         -- Machine state: registers, memory, PC
  Instructions.lean  -- RV32I instruction subset and semantics (incl. ECALL)
  Program.lean       -- Programs as instruction lists, sequential composition
  Execution.lean     -- Branch-aware execution, code memory, step/stepN
  SepLogic.lean      -- Separation logic assertions and combinators
  Spec.lean          -- Hoare triples, frame rule, structural rules
  CPSSpec.lean       -- CPS-style Hoare triples, branch specs, structural rules
  ControlFlow.lean   -- if_eq macro, symbolic proofs, pcIndep
  MulMacro.lean      -- The add_mulc macro with correctness proofs
  Examples.lean      -- Swap, zero, triple, halt, and other macro examples
```

## Lean Toolchain

This project uses the same Lean 4 toolchain as
[sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean):

```
leanprover/lean4:nightly-2026-01-22
```

## Building

```bash
# Install elan (Lean version manager) if not already installed
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build the project
lake build
```

## Status

This is a **prototype** demonstrating the approach. Current state:

- **Working**: Machine model, instruction semantics, program composition,
  separation logic framework, Hoare triple infrastructure, concrete
  correctness proofs via `native_decide`.
- **Proved**: Separation logic properties (commutativity, associativity, unit),
  Hoare triple structural rules (skip, sequence, consequence, frame,
  existential), register file lemmas (`getReg_setReg_eq`, `getReg_setReg_ne`,
  `getReg_setPC`), swap correctness (symbolic Hoare triple proof),
  `add_mulc_correct` (general inductive proof), real separation logic with
  `PartialState` and PC as resource, CPS-style branch specs (`cpsBranch`,
  `cpsNBranch`), `if_eq` control flow macro with symbolic proofs,
  ECALL/HALT termination (SP1 convention).
- **TODO**: More control flow macros (loops, function calls), connect to
  sail-riscv-lean for full ISA coverage.

## Relationship to sail-riscv-lean

The [sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean) project
provides a complete, machine-generated Lean 4 formalization of the full
RV64D RISC-V ISA. This project uses the same Lean toolchain for compatibility.
A natural next step would be to connect this macro assembler framework to the
full sail-riscv-lean semantics, proving that the generated instruction
sequences behave correctly under the official RISC-V specification.

## References

- Kennedy, A., Benton, N., Jensen, J.B., Dagand, P.-E. (2013).
  "Coq: The world's best macro assembler?" PPDP 2013.
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- SP1 zkVM: https://github.com/succinctlabs/sp1
  The `ECALL`-based termination mechanism follows SP1's convention of using
  `ecall` with syscall ID in `t0` (x5) to signal halting.
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA specification: https://riscv.org/technical/specifications/
