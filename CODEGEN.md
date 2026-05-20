# Codegen

Roadmap for emitting executable RISC-V from the verified `Program`s in this
repo and running them on the Zisk emulator (`ziskemu`). Companion to
[`PLAN.md`](PLAN.md) (the verification roadmap) and the host-I/O ADR at
[`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md).

## Locked decisions

1. **Text emitter first.** Emit a `.s` file, assemble & link with
   `riscv64-unknown-elf-as -march=rv64imac` and
   `riscv64-unknown-elf-ld -Ttext=0x80000000`, run on `ziskemu`. A Lean-native
   binary encoder (`Instr → BitVec 32` + ELF writer) is *future work*, not
   blocking; see the Zisk
   [`elf-regressions`](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
   examples for the target shape.
2. **First smoke target.** A synthetic
   `LI a0, 42 ;; LI a1, 58 ;; ADD a2, a0, a1 ;; <halt>` — pure toolchain
   validation before touching EVM-specific memory layout. Mirrors Zisk's
   [`simple_add/test.s`](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s).
3. **Tool home: `lake exe codegen`.** A new Lean executable target declared in
   `lakefile.toml` and rooted at the existing `Main.lean`. Source of truth is
   the verified `Instr` type at `EvmAsm/Rv64/Basic.lean:113-237`.
4. **Halt convention is parametric**: `--halt={sp1,linux93}`.
   - `sp1` = `ECALL` with `t0 = 0` — matches the verified `step_ecall_halt` at
     `EvmAsm/Rv64/Execution.lean:611-615`.
   - `linux93` = `ECALL` with `a7 = 93` — matches Zisk's `simple_add`.
   - This sidesteps the still-Open
     [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) ADR.

## File layout

New code lives under a fresh `EvmAsm/Codegen/` tree so the verified core is
untouched. Generated artifacts go in `gen-out/` (gitignored).

| Path | Purpose |
|---|---|
| `EvmAsm/Codegen.lean` | Top-level umbrella (mirrors `EvmAsm/Rv64.lean`, `EvmAsm/Evm64.lean`). |
| `EvmAsm/Codegen/Emit.lean` | Pure `emitReg`, `emitInstr`, `emitProgram` — `Instr → String`. No `IO`. |
| `EvmAsm/Codegen/Layout.lean` | `HaltConv` enum, halt stubs, `_start` preamble, `.option norvc`, `MEM_START`/`MEM_END` constants, `BuildUnit` struct + `emitBuildUnit`/`emitDataLabel` helpers. |
| `EvmAsm/Codegen/Dispatch.lean` | M5b dispatcher scaffolding: `OpcodeHandlerSpec` (with optional `preBody` for x10-clobbering handlers) + `HandlerTail` types, `emitDispatcherPrologue`/`Epilogue`/`DataSection` and `buildDispatchUnit` helpers. Pure (no IO). |
| `EvmAsm/Codegen/Programs.lean` | Registry (`smoke`, `evm_add`, `evm_div`, `evm_mod`, `input_echo`, `evm_add_from_input`, `evm_div_from_input`, `evm_mod_from_input`, `tiny_interp_{add,add2}`, `tiny_interp_dispatch_{add,add2}` → `BuildUnit`) plus the M5b opcode handler registry (`tinyInterpRegistry`) composed from `pushHandlers` (PUSH0..32), `dupHandlers` (DUP1..16), `swapHandlers` (SWAP1..16), `singletonHandlers` (17 fixed-shape opcodes), `memoryHandlers` (MLOAD/MSTORE/MSTORE8, M7), `stopHandler`; shared helpers (`advancePc`, `copy64`, `evmAddEpilogue`, `evmDivPatched`/`evmModPatched` for the DIV/MOD NOP-splice). |
| `EvmAsm/Codegen/Tests/Cases.lean` | Per-opcode regression test registry: `OpcodeTestCase` struct + `opcodeTestCases` list. Wraps each bytecode through the M5b dispatcher for end-to-end ziskemu validation. |
| `EvmAsm/Codegen/Cli.lean` | Argument parsing (`--program`, `--test-case`, `--list-test-cases`, `--halt`, `--out`, `--asm-only`). |
| `EvmAsm/Codegen/Driver.lean` | `IO`: shells out to `as`/`ld` if available; `--asm-only` for CI without the cross toolchain. |
| `Main.lean` | Already exists as `import EvmAsm`; extend to call `EvmAsm.Codegen.Cli.main`. |
| `lakefile.toml` | Add `[[lean_exe]] name = "codegen"; root = "Main"; supportInterpreter = true`. |
| `scripts/codegen-*.sh` | Per-milestone round-trip checks: `codegen-smoke.sh` (M0), `codegen-evm_add-check.sh` (M2), `codegen-evm_add-from-input-check.sh` (M4), `codegen-tiny-interp-check.sh` (M5a), `codegen-tiny-interp-dispatch-check.sh` (M5b), `codegen-opcodes-check.sh` (M6a; canonical opcode regression runner), `codegen-evm_div-check.sh` / `codegen-evm_div-cases-check.sh` / `codegen-evm_mod-check.sh` / `codegen-evm_mod-cases-check.sh` (standalone DIV/MOD wrappers — not yet routed through the dispatcher). |
| `gen-out/` | Generated `.s`/`.elf`/`.input`; gitignored. |

## Milestones

### M0 — Synthetic smoke (S)

Emit `.s` for `smoke : Program := LI .x10 42 ;; LI .x11 58 ;; ADD .x12 .x10 .x11`,
assemble, link, run on `ziskemu`.

- Implement `emitInstr` for *only* the constructors needed by the smoke (`LI`,
  `ADD`, `ECALL`) plus the halt stubs.
- Wrapper:
  ```asm
  .option norvc
  .section .text
  .globl _start
  _start:
  <body>
  <halt stub>
  ```
  - Halt stub (sp1):    `li t0, 0` ; `ecall`
  - Halt stub (linux93): `li a7, 93` ; `li a0, 0` ; `ecall`
- Driver: `as -march=rv64imac -mno-relax`,
  `ld -Ttext=0x80000000 -nostdlib --no-relax`.

**Exit criteria.**
`lake exe codegen --program smoke --halt linux93 -o gen-out/smoke` produces
`gen-out/smoke.elf`; `ziskemu -e gen-out/smoke.elf` exits 0. Direct
verification that `a2 = 100` is deferred to M2 when `write_output` is wired
— for M0 we only validate that the toolchain (emitter → `as` → `ld` →
`ziskemu`) round-trips and that the halt convention works.

**Status (2026-05-18, resolved).** Toolchain validated end-to-end on
macOS 26 with Homebrew `riscv64-elf-binutils` and ZisK v0.18.0. The
SP1-vs-`ziskemu` halt experiment §Tricky bits #5 below is answered:
**`ziskemu` honors `linux93` (`ecall` + `a7 = 93`) and ignores `sp1`
(`ecall` + `t0 = 0`)**. `--halt linux93` is therefore the default for
generated ELFs; `--halt sp1` remains correct against the verified `step`
semantics but produces an ELF that runs to `--max-steps` on `ziskemu`.

### M1 — Total coverage of `Instr` (S/M)

Make `emitInstr` total for every constructor in `EvmAsm/Rv64/Basic.lean:113-237`:

- Immediates: `BitVec 12`, `BitVec 6` → signed decimal (`.toInt`).
  `BitVec 20` (LUI/AUIPC) → unsigned hex. `LI`'s `Word` → 64-bit signed `Int`
  literal — `as` handles the lowering to `lui`+`addiw`+`slli`+`addi`.
- Branches (`BEQ`, …, `JAL`) emit numeric byte offsets in M1; labels arrive in M3.
- `MV`, `NOP`, `FENCE`, `ECALL`, `EBREAK` pass through as their canonical mnemonics.
- Add `EvmAsm/Codegen/RoundTripTests.lean` — `#guard` examples covering each
  constructor once (e.g. `emitInstr (.SLTU .x5 .x7 .x6) = "sltu x5, x7, x6"`).

**Exit criteria.**
`lake exe codegen --program evm_add --asm-only` emits assembly that
`riscv64-unknown-elf-as -march=rv64imac` accepts cleanly; round-trip tests
pass under `lake build`.

### M2 — End-to-end `evm_add` (M) — **DONE (2026-05-18)**

Wire enough memory and registers so the verified `evm_add` program
(`EvmAsm/Evm64/Add/Program.lean`) computes a 256-bit sum on `ziskemu`.

**Delivered:**
- `BuildUnit` struct in `EvmAsm/Codegen/Layout.lean`: a verified
  `Program` body alongside optional raw-asm prologue, epilogue, and
  `.data` section. `emitBuildUnit` composes them into the full `.s`.
- `evm_add` wrapping in `EvmAsm/Codegen/Programs.lean`:
  - `.data` section with two 256-bit operands as eight LE doublewords.
  - Prologue (raw text, because `la` is a GNU-as pseudo not in our
    `Instr`): `la x12, operands`.
  - Body: `EvmAsm.Evm64.evm_add ++ evmAddEpilogue` where the 9-instr
    epilogue is itself a verified `Program` — every instruction lives
    in `Instr` and goes through the same totalized `emitInstr` and
    `#guard` round-trip tests as the body.
- `Driver.lean` adds `-Tdata=0xa0000000` to the link step so writable
  `.data` lands in `ziskemu`'s RAM region (`0xa0000000–0xc0000000`);
  without this, the emulator refuses the ELF with
  *"writable data section … outside RAM bounds"*.
- `scripts/codegen-evm_add-check.sh` builds, emits, links, runs, and
  diffs the first 32 bytes of `ziskemu`'s `-o` output against the
  expected 4-limb sum. **PASSES** with the M2 test case
  `A = 2^64-1, B = 1 → sum LE = [0, 1, 0, 0]`.

**Empirical surprise — `write_output` is memory-mapped, not an ecall.**
ziskemu does NOT honor the zkvm-standards `ecall + t0=0x10` write_output
syscall (the verified `step` semantics in
`EvmAsm/Rv64/Execution.lean:411` do). Instead, the public-output region
is memory-mapped at `OUTPUT_ADDR = 0xa001_0000` (constant from
`zisk/ziskos/entrypoint/src/ziskos_definitions.rs`). Guest writes u32
slots there directly; ziskemu's `-o <file>` dumps the full 256-byte
region. `MAX_OUTPUT = 0x1_0000` (64 KB) per the same file but the
default dump is `64 × 4 = 256` bytes. This mirrors the SP1/linux93
halt-convention split — the verified semantics target a different host
than ziskemu — and is now folded into M4's scope.

**Exit criteria (met).**
`ziskemu -e gen-out/evm_add.elf` halts and the post-state limbs equal
the `Word`-level sum. `scripts/codegen-evm_add-check.sh` exits 0.

### M3 — Labels (deferred)

Originally planned as two-pass emission rewriting numeric branch/jal offsets
into `Lk`-style labels. **Deferred**: the verified `Program`s in this repo
already carry branch/JAL offsets as explicit `BitVec 13` / `BitVec 21` byte
counts (see e.g. `EvmAsm/Rv64/Program.lean:104-110`); there are no symbolic
labels to resolve at codegen time, so emitting numeric offsets is exact and
readable enough through M2. Pick this milestone back up only if (a) a
verified Program starts using a symbolic branch target we'd otherwise have
to hand-compute, or (b) the M5 interpreter emission becomes unreadable
without labels.

**Exit criteria (if revisited).**
A `Program` containing a backward branch builds with `Lk`-style labels;
`riscv64-elf-objdump -d` shows the same encoded offsets as the
`--no-labels` build.

### M4 — `read_input` / `write_output` plumbing, including hint inputs (M) — **DONE (2026-05-18)**

The original M4 plan expected `read_input` (`t0 = 0xF2`) and
`write_output` (`t0 = 0x10`) to be ECALL syscalls (per the verified
`step` semantics in `EvmAsm/Rv64/Execution.lean:411,416`). M2 already
showed ziskemu uses memory-mapped output instead; M4 confirmed the
same for input. Both ECALL paths are ignored by ziskemu — everything
is memory-mapped.

**Empirical input layout** (determined by `input_echo` + a
known-pattern `ziskemu -i <file>`):
```
INPUT_ADDR + 0..8   = 8 bytes of ziskemu-side metadata (currently zero)
INPUT_ADDR + 8..16  = LE u64 length of the first record
                      (matches the first 8 bytes of the `-i` file)
INPUT_ADDR + 16..   = first record's data, packed verbatim from the
                      `-i` file after the length prefix
```
This matches `INPUT_INITIAL_OFFSET = 8` in the SDK
(`zisk/ziskos/entrypoint/src/lib.rs`).
`INPUT_DATA_OFFSET = 16` is captured as a constant in
`EvmAsm/Codegen/Programs.lean`.

**Delivered:**
- `input_echo` program: minimal probe that copies 32 bytes from
  `INPUT_ADDR + 0..32` to `OUTPUT_ADDR`, used to determine the layout
  above and as a permanent regression check.
- `copy64` Program helper (eight LE-dword load/store pairs).
- `evm_add_from_input`: same wrapping as `evm_add` but loads both
  256-bit operands at runtime from
  `INPUT_ADDR + INPUT_DATA_OFFSET`, copies them to a writable
  `.data` scratch region (`operands_ram`), runs the verified
  `evm_add` body, then writes the result via the existing
  `evmAddEpilogue`. Reuses everything from M2 — pure additive M4 work.
- `scripts/codegen-evm_add-from-input-check.sh`: builds, packs a
  72-byte input file (`8 B length || 32 B A || 32 B B`), runs
  `ziskemu -e ... -i ... -o ...`, diffs the first 32 bytes of public
  output against the expected `A + B` LE limbs. **PASSES** with the
  same test case as M2 (`A = 2^64-1, B = 1 → [0, 1, 0, 0]`),
  exercising the limb-0→limb-1 carry through the prover-input path.

**Hint inputs.** The mechanism is the *same* — both real public input
and prover-supplied non-deterministic hints share the single
`INPUT_ADDR` region; the convention is just that the prover packs
auxiliary witnesses (e.g. `(q, r)` for `DIV`) into the same
length-prefixed record after the public inputs. A full hint-driven
example will come when `evm_div` is wired into the registry; M4
infrastructure is in place to support it without further codegen
changes.

**Exit criteria (met).**
A `read_input → use → write_output → HALT` program consumes a
host-supplied input file and emits the expected bytes through
`ziskemu`'s output channel.

The `read_input` buffer carries **both** real public input **and**
prover-supplied non-deterministic hints — under the zkvm-standards I/O
ABI there is only one input channel; the host concatenates everything the
guest will need into a single buffer, and the guest decodes a structured
header (lengths, offsets) to find each section. This is the same channel
through which the prover supplies precomputed witnesses for expensive
operations: e.g. for `DIV` the prover supplies `(q, r)` and the guest
verifies `q · d + r = n ∧ r < d` instead of running long division.

M4 therefore covers three closely related concerns that share the same
syscall surface:

1. **Reading prover input** — `read_input` syscall, ELF reserves
   `__input_buf` in `.bss`/`.data` at `inputBufBase`, exposed via an
   emitted linker script template. Codegen accepts `--input <file>` and
   passes it through to `ziskemu -i <file>`.
2. **Hint inputs** — a small Lean-side helper that lets a `Program`
   declare "I expect a hint at offset N of size M (e.g. the `(q, r)` pair
   for DIV)". Codegen lays out the buffer; the host-side companion (a
   Python or Rust script under `scripts/`) packs the hints in the right
   order. Tracks the zkvm-standards hint conventions documented in
   `docs/zkvm-host-io-input-buffer-design.md`.
3. **Writing public output** — `write_output` syscall, used both by the
   smoke smoke-test (writing `a2`) and by the EVM interpreter (writing
   the final stack top / return data).

Cross-reference: the SP1-legacy streaming surface
(`HINT_LEN`/`HINT_READ`/`COMMIT`) has been retired from the Lean code; we
target only the zkvm-standards single-buffer shape.

**Exit criteria.**
- `evm_div` (when implemented) consumes a prover-supplied `(q, r)` hint
  from `read_input` and writes the verified quotient via `write_output`.
- An end-to-end `scripts/codegen-div-check.sh` packs an input, runs
  `ziskemu -i ...`, and diffs the public output against the expected
  value computed in Lean.

### M5 — Tiny EVM interpreter (L) — **DONE (2026-05-19)**

Split into two slices. **M5a** unrolls verified opcode `Program`s as a
linear chain (no runtime dispatch) to validate that the handlers
compose under `++` honoring the `x10` code-pointer convention.
**M5b** codegens the actual fetch/decode/dispatch loop from
`EvmAsm/Evm64/InterpreterLoop.lean` + `EvmAsm/Evm64/Dispatch.lean`.

#### M5a — Unrolled tiny interpreter (S) — **DONE (2026-05-19)**

Chain verified opcode `Program`s end-to-end for two hand-picked
bytecodes, no runtime dispatch. Each opcode handler reads its
operands from the conventional registers (`x10` = EVM code pointer,
`x12` = EVM stack pointer); a one-instruction `advancePc` between
handlers does the dispatcher's PC-update job inline.

**Delivered:**
- `advancePc (off : Nat) : Program` helper in
  `EvmAsm/Codegen/Programs.lean` — a single `ADDI .x10 .x10 off`
  emitted between unrolled opcode handlers. Stays in the verified
  `Program` world, so the existing `RoundTripTests.lean` already
  covers it.
- `tinyInterpAdd` / `tinyInterpAdd2` `Program`s composing
  `EvmAsm.Evm64.evm_push 1`, `EvmAsm.Evm64.evm_add`, and `advancePc`
  via `++`. STOP is handled by fall-through to the halt stub — no
  RISC-V `Program` body needed in the unrolled chain.
- `tinyInterpPrologue` + `tinyInterpDataSection` lay out the EVM
  bytecode bytes as `.byte` directives under label `evm_code`,
  followed by 256 bytes of writable scratch ending at label
  `evm_stack_top`. Prologue initializes `x10 = &evm_code` and
  `x12 = &evm_stack_top`.
- Two `BuildUnit`s (`tinyInterpAddUnit`, `tinyInterpAdd2Unit`)
  registered in `lookupProgram` and `knownProgramNames`. Both reuse
  the existing `evmAddEpilogue` for the result-to-`OUTPUT_ADDR` copy.
- `scripts/codegen-tiny-interp-check.sh`: builds, emits, links, runs
  both ELFs on `ziskemu`, and diffs the first 32 bytes of public
  output against the expected LE limbs. **PASSES** for both test
  programs.

**Test cases.**
- `tiny_interp_add`: `PUSH1 0xFF; PUSH1 0x01; ADD; STOP`
  → expected `[0x100, 0, 0, 0]` (first 8 bytes `00 01 00 00 00 00 00 00`).
- `tiny_interp_add2`: `PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP`
  → expected `[0x60, 0, 0, 0]` (first 8 bytes `60 00 00 00 00 00 00 00`).
  Exercises chained ADDs and a stack pointer that walks back up after
  each `evm_add`.

**Exit criteria (met).**
`scripts/codegen-tiny-interp-check.sh` exits 0; `riscv64-elf-objdump
-d` shows the inline `addi a0, a0, N` advances between unrolled opcode
handler bodies.

#### M5b — Runtime fetch/decode/dispatch loop (M) — **DONE (2026-05-19)**

A real fetch/decode/dispatch loop in RISC-V, with verified opcode
`Program`s wrapped one-by-one in subroutines. Per §Tricky bits #9
("Codegen is not verified") the loop scaffold lives as raw asm; only
the opcode bodies remain verified.

**Delivered:**
- `opcodeHandlerLabel : Nat → String` + `emitOpcodeHandlerTable`
  in `EvmAsm/Codegen/Programs.lean`: render a 256-entry jump table
  in `.data` mapping each opcode byte to a handler label. Unhandled
  bytes route to `h_invalid`.
- `tinyInterpDispatchPrologue` — `_start` init (`la x10, evm_code`,
  `la x12, evm_stack_top`) followed by `.dispatch_loop:`:
    ```
    lbu  x5, 0(x10)              # fetch opcode byte
    la   x6, opcode_handlers
    slli x5, x5, 3               # opcode * 8 (entry stride)
    add  x6, x6, x5
    ld   x7, 0(x6)               # load handler address
    jalr x1, x7, 0               # call handler
    j    .dispatch_loop
    ```
- `tinyInterpDispatchEpilogue` — handler subroutines + exit path:
  - `h_PUSH1`: `<emitProgram (evm_push 1)>` + `addi x10, x10, 2` + `ret`
  - `h_ADD`:   `<emitProgram evm_add>`     + `addi x10, x10, 1` + `ret`
  - `h_STOP`:  `j .exit_label` (no return to dispatcher)
  - `h_invalid`: `j .exit_label` (same exit path as STOP for this slice)
  - `.exit_label`: `<emitProgram evmAddEpilogue>` — falls through to
    the linux93 halt stub appended by `emitBuildUnit`.
- Two `BuildUnit`s (`tinyInterpDispatchAddUnit`,
  `tinyInterpDispatchAdd2Unit`) registered in `lookupProgram` and
  `knownProgramNames`. They reuse `tinyInterpAddBytecode` /
  `tinyInterpAdd2Bytecode` verbatim, so M5a and M5b run on identical
  inputs and produce identical expected outputs — any regression is
  isolated to the dispatcher.
- `scripts/codegen-tiny-interp-dispatch-check.sh` mirrors the M5a
  script and runs both dispatch units. **PASSES** for both bytecodes
  with `-n 200000` step budget.

**Calling convention (informal).** `x10` (EVM code pointer) is
preserved across handler calls; each handler wrapper advances it by
the opcode's byte width before returning. `x12` (EVM stack pointer)
is updated freely by handlers and persists across the loop. `x1` is
the standard return address. The dispatcher reloads its scratch
(`x5`, `x6`, `x7`) from `x10` and the jump-table base every
iteration, so the fact that verified handlers clobber them
(`evm_add` uses `x5`/`x6`/`x7`/`x11`) is by design.

**Layout note.** `evm_stack_top` and `opcode_handlers` end up at
the same address (no `.balign` padding needed since the stack
region already lands on an 8-byte boundary). Safe at the worst-case
depth of 2 (= 64 bytes) for both test programs, but worth flagging
if M5c expands to deeper bytecodes — give the stack its own
explicit reserved tail before the jump table.

**Exit criteria (met).**
`scripts/codegen-tiny-interp-dispatch-check.sh` exits 0; both M5a
and M5b produce identical bytes through `ziskemu`'s public output.

### M6a — Opcode registry + test harness (S/M) — **DONE (2026-05-20)**

Pure-infrastructure refactor of M5b's hand-written dispatcher
scaffolding into a declarative registry, plus a generic per-opcode
test harness. Zero behavior change: M5a, M5b, and M2 scripts all
still pass; the dispatcher emits the same handler subroutines in
the same order.

**Delivered:**
- New `EvmAsm/Codegen/Dispatch.lean`: `OpcodeHandlerSpec` struct
  (`label`, `opcodes : List Nat`, `body : Program`, `tail :
  HandlerTail`) plus `emitDispatcherPrologue / Epilogue /
  DataSection` helpers that consume `List OpcodeHandlerSpec`.
  `buildDispatchUnit` produces a complete `BuildUnit` from a
  registry, an exit body (`evmAddEpilogue`), and a bytecode payload.
- `EvmAsm/Codegen/Programs.lean` M5b section is now a 3-entry
  registry (`tinyInterpRegistry`):
    ```lean
    [ { label := "h_PUSH1"; opcodes := [0x60]; body := evm_push 1; tail := .advanceAndRet 2 }
    , { label := "h_ADD"  ; opcodes := [0x01]; body := evm_add    ; tail := .advanceAndRet 1 }
    , { label := "h_STOP" ; opcodes := [0x00]; body := []         ; tail := .custom "  j .exit_label" } ]
    ```
  Adding an opcode now = adding one record.
- New `EvmAsm/Codegen/Tests/Cases.lean`: `OpcodeTestCase` struct
  (`name`, `bytecode`, `expectedOutHex`) + `opcodeTestCases : List
  OpcodeTestCase` registry. Two M5b bytecodes migrated as
  `add_basic` / `add_chain`. `lookupTestCase` + `buildTestCaseUnit`
  let the CLI emit any case via the M5b dispatcher.
- `EvmAsm/Codegen/Cli.lean` extended with `--test-case <name>` and
  `--list-test-cases`. The list flag emits TSV (`name\thex`) so the
  bash runner reads expected outputs straight from Lean — single
  source of truth, no hex duplication.
- `scripts/codegen-opcodes-check.sh`: portable (bash 3.2-safe)
  runner. Calls `--list-test-cases`, iterates, emits + runs + diffs.
  Adding a regression test = appending one record to
  `opcodeTestCases`.

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 (both migrated cases
pass); `scripts/codegen-tiny-interp{,-dispatch}-check.sh` continue
to exit 0; M2/M4 scripts unchanged.

### M6b — Mass wire-up of fixed-shape opcodes (M) — **DONE (2026-05-20)**

Bring M5b dispatcher coverage from 3 → 82 opcodes by registering
every verified handler that matches the standard ABI (`<body>` +
`addi x10, x10, width` + `ret`). Pure registry expansion against
M6a's infrastructure; the dispatcher scaffolding (loop, jump table,
exit path) is unchanged from M6a.

**Delivered:**
- `EvmAsm/Codegen/Programs.lean` `tinyInterpRegistry` now composed
  from four builders:
  - `pushHandlers` — PUSH0..PUSH32 (33 entries, opcode bytes
    `0x5f + n`, tail `.advanceAndRet (1 + n)`).
  - `dupHandlers` — DUP1..DUP16 (16 entries, opcode bytes
    `0x7f + n`, tail `.advanceAndRet 1`).
  - `swapHandlers` — SWAP1..SWAP16 (16 entries, opcode bytes
    `0x8f + n`, tail `.advanceAndRet 1`).
  - `singletonHandlers` — 17 fixed-shape singletons: ADD, MUL, SUB,
    SIGNEXTEND, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT,
    BYTE, SHR, POP.
  Plus `stopHandler` for STOP. Total: 33 + 16 + 16 + 17 + 1 =
  **83 wired opcodes**; remaining 173 bytes fall to `h_invalid`.
- **`OpcodeHandlerSpec.preBody : String`** added in
  `EvmAsm/Codegen/Dispatch.lean`. Used to inject raw asm between
  the handler's label and verified body. Required because four
  verified bodies (`evm_mul`, `evm_signextend`, `evm_byte`,
  `evm_shr`) use `x10` as a scratch accumulator, which clobbers
  our dispatcher's preserved EVM code pointer. Those handlers
  carry `preBody := "  mv x9, x10"` to stash the code pointer in
  `x9` (a register no verified opcode body touches) and a
  `x10RestoreAdvance1` tail that restores it before the standard
  advance + ret. Discovered empirically when `mul_basic` panicked
  ziskemu with `Mem::read() section not found for addr: 1` — the
  `addi x10, x10, 1` after `MULHU .x10 ...` landed at address 1.
- **`EvmAsm/Codegen/Tests/Cases.lean`** grew from 2 to 22 cases:
  16 singleton tests (one per opcode), 3 family representatives
  (`push32_basic`, `dup1_basic`, `swap1_basic`), one `arith_mix`
  kitchen sink, plus the two M6a baseline cases (`add_basic`,
  `add_chain`).

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 with all 22 cases
PASS; `scripts/codegen-tiny-interp{,-dispatch}-check.sh`,
`codegen-smoke.sh`, and `codegen-evm_add-check.sh` continue to
exit 0; full M6b suite runs in ~48 s (under the 60 s threshold
for considering the runtime-bytecode optimization).

### M7 — Memory opcodes (S/M) — **DONE (2026-05-20)**

Wires MLOAD / MSTORE / MSTORE8 into `tinyInterpRegistry`. First
milestone needing infrastructure beyond a stack-only ABI: the
dispatcher prologue now initialises a third persistent register
(`x13` = EVM memory base) alongside `x10` (code pointer) and `x12`
(stack pointer). MSIZE is deferred — the verified core doesn't
yet bookkeep memory expansion (`evmMemSizeIs` lives outside the
verified `Program`s; see `docs/99-mload-design.md` §4 and the
`evm_mload` docstring).

**Delivered:**
- `EvmAsm/Codegen/Dispatch.lean` — `emitDispatcherPrologue` adds
  `la x13, evm_memory`. `emitDispatcherDataSection` now declares
  a 32 KiB `evm_memory:` `.zero` block between `evm_stack_top:`
  and `opcode_handlers:`.
- `EvmAsm/Codegen/Programs.lean` — new `memoryHandlers` list with
  three entries:
    - `h_MLOAD` (0x51): `evm_mload .x15 .x16 .x17 .x18 .x13`
    - `h_MSTORE` (0x52): `evm_mstore .x15 .x14 .x16 .x17 .x18 .x13`
    - `h_MSTORE8` (0x53): `evm_mstore8 .x15 .x14 .x18 .x13`
  All three use `.advanceAndRet 1` — no `preBody` needed (none
  touch `x10`). MSTORE / MSTORE8's internal `ADDI .x12 .x12 64`
  handles the stack shrink.
- `EvmAsm/Codegen/Tests/Cases.lean` — two new cases
  (`mstore_mload`, `mstore8_basic`). Total now 24.

**Register convention.**
- `x10` = EVM code pointer (preserved across handlers)
- `x12` = EVM stack pointer (handlers update freely)
- `x13` = EVM memory base, init'd in dispatcher prologue (new in M7)
- `x14, x15, x16, x17, x18` = caller-saved scratch for memory handlers

**`.data` budget.**
The dispatcher's `.data` section starts at `0xa0000000` and must
stay under `0xa0010000` (= `OUTPUT_ADDR`). Post-M7 layout: ~50 B
bytecode + 256 B stack scratch + 32 KiB EVM memory + 2 KiB jump
table ≈ 35 KiB. Comfortably under the 64 KiB cap. A future
milestone that needs > 32 KiB of EVM memory should either grow
the budget (extending `.data` is bounded by `OUTPUT_ADDR`) or
relocate `evm_memory` to a separate section linked above
`OUTPUT_ADDR + 0x10000`.

**Exit criteria (met).**
`scripts/codegen-opcodes-check.sh` exits 0 with all 24 cases
PASS; legacy scripts (`codegen-tiny-interp{,-dispatch}-check.sh`,
`codegen-smoke.sh`, `codegen-evm_add{,-from-input}-check.sh`,
`codegen-evm_div{,-cases}-check.sh`, `codegen-evm_mod{,-cases}-check.sh`)
all still exit 0. Full M7 suite runs in **~57 s** — just under
the 60 s threshold; the next milestone that materially grows the
dispatcher ELF should consider the runtime-bytecode optimization.

### Sequencing

M0 ✅ → M1 ✅ → M2 ✅ → M4 ✅ → M5a ✅ → M5b ✅ → M6a ✅ → M6b ✅ → M7 ✅.
M3 is deferred; revisit only if a future milestone (full opcode
coverage, JUMP/JUMPI, or the binary encoder) makes label-free
emission unreadable. M7 unblocks M8 (hint-dependent opcodes
through the dispatcher) and any non-trivial EVM bytecode that
exercises memory.

## Tricky bits / open questions

1. **`LI rd, imm64` lowering.** `as` chooses 1–8 instructions to materialize a
   64-bit constant. The verified specs assume specific PC arithmetic — for the
   text-first path this is fine because we never re-derive PCs at the bit
   level. The future binary encoder will need to reproduce `as`'s expansion
   exactly (or use its own).
2. **`MV`, `NOP`, `FENCE`** are accepted verbatim by `as`. No manual lowering.
3. **Branch encoding sanity.** M1 emits numeric byte offsets via `.toInt` on
   `BitVec 13`/`BitVec 21`. M3's label path is for readability; verify the
   encoded bytes match the numeric path with `objdump`.
4. **`.option norvc`** at every unit head — keeps `as` from emitting 2-byte
   compressed encodings. Required for predictable PC layout and for the future
   binary encoder.
5. **SP1 `t0=0` vs `ziskemu` HALT — RESOLVED (2026-05-18).** The verified
   `step` halts on `t0=0` (`EvmAsm/Rv64/Execution.lean:611-615`), but
   `ziskemu`'s stock examples use `a7=93`. M0 ran the experiment with
   ZisK v0.18.0 on macOS 26: **`ziskemu` halts cleanly on `linux93`
   (`ecall` + `a7=93`) and ignores `sp1` (`ecall` + `t0=0`)** — the SP1
   variant runs to `--max-steps` and errors with `EmulationNoCompleted`.
   `--halt linux93` is the codegen default; `--halt sp1` is kept for
   anyone proving against the SP1 step semantics directly.
   `docs/host-io-halt-convention.md` remains the canonical ADR.
6. **Memory bounds.** Emitted ELFs must respect
   `MEM_START=0x20` / `MEM_END=0x78000000`. Codify in `Codegen/Layout.lean` so
   the constants can't drift from `EvmAsm/Rv64/Basic.lean:244,247`.
7. **No `read_input` in M0.** Deferred to M4. M0/M1/M2 use hardcoded values
   (smoke) or `.data` seeding (`evm_add`).
8. **Toolchain availability.** Gate the assemble/link step behind a feature
   check; CI without `riscv64-unknown-elf-as` still runs `--asm-only` to catch
   emitter regressions.
9. **Codegen is not verified.** It's an output channel, not part of the trusted
   kernel surface. The `native_decide` / `bv_decide` restrictions in
   [`CLAUDE.md`](CLAUDE.md) and [`AGENTS.md`](AGENTS.md) do not apply because
   the codegen code carries no proofs.

## Verification (per milestone)

- **M0.** `ziskemu -e gen-out/smoke.elf` exits 0 (validated 2026-05-18 with
  ZisK v0.18.0). Both halt modes exercised; result of the SP1/`ziskemu`
  experiment recorded in §Tricky bits #5 above. Direct `a2 = 100`
  verification is deferred to M2 (needs `write_output` wiring).
- **M1.** `lake build` passes (includes `RoundTripTests.lean`);
  `lake exe codegen --program evm_add --asm-only | riscv64-unknown-elf-as -march=rv64imac -o /dev/null -`
  returns 0.
- **M2.** ✅ `scripts/codegen-evm_add-check.sh` exits 0 (validated
  2026-05-18). Test case `A = 2^64-1, B = 1 → sum LE = [0, 1, 0, 0]`
  exercises the limb-0→limb-1 carry.
- **M3.** `diff <(codegen --no-labels … | as | objdump -d) <(codegen … | as | objdump -d)`
  shows only label-noise differences.
- **M4.** ✅ `scripts/codegen-evm_add-from-input-check.sh` exits 0
  (validated 2026-05-18). Same operands and expected sum as M2, but
  loaded at runtime from `ziskemu -i <file>` instead of `.data`.
- **M5a.** ✅ `scripts/codegen-tiny-interp-check.sh` exits 0
  (validated 2026-05-19). Two unrolled bytecodes
  (`PUSH1; PUSH1; ADD; STOP` and `PUSH1; PUSH1; ADD; PUSH1; ADD; STOP`)
  round-trip through verified opcode `Program`s chained with
  `advancePc`.
- **M5b.** ✅ `scripts/codegen-tiny-interp-dispatch-check.sh` exits 0
  (validated 2026-05-19). Same two bytecodes as M5a, but routed
  through a 256-entry jump table + handler subroutines (`jalr ra,
  …`) instead of an unrolled chain. Output bytes match M5a's, which
  cross-checks the dispatcher against the unrolled reference.
- **M6a.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 (validated
  2026-05-20). Generic harness driven by Lean-declared
  `opcodeTestCases`; the two M5b bytecodes (`add_basic`,
  `add_chain`) migrated as the seed regression suite. `--list-test-cases`
  emits TSV with expected outputs so the bash runner stays in sync
  with `Tests/Cases.lean` automatically.
- **M6b.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 with **22
  test cases** PASS (validated 2026-05-20). 83 opcodes wired through
  `tinyInterpRegistry`: PUSH0..32, DUP1..16, SWAP1..16, plus 17
  fixed-shape singletons (ADD, MUL, SUB, SIGNEXTEND, LT, GT, SLT,
  SGT, EQ, ISZERO, AND, OR, XOR, NOT, BYTE, SHR, POP) and STOP.
  Four handlers that clobber `x10` (MUL, SIGNEXTEND, BYTE, SHR)
  use the new `OpcodeHandlerSpec.preBody` field to save the EVM
  code pointer in `x9` before the body and restore it in the tail.
- **M7.** ✅ `scripts/codegen-opcodes-check.sh` exits 0 with **24
  test cases** PASS (validated 2026-05-20). Three memory opcodes
  wired (MLOAD, MSTORE, MSTORE8) plus a 32 KiB `evm_memory:`
  `.data` region and `x13` = memory-base in the dispatcher prologue.
  MSIZE deferred pending verified memory-expansion bookkeeping.
  Suite runtime: ~57 s (just under the 60 s threshold).

## Future work (post-M7)

Near-term (builds directly on M6a's registry; no new design surface):
- **M8 — hint-input demo via `evm_div` / `evm_mod`.** Closes the loop
  on M4's prover-hint infrastructure. The standalone `evm_div` /
  `evm_mod` wrappers in `Programs.lean` already exercise the
  hint-input path end-to-end through ziskemu (with `evm_div_from_input`
  / `evm_mod_from_input`); M8 routes them through the dispatcher
  instead, so the same bytecode that runs ADD can also run DIV.
  Likely needs a `callableLabel?` extension to `OpcodeHandlerSpec`
  to expose distinct entry points for opcodes that are also
  near-called from within other handlers.

Longer-term (genuine new design surface):

- **JUMP / JUMPI + JUMPDEST table.** Real control flow. Handlers must
  write `x10` directly (the wrapper baking in a fixed advance no longer
  works) and JUMP/JUMPI need to consult a JUMPDEST validity table built
  from the bytecode at codegen time.
- **Lean-native binary encoder** (`Instr → BitVec 32` + ELF writer) to
  drop the GNU binutils dependency. Cross-check the encoded bytes
  against the verified `step` semantics.
- **STF integration**: consume RLP-decoded transactions via `read_input`
  and drive the full interpreter loop.
- **Precompile stubs** aligned with
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators`.
- **Cross-zkVM testing** (SP1, RISC0) to validate the halt-convention
  ADR closure described in
  [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md).

## References

- [Zisk emulator quickstart](https://0xpolygonhermez.github.io/zisk/getting_started/quickstart.html)
- [Zisk ELF regressions](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
- [Zisk `simple_add` example](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s)
- [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md) — I/O ABI ADR
- [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) — halt-convention ADR (Open)
- [`docs/zkvm-host-io-input-buffer-design.md`](docs/zkvm-host-io-input-buffer-design.md) — input-buffer design
