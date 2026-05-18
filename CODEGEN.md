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
| `EvmAsm/Codegen/Layout.lean` | `HaltConv` enum, halt stub, `_start`, `.option norvc`, `MEM_START`/`MEM_END` constants. |
| `EvmAsm/Codegen/Programs.lean` | Registry: `"smoke"`, `"evm_add"`, `"interp_tiny"`, … → `Program`. |
| `EvmAsm/Codegen/Cli.lean` | Argument parsing (`--program`, `--halt`, `--out`, `--asm-only`). |
| `EvmAsm/Codegen/Driver.lean` | `IO`: shells out to `as`/`ld` if available; `--asm-only` for CI without the cross toolchain. |
| `Main.lean` | Already exists as `import EvmAsm`; extend to call `EvmAsm.Codegen.Cli.main`. |
| `lakefile.toml` | Add `[[lean_exe]] name = "codegen"; root = "Main"; supportInterpreter = true`. |
| `scripts/codegen-smoke.sh` | One-liner driving the M0 round-trip. |
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

### M4 — `read_input` / `write_output` plumbing, including hint inputs (M/L)

Match the verified `Execution.lean` syscall handlers:
- `t0 = 0xF2` → `read_input` (writes `(inputBufBase, privateInput.length)` to
  `[a0]`/`[a1]`). See `EvmAsm/Rv64/Execution.lean` ~line 416.
- `t0 = 0x10` → `write_output` (concatenating). See ~line 411.

**M4 must reconcile the syscall ABI with ziskemu's memory-mapped IO**
(see M2's empirical finding). Concretely: the verified `step` halts on
`t0 = 0x10` and appends to `publicValues`, but ziskemu reads its
public-output region at `OUTPUT_ADDR = 0xa001_0000` via plain stores
and ignores the syscall. A small adapter — either (a) a
`write_output_mm` Program in Lean that lowers the syscall to the
memory-mapped equivalent, or (b) a ziskemu-side shim that recognizes
`t0 = 0x10` — closes the gap. Input is presumably similar:
`INPUT_ADDR = 0x4000_0000`, with `MAX_INPUT = 0x2000` (8 KB), per
`zisk/ziskos/entrypoint/src/ziskos_definitions.rs`.

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

### M5 — Tiny EVM interpreter (L)

Codegen `EvmAsm/Evm64/InterpreterLoop.lean` + `EvmAsm/Evm64/Dispatch.lean` and
run small bytecodes (`PUSH1 a; PUSH1 b; ADD; STOP`, a two-op branch, …). A
reference oracle in Lean or Python diffs the expected stack against
`ziskemu`'s public output.

**Exit criteria.**
2–3 hand-picked bytecodes round-trip end-to-end against an oracle; smoke +
`evm_add` + tiny-interp all in a single CI-runnable script.

### Sequencing

M0 → M1 → M2 → M4 → M5. M3 is deferred (see above); revisit only if
M5 makes label-free emission unreadable. M4 unblocks M5.

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
- **M4.** End-to-end `read_input → write_output` test: prover input file in,
  expected bytes out via `ziskemu`.
- **M5.** Per-bytecode regression script under `scripts/`; each test compares
  `ziskemu`'s `write_output` against the reference oracle.

## Future work (post-M5)

- Lean-native binary encoder (`Instr → BitVec 32` + ELF writer) to drop the
  GNU binutils dependency. Cross-check the encoded bytes against the verified
  `step` semantics.
- STF integration: consume RLP-decoded transactions via `read_input` and drive
  the full interpreter loop.
- Precompile stubs aligned with
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators`.
- Cross-zkVM testing (SP1, RISC0) to validate the halt-convention ADR closure
  described in [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md).

## References

- [Zisk emulator quickstart](https://0xpolygonhermez.github.io/zisk/getting_started/quickstart.html)
- [Zisk ELF regressions](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions)
- [Zisk `simple_add` example](https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s)
- [`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md) — I/O ABI ADR
- [`docs/host-io-halt-convention.md`](docs/host-io-halt-convention.md) — halt-convention ADR (Open)
- [`docs/zkvm-host-io-input-buffer-design.md`](docs/zkvm-host-io-input-buffer-design.md) — input-buffer design
