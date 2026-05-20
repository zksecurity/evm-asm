/-
  EvmAsm.Codegen.Programs

  Registry of programs the codegen tool knows how to emit, each as a
  `BuildUnit` (verified body + optional wrapping).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## ZisK host-IO memory map

Both constants are mirrored from
`zisk/ziskos/entrypoint/src/ziskos_definitions.rs`. ZisK uses
memory-mapped I/O (not ECALL syscalls) for guest-↔-host data.

Empirical input layout (determined by `input_echo` + `ziskemu -i`):

```
INPUT_ADDR + 0..8   = 8 bytes of ziskemu-side metadata (currently zero)
INPUT_ADDR + 8..16  = LE u64 length of the first record
                      (matches the first 8 bytes of the `-i` file)
INPUT_ADDR + 16..   = first record's data, packed verbatim from the
                      `-i` file after the length prefix
```

Matches the SDK's `INPUT_INITIAL_OFFSET = 8` in
`ziskos/entrypoint/src/lib.rs`: the SDK skips those 8 bytes before
reading the first length-prefixed record.
-/

/-- ZisK private-input region. Bytes loaded from `ziskemu -i <file>`
    surface here at runtime. `MAX_INPUT = 0x2000` (8 KiB). -/
def INPUT_ADDR : Word := 0x40000000

/-- Byte offset within the `INPUT_ADDR` region where the first
    length-prefixed record's data starts: skip 8 bytes of ziskemu
    metadata + 8 bytes of u64 length prefix. -/
def INPUT_DATA_OFFSET : Nat := 16

/-- ZisK public-output region. Plain stores here at `OUTPUT_ADDR + 4·k`
    surface in `ziskemu`'s `-o <file>` and `-c` console log.
    `MAX_OUTPUT = 0x1_0000` (64 KiB) per the ABI but ziskemu's default
    `-o` dumps the first 256 bytes (64 × u32 slots). -/
def OUTPUT_ADDR : Word := 0xa0010000

/-! ## smoke — M0 toolchain validation -/

/-- M0 smoke target. Loads two immediates, adds them, falls through to the
    halt stub appended by `emitBuildUnit`. Expected post-state: `x12 = 100`.
    No memory setup or I/O needed; the post-state isn't observable from
    `ziskemu` until M2 wires `write_output`. -/
def smoke : Program :=
  LI .x10 (42 : Word) ;;
  LI .x11 (58 : Word) ;;
  ADD .x12 .x10 .x11

def smokeUnit : BuildUnit := { body := smoke }

/-! ## input_echo — M4 probe for ziskemu's `-i <file>` layout

    Copies 32 bytes from `INPUT_ADDR + 0..32` to `OUTPUT_ADDR + 0..32`.
    Used by `scripts/codegen-input-echo-probe.sh` to determine
    empirically where bytes from a `ziskemu -i <file>` invocation land:
    starting at `INPUT_ADDR + 0` (raw blob) or `INPUT_ADDR + 8` (after
    `INPUT_INITIAL_OFFSET`), and whether ziskemu prepends/skips a
    length prefix. -/
def input_echo : Program :=
  LI .x5 INPUT_ADDR ;;
  LI .x6 OUTPUT_ADDR ;;
  LD .x7 .x5 0  ;; SD .x6 .x7 0  ;;
  LD .x7 .x5 8  ;; SD .x6 .x7 8  ;;
  LD .x7 .x5 16 ;; SD .x6 .x7 16 ;;
  LD .x7 .x5 24 ;; SD .x6 .x7 24

def inputEchoUnit : BuildUnit := { body := input_echo }

/-! ## evm_add — M2 first verified-body end-to-end -/

/-- Operand A as four little-endian 64-bit limbs (low limb first).
    Chosen so the test exercises the limb-0→limb-1 carry: A = 2^64 - 1. -/
def evmAddOperandA : List UInt64 := [0xFFFFFFFFFFFFFFFF, 0, 0, 0]

/-- Operand B as four little-endian 64-bit limbs (low limb first).
    B = 1. -/
def evmAddOperandB : List UInt64 := [0x1, 0, 0, 0]

/-- Expected 256-bit sum, also four LE 64-bit limbs.
    A + B = 2^64, which means limb 0 = 0 and limb 1 = 1, others 0. -/
def evmAddExpectedSum : List UInt64 := [0x0, 0x1, 0, 0]

/-- evm_add expects `x12` to point at 64 bytes of memory: the 32-byte
    operand A at offset 0..32 and operand B at offset 32..64. After it
    runs, `x12` has been advanced by 32 and points at the 32-byte sum
    that overwrote operand B's slot.

    `la x12, operands` is a GNU-as pseudo that expands to
    `auipc x12, %hi(operands)` + `addi x12, x12, %lo(operands)` —
    PC-relative, resolved by the linker after the `.data` section's
    address is known. We keep it as raw asm text because `la` isn't in
    our `Instr` enum. -/
def evmAddPrologue : String :=
  "  la x12, operands"

/-- Copy the 32-byte sum from `mem[x12 .. x12+32]` into ZisK's public
    output region (`OUTPUT_ADDR .. OUTPUT_ADDR+32`). Plain 64-bit
    stores; no syscall (ZisK output is memory-mapped, not ecall-based).

    Lives in the verified Program world: every instruction is in
    `Instr`, so it benefits from `emitInstr` totality and the round-trip
    tests. -/
def evmAddEpilogue : Program :=
  LI .x5 OUTPUT_ADDR ;;
  LD .x6 .x12 0  ;; SD .x5 .x6 0  ;;
  LD .x6 .x12 8  ;; SD .x5 .x6 8  ;;
  LD .x6 .x12 16 ;; SD .x5 .x6 16 ;;
  LD .x6 .x12 24 ;; SD .x5 .x6 24

/-- `.data` section seeded with A and B back-to-back, eight LE doublewords. -/
def evmAddDataSection : String :=
  emitDataLabel ".data" "operands" (evmAddOperandA ++ evmAddOperandB)

def evmAddUnit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_add ++ evmAddEpilogue
  prologueAsm := evmAddPrologue
  dataAsm     := evmAddDataSection
}

/-! ## evm_add_from_input — M4 prover-supplied operands -/

/-- Copy 64 bytes (8 little-endian dwords) from `mem[src]` to `mem[dst]`.
    Caller sets `dst` and `src`; `scratch` is clobbered. Lives in the
    verified `Program` world. -/
def copy64 (dst src scratch : Reg) : Program :=
  LD scratch src 0  ;; SD dst scratch 0  ;;
  LD scratch src 8  ;; SD dst scratch 8  ;;
  LD scratch src 16 ;; SD dst scratch 16 ;;
  LD scratch src 24 ;; SD dst scratch 24 ;;
  LD scratch src 32 ;; SD dst scratch 32 ;;
  LD scratch src 40 ;; SD dst scratch 40 ;;
  LD scratch src 48 ;; SD dst scratch 48 ;;
  LD scratch src 56 ;; SD dst scratch 56

/-- Same wrapping as `evmAddUnit`, but instead of seeding the two
    operands as `.data`, copy them in at runtime from the
    ziskemu-loaded input region (`INPUT_ADDR + INPUT_DATA_OFFSET`).

    Prologue (raw text, since `la` is a pseudo): `la x12, operands_ram`.
    Body: load `INPUT_ADDR + 16` into x5, copy 64 bytes to RAM
    pointed at by x12, run `evm_add`, then `evmAddEpilogue` writes
    the 32-byte sum to `OUTPUT_ADDR`.

    The 64-byte scratch region is a `.data` section reserved as eight
    zero doublewords; ziskemu's loader places `.data` in RAM at
    `0xa0000000` (per `-Tdata=0xa0000000` in `Driver.lean`), so the
    region is writable. -/
def evm_add_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_add ++
  evmAddEpilogue

def evmAddFromInputPrologue : String :=
  "  la x12, operands_ram"

/-- 64 bytes of writable scratch RAM, label `operands_ram`,
    pre-initialized to zero. The runtime copy from INPUT overwrites it. -/
def evmAddFromInputDataSection : String :=
  emitDataLabel ".data" "operands_ram" (List.replicate 8 (0 : UInt64))

def evmAddFromInputUnit : BuildUnit := {
  body        := evm_add_from_input
  prologueAsm := evmAddFromInputPrologue
  dataAsm     := evmAddFromInputDataSection
}

/-! ## tiny_interp — M5a unrolled tiny EVM interpreter

    Two hand-picked EVM bytecodes laid out as `.data` bytes, executed
    by *chaining* verified opcode `Program`s with explicit `x10`
    advances between handlers. No runtime fetch/decode/dispatch loop
    (deferred to M5b). The point is to validate that verified opcode
    Programs compose under `++` while honoring the `x10` code-pointer
    convention that `evm_push` reads its immediates from.

    Stack layout: 256 bytes of writable scratch ending at label
    `evm_stack_top`. The EVM stack grows downward; the prologue
    initializes `x12 = evm_stack_top` and each `evm_push` decrements
    `x12` by 32 to allocate a new slot. Worst-case depth across both
    test programs is 2 slots = 64 bytes, so 256 leaves comfortable
    headroom. -/

/-- Dispatcher glue between unrolled opcode `Program`s: advance the
    EVM code pointer (`x10`) by the byte width of the opcode just
    executed (`1 + n` for `PUSHn`, `1` for `ADD`/`STOP`).

    In the M5b full dispatch loop this advance is computed inside the
    decoder; M5a inlines it directly so chained verified Programs read
    their PUSH immediates from the right byte. Stays in the verified
    `Program` world. -/
def advancePc (off : Nat) : Program :=
  ADDI .x10 .x10 (BitVec.ofNat 12 off)

/-- Prologue shared by all tiny-interp units. `la x10, evm_code`
    points the EVM code pointer at the start of the bytecode; `la
    x12, evm_stack_top` initializes the EVM stack pointer at the
    high-address end of a 256-byte writable scratch region. -/
def tinyInterpPrologue : String :=
  "  la x10, evm_code\n" ++
  "  la x12, evm_stack_top"

/-- `.data` section: a label `evm_code` holding the bytecode bytes,
    followed by 256 bytes of writable scratch ending at label
    `evm_stack_top`. `bytecodeBytes` is a comma-separated `.byte`
    directive payload (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`).

    Written as raw asm text rather than `emitDataLabel` because the
    layout is hybrid (`.byte` payload for the bytecode, `.zero` for
    the stack scratch) — `emitDataLabel` only takes `UInt64` dwords. -/
def tinyInterpDataSection (bytecodeBytes : String) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:"

/-- M5a test case 1: `PUSH1 0xFF; PUSH1 0x01; ADD; STOP`. Expected
    256-bit sum = `0x100`, which as four LE u64 limbs is
    `[0x100, 0, 0, 0]` — first 8 bytes `00 01 00 00 00 00 00 00`.

    The chain is `Program ++ Program ++ ...`; each `advancePc`
    between opcode handlers is the only dispatcher glue. STOP needs
    no body — falling through to the halt stub appended by
    `emitBuildUnit` is equivalent. -/
def tinyInterpAdd : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd`: `60 ff 60 01 01 00`. -/
def tinyInterpAddBytecode : String :=
  "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"

def tinyInterpAddUnit : BuildUnit := {
  body        := tinyInterpAdd ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAddBytecode
}

/-- M5a test case 2: `PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD;
    STOP`. Expected sum = `0x60`, LE limbs `[0x60, 0, 0, 0]` — first
    8 bytes `60 00 00 00 00 00 00 00`. Exercises chained ADDs and a
    stack-pointer history that walks back up after each ADD. -/
def tinyInterpAdd2 : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd2`: `60 10 60 20 01 60 30 01 00`. -/
def tinyInterpAdd2Bytecode : String :=
  "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"

def tinyInterpAdd2Unit : BuildUnit := {
  body        := tinyInterpAdd2 ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAdd2Bytecode
}

/-! ## tiny_interp_dispatch — M5b runtime fetch/decode/dispatch loop

    Same EVM bytecodes as M5a, but routed through an actual RISC-V
    dispatch loop. The dispatcher scaffolding (loop body, 256-entry
    jump table, `h_invalid` fallback, `.exit_label`) now lives in
    `EvmAsm.Codegen.Dispatch`; this section declares only the opcode
    handler registry.

    **Adding a new opcode = adding one `OpcodeHandlerSpec` entry below.**

    Calling convention (informal):
      x10  EVM code pointer  (preserved across handler calls; each
                              handler with `tail := .advanceAndRet n`
                              advances `x10` by `n` before returning)
      x12  EVM stack pointer (handlers update freely; persistent
                              across the loop)
      x1   return address    (clobbered by `jalr ra, ...`; each
                              `advanceAndRet` handler ends in `ret`)
      x5, x6, x7   scratch   (clobbered by both the dispatcher's
                              fetch/lookup *and* the verified handler
                              bodies; the dispatcher reloads from x10
                              and the table base on every iteration,
                              so no preservation needed)

    Coverage (M6b): 81 opcodes wired —
      - **PUSH0..PUSH32** (33) via `pushHandlers`
      - **DUP1..DUP16** (16) via `dupHandlers`
      - **SWAP1..SWAP16** (16) via `swapHandlers`
      - **16 fixed-shape singletons** via `singletonHandlers`:
        SUB, MUL, SIGNEXTEND, AND, OR, XOR, NOT, LT, GT, SLT, SGT,
        EQ, ISZERO, BYTE, SHR, POP — each a parameter-free verified
        `Program` with the standard `<body>` + `addi x10, x10, 1` +
        `ret` ABI.
      - **STOP** via `stopHandler` (jumps to `.exit_label` instead
        of returning to the dispatcher).

    All other opcode bytes fall to `h_invalid` (emitted automatically
    by `emitDispatcherEpilogue`), which takes the same exit path as
    STOP. -/

/-- PUSH0..PUSH32. Opcode byte = `0x5f + n`; the handler advances
    `x10` by `1 + n` (one opcode byte + `n` immediate bytes). -/
def pushHandlers : List OpcodeHandlerSpec :=
  (List.range 33).map (fun n =>
    { label   := s!"h_PUSH{n}"
      opcodes := [0x5f + n]
      body    := EvmAsm.Evm64.evm_push n
      tail    := .advanceAndRet (1 + n) })

/-- DUP1..DUP16. Opcode byte = `0x7f + n` (so DUP1 = `0x80`);
    width 1. `evm_dup n` duplicates the n-th stack item (1-indexed
    from top) onto the top. -/
def dupHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_DUP{n}"
      opcodes := [0x7f + n]
      body    := EvmAsm.Evm64.evm_dup n
      tail    := .advanceAndRet 1 })

/-- SWAP1..SWAP16. Opcode byte = `0x8f + n` (so SWAP1 = `0x90`);
    width 1. `evm_swap n` swaps the top with the (n+1)-th stack
    item. -/
def swapHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_SWAP{n}"
      opcodes := [0x8f + n]
      body    := EvmAsm.Evm64.evm_swap n
      tail    := .advanceAndRet 1 })

/-- Tail used by handlers whose verified body clobbers `x10` (the
    EVM code pointer in our dispatcher convention). Restores `x10`
    from `x9` (saved via `preBody`), then advances by 1 and returns. -/
private def x10RestoreAdvance1 : HandlerTail :=
  .custom "  mv x10, x9\n  addi x10, x10, 1\n  ret"

/-- Fixed-shape singleton opcodes: parameter-free verified `Program`s
    that fit the standard `<body>` + `addi x10, x10, 1` + `ret` ABI.

    Four bodies (`evm_mul`, `evm_signextend`, `evm_byte`, `evm_shr`)
    use `x10` as an internal scratch / accumulator register, which
    clobbers our dispatcher's preserved EVM code pointer. They carry
    `preBody := "  mv x9, x10"` to stash x10 in x9 (a register no
    verified opcode body touches) and use `x10RestoreAdvance1` as
    the tail to restore before advancing. -/
def singletonHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_ADD"        , opcodes := [0x01], body := EvmAsm.Evm64.evm_add       , tail := .advanceAndRet 1 }
  , { label := "h_MUL"        , opcodes := [0x02], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_mul       , tail := x10RestoreAdvance1 }
  , { label := "h_SUB"        , opcodes := [0x03], body := EvmAsm.Evm64.evm_sub       , tail := .advanceAndRet 1 }
  , { label := "h_SIGNEXTEND" , opcodes := [0x0b], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_signextend, tail := x10RestoreAdvance1 }
  , { label := "h_LT"         , opcodes := [0x10], body := EvmAsm.Evm64.evm_lt        , tail := .advanceAndRet 1 }
  , { label := "h_GT"         , opcodes := [0x11], body := EvmAsm.Evm64.evm_gt        , tail := .advanceAndRet 1 }
  , { label := "h_SLT"        , opcodes := [0x12], body := EvmAsm.Evm64.evm_slt       , tail := .advanceAndRet 1 }
  , { label := "h_SGT"        , opcodes := [0x13], body := EvmAsm.Evm64.evm_sgt       , tail := .advanceAndRet 1 }
  , { label := "h_EQ"         , opcodes := [0x14], body := EvmAsm.Evm64.evm_eq        , tail := .advanceAndRet 1 }
  , { label := "h_ISZERO"     , opcodes := [0x15], body := EvmAsm.Evm64.evm_iszero    , tail := .advanceAndRet 1 }
  , { label := "h_AND"        , opcodes := [0x16], body := EvmAsm.Evm64.evm_and       , tail := .advanceAndRet 1 }
  , { label := "h_OR"         , opcodes := [0x17], body := EvmAsm.Evm64.evm_or        , tail := .advanceAndRet 1 }
  , { label := "h_XOR"        , opcodes := [0x18], body := EvmAsm.Evm64.evm_xor       , tail := .advanceAndRet 1 }
  , { label := "h_NOT"        , opcodes := [0x19], body := EvmAsm.Evm64.evm_not       , tail := .advanceAndRet 1 }
  , { label := "h_BYTE"       , opcodes := [0x1a], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_byte      , tail := x10RestoreAdvance1 }
  , { label := "h_SHR"        , opcodes := [0x1c], preBody := "  mv x9, x10", body := EvmAsm.Evm64.evm_shr       , tail := x10RestoreAdvance1 }
  , { label := "h_POP"        , opcodes := [0x50], body := EvmAsm.Evm64.evm_pop       , tail := .advanceAndRet 1 } ]

/-- STOP: transitions out of the dispatcher loop instead of returning
    to it. The body is empty; the dispatcher's `jalr` lands on
    `h_STOP:` which jumps to `.exit_label`. -/
def stopHandler : OpcodeHandlerSpec :=
  { label   := "h_STOP"
    opcodes := [0x00]
    body    := []
    tail    := .custom "  j .exit_label" }

/-- M5b dispatch registry. Order doesn't affect correctness — the
    256-entry jump table is built by `jumpTargetLabel`, which scans
    the list for a spec whose `opcodes` contains the byte. -/
def tinyInterpRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ singletonHandlers ++
  [stopHandler]

def tinyInterpDispatchAddUnit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAddBytecode

def tinyInterpDispatchAdd2Unit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAdd2Bytecode

/-! ## evm_div — M2 first DIV end-to-end through ziskemu

    NOTE: `evm_div` is not yet proven correct in Lean — the spec
    composition (Phase 2a, see bead `evm-asm-9iqmw`) is still in
    flight. The scripts under `scripts/codegen-evm_div*` provide
    empirical confirmation by running the codegen output on ziskemu.

    `evm_div` shares ADD's `x12`-points-at-operands convention: before,
    `x12 = sp` with dividend `a` at `sp+0..32` and divisor `b` at
    `sp+32..64`; after, the quotient lives at `sp+32..64` and `x12 = sp+32`.
    So `evmAddEpilogue` (which copies `[x12, x12+32)` to `OUTPUT_ADDR`)
    works unchanged for DIV.

    Unlike ADD, `evm_div` also uses scratch at "negative" offsets from
    `x12` — the body encodes them as the unsigned bit pattern of
    12-bit signed negatives (`3936..4088 ≡ -160..-8`). The `.data`
    layout therefore places a 256-byte zero-filled `div_scratch:` block
    *before* the `operands:` label so that `x12 - 160..-8` lands in
    writable RAM.

    `evm_div`'s body lays out main code, then a NOP "exit PC" at index
    267, then the 75-instruction `divK_div128_v4` subroutine. When the
    main path completes (via `divK_div_epilogue`'s JAL +24 to the NOP)
    it falls through into the subroutine instead of halting — and the
    codegen's halt stub, appended after the body, is unreachable. We
    splice the body to replace that NOP with `JAL .x0 +304`, which
    skips over the 75 subroutine instructions (75·4 + 4 = 304 bytes)
    and lands at the start of `evmAddEpilogue`. The in-loop callers of
    the subroutine still use the original `jal x2, +560` offsets, which
    remain correct because we only replaced the NOP, not the
    subroutine's position relative to its callers. -/

/-- `EvmAsm.Evm64.evm_div` with the NOP "exit PC" at internal index 267
    replaced by a forward JAL that skips the 75-instruction subroutine
    and lands at the instruction immediately following the body — i.e.
    the start of whatever `Program` is appended next (`evmAddEpilogue`
    in both DIV BuildUnits below). -/
def evmDivPatched : Program :=
  (EvmAsm.Evm64.evm_div : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div : List Instr).drop 268

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=2 cascade
    plus the normalize/loop path (not an early-exit). -/
def evmDivDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 2. -/
def evmDivDivisor : List UInt64 := [2, 0, 0, 0]

/-- Expected quotient = 2^64 / 2 = 2^63, LE limbs. The actual on-disk
    expected hex is asserted by `scripts/codegen-evm_div-check.sh`; this
    constant is documentation. -/
def evmDivExpectedQuotient : List UInt64 := [0x8000000000000000, 0, 0, 0]

/-- Same `la x12, operands` as ADD — points the EVM stack pointer at
    the dividend, with the divisor packed directly after it. -/
def evmDivPrologue : String :=
  "  la x12, operands"

/-- `.data` section: 256 bytes of zero-filled scratch labeled
    `div_scratch:` *first*, then `operands:` with dividend ++ divisor
    (eight LE dwords). The scratch comes first so that `x12 - 160..-8`
    (the DIV body's scratch range, encoded as unsigned 12-bit offsets
    `3936..4088`) falls inside writable RAM.

    Written as raw asm rather than `emitDataLabel` because the layout
    mixes `.zero` and `.dword`. -/
def evmDivDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmDivDividend ++ evmDivDivisor).map emitDword)

def evmDivUnit : BuildUnit := {
  body        := evmDivPatched ++ evmAddEpilogue
  prologueAsm := evmDivPrologue
  dataAsm     := evmDivDataSection
}

/-! ## evm_div_from_input — M4 prover-supplied DIV operands

    Same wrapping as `evmDivUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region instead of being baked into `.data`.
    Lets one ELF cover many test vectors. Layout is identical to
    `evm_add_from_input` plus the 256 B `div_scratch:` block in front
    of `operands_ram:`. -/

def evm_div_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmDivPatched ++
  evmAddEpilogue

def evmDivFromInputPrologue : String :=
  "  la x12, operands_ram"

/-- `.data` section: 256 B of writable `div_scratch:` *before*
    `operands_ram:` (64 B reserved zero, overwritten at runtime). -/
def evmDivFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmDivFromInputUnit : BuildUnit := {
  body        := evm_div_from_input
  prologueAsm := evmDivFromInputPrologue
  dataAsm     := evmDivFromInputDataSection
}

/-! ## evm_mod — M2 first MOD end-to-end through ziskemu

    Same calling convention and scratch layout as `evm_div`. `evm_mod`
    differs only in the epilogue: `divK_mod_epilogue` copies `u[0..3]`
    (the de-normalized remainder) to `sp+32..64` instead of `q[0..3]`.
    The body structure (NOP "exit PC" at index 267 followed by the
    75-instruction `divK_div128_v4` subroutine) is identical, so the
    same NOP-splice fix applies. Like `evm_div`, `evm_mod` is not yet
    proven correct in Lean — the scripts under `scripts/codegen-evm_mod*`
    provide empirical confirmation by running on ziskemu. -/

/-- `EvmAsm.Evm64.evm_mod` with the NOP "exit PC" at index 267 replaced
    by a forward JAL skipping the 75-instruction subroutine to land at
    `evmAddEpilogue`. Same +304 byte offset as `evmDivPatched` because
    the MOD body has the identical 343-instruction layout. -/
def evmModPatched : Program :=
  (EvmAsm.Evm64.evm_mod : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod : List Instr).drop 268

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=1 cascade
    on the divisor (b=3, limb 0 only) plus the loop body. -/
def evmModDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 3. -/
def evmModDivisor : List UInt64 := [3, 0, 0, 0]

/-- Expected remainder = 2^64 mod 3 = 1 (since 2^64 = 3·6148914691236517205 + 1). -/
def evmModExpectedRemainder : List UInt64 := [1, 0, 0, 0]

def evmModPrologue : String :=
  "  la x12, operands"

def evmModDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmModDividend ++ evmModDivisor).map emitDword)

def evmModUnit : BuildUnit := {
  body        := evmModPatched ++ evmAddEpilogue
  prologueAsm := evmModPrologue
  dataAsm     := evmModDataSection
}

/-! ## evm_mod_from_input — M4 prover-supplied MOD operands

    Same wrapping as `evmModUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region (mirrors `evm_div_from_input`). -/

def evm_mod_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmModPatched ++
  evmAddEpilogue

def evmModFromInputPrologue : String :=
  "  la x12, operands_ram"

def evmModFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmModFromInputUnit : BuildUnit := {
  body        := evm_mod_from_input
  prologueAsm := evmModFromInputPrologue
  dataAsm     := evmModFromInputDataSection
}

/-! ## registry -/

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div"                   => some evmDivUnit
  | "evm_div_from_input"        => some evmDivFromInputUnit
  | "evm_mod"                   => some evmModUnit
  | "evm_mod_from_input"        => some evmModFromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | _                           => none

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div", "evm_mod", "input_echo",
   "evm_add_from_input", "evm_div_from_input", "evm_mod_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2"]

end EvmAsm.Codegen
