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
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program

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

/-! ## divK NOP-splice helpers (used by both M2 standalone DIV/MOD
    wrappers and the M8 dispatcher handlers, so hoisted above the
    M5b registry section that references them) -/

/-- `EvmAsm.Evm64.evm_div` with the NOP "exit PC" at internal index 267
    replaced by a forward `JAL .x0 +304` that skips the 75-instruction
    inline `divK_div128_v4` subroutine and lands at the instruction
    immediately following the body. In the M2 standalone wrapper that
    landing site is the start of `evmAddEpilogue`; in the M8
    dispatcher wrapper (M5b registry) it is the `mv x10, x9` of the
    handler's `x10RestoreAdvance1` tail. -/
def evmDivPatched : Program :=
  (EvmAsm.Evm64.evm_div : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_mod` with the same NOP-splice as `evmDivPatched`.
    Same +304 byte offset because the MOD body has the identical
    343-instruction layout (267 main + NOP + 75 subroutine). -/
def evmModPatched : Program :=
  (EvmAsm.Evm64.evm_mod : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod : List Instr).drop 268

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

/-- M7 memory opcodes. Register-parameterized; the dispatcher
    prologue sets up `x13 = &evm_memory` (see
    `EvmAsm/Codegen/Dispatch.lean`). The scratch registers `x14..x18`
    are caller-saved across the `jalr` from the dispatcher loop;
    nothing else in the registry preserves them.

    Stack-pointer bookkeeping is internal to the verified bodies:
    `evm_mload` is net stack-neutral, while `evm_mstore` and
    `evm_mstore8` each end with `ADDI .x12 .x12 64` so the wrapper
    uses the standard `.advanceAndRet 1` tail. None of the memory
    opcodes touch `x10`, so no `preBody` is needed. -/
def memoryHandlers : List OpcodeHandlerSpec :=
  [ -- MLOAD: pop offset, push value. memBase=x13;
    -- scratch: offReg=x15, byteReg=x16, accReg=x17, addrReg=x18.
    { label   := "h_MLOAD"
      opcodes := [0x51]
      body    := EvmAsm.Evm64.evm_mload .x15 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE: pop offset + value, write 32 bytes BE to memory.
    -- valReg=x14 (scratch; placeholder per evm_mstore docstring).
    { label   := "h_MSTORE"
      opcodes := [0x52]
      body    := EvmAsm.Evm64.evm_mstore .x15 .x14 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE8: pop offset + value, write 1 byte to memory.
    { label   := "h_MSTORE8"
      opcodes := [0x53]
      body    := EvmAsm.Evm64.evm_mstore8 .x15 .x14 .x18 .x13
      tail    := .advanceAndRet 1 } ]

/-- M8 unsigned division opcodes. Both `evm_div` and `evm_mod` carry
    a 75-instruction `divK_div128_v4` subroutine appended after a
    NOP "exit PC" at body index 267; the `evmDivPatched` /
    `evmModPatched` helpers (above) replace that NOP with `JAL .x0
    (304 : BitVec 21)` so the main path skips the inline subroutine
    and lands at the handler's wrapper tail.

    Both bodies clobber `x10` heavily (Knuth-D quotient accumulator,
    69 references) AND `x9` heavily (loop counter `j`, 94 refs).
    So we can't reuse the standard `x9`-as-save pattern from M6b —
    DIV/MOD save `x10` to **`x14`** instead, with a custom tail that
    restores from `x14`. `x14` is unused by `evm_div` / `evm_mod` (and
    their internal subroutine `divK_div128_v4`), and it's outside the
    dispatcher's preserved set, so clobbering it post-handler is fine.

    Stack-scratch: `evm_div` writes to negative `x12` offsets down to
    `-152` bytes (per `divK_*` scratch layout). The dispatcher's
    256-byte `evm_stack_low` block leaves 192 bytes below `x12`
    after two PUSH ops — comfortably > 152.

    **SDIV / SMOD are deferred to M8.5 / M9.** Their verified bodies
    end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`) that
    bypasses the dispatcher's standard wrapper tail; integrating them
    needs a trampoline-style wrapper (set `x18` to a per-handler
    "restore" stub before the body runs, splice off the body's
    initial save_ra_block). Tracked as the next codegen PR. -/
private def divModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  ret"

def divModHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_DIV"
      opcodes := [0x04]
      preBody := "  mv x14, x10"
      body    := evmDivPatched
      tail    := divModTail }
  , { label   := "h_MOD"
      opcodes := [0x06]
      preBody := "  mv x14, x10"
      body    := evmModPatched
      tail    := divModTail } ]

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
  memoryHandlers ++ divModHandlers ++ [stopHandler]

def tinyInterpDispatchAddUnit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAddBytecode

def tinyInterpDispatchAdd2Unit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAdd2Bytecode

/-! ## runtime_dispatcher — M8.5 runtime-bytecode dispatcher

    Same `tinyInterpRegistry` and `evmAddEpilogue` as the
    `tiny_interp_dispatch_*` units, but the dispatcher prologue
    reads `x10` from `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    instead of an in-`.data` label. One ELF runs any bytecode; the
    bash test harness packs each per-case bytecode into a
    ziskemu `-i <file>` payload and reuses the same dispatcher
    ELF for every case.

    See `EvmAsm/Codegen/Dispatch.lean` for `buildRuntimeDispatchUnit`
    and the runtime prologue/data-section helpers. -/
def runtimeDispatcherUnit : BuildUnit :=
  buildRuntimeDispatchUnit tinyInterpRegistry evmAddEpilogue

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

/-! ## evm_sdiv_v4 — signed DIV end-to-end through ziskemu

    `evm_sdiv_v4` uses the SDIV sign-handling wrapper and the corrected v4
    unsigned callable divider. Unlike standalone DIV/MOD, the wrapper returns
    via the caller return address saved in `x18`, so codegen seeds `x1` with a
    raw-asm label immediately after the verified body. -/

def evmSdivV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSdivV4ExpectedQuotient : List UInt64 := [0xfffffffffffffff2,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Prologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands"

def evmSdivV4Epilogue : String :=
  "after_sdiv:\n" ++ emitProgram evmAddEpilogue

def evmSdivV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSdivV4Dividend ++ evmSdivV4Divisor).map emitDword)

def evmSdivV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_sdiv_v4
  prologueAsm := evmSdivV4Prologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4DataSection
}

/-! ## evm_sdiv_v4_from_input — prover-supplied signed DIV operands -/

def evm_sdiv_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_sdiv_v4

def evmSdivV4FromInputPrologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands_ram"

def evmSdivV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSdivV4FromInputUnit : BuildUnit := {
  body        := evm_sdiv_v4_from_input
  prologueAsm := evmSdivV4FromInputPrologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4FromInputDataSection
}

/-! ## evm_smod_v4 — signed MOD end-to-end through ziskemu -/

def evmSmodV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSmodV4ExpectedRemainder : List UInt64 := [0xfffffffffffffffd,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Prologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands"

def evmSmodV4Epilogue : String :=
  "after_smod:\n" ++ emitProgram evmAddEpilogue

def evmSmodV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSmodV4Dividend ++ evmSmodV4Divisor).map emitDword)

def evmSmodV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_smod_v4
  prologueAsm := evmSmodV4Prologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4DataSection
}

/-! ## evm_smod_v4_from_input — prover-supplied signed MOD operands -/

def evm_smod_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_smod_v4

def evmSmodV4FromInputPrologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands_ram"

def evmSmodV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSmodV4FromInputUnit : BuildUnit := {
  body        := evm_smod_v4_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

/-! ## stateless_guest — PR2 SSZ-output stub

    See the definition of `statelessGuestUnit` below
    (after `zkvmKeccak256Function`, which the epilogue inlines). -/

/-! ## zisk_keccak_probe — PR-K1 ziskemu Keccak-f[1600] intrinsic probe

    Emits a raw-asm probe that triggers ziskemu's built-in
    Keccak-f[1600] accelerator (`_opcode_keccak` in
    `~/.zisk/zisk/emulator-asm/src/emu.c:507`). The accelerator is
    invoked by writing the state pointer into a non-standard CSR at
    address 0x800 -- which is the syscall ID the Zisk compiler
    expects, per `ziskos/entrypoint/src/syscalls/keccakf.rs` (uses
    `csrs 0x800, <reg>` via the `ziskos_syscall!` macro).

    GNU-as `csrs csr, rs1` expands to `csrrs x0, csr, rs1`. The
    32-bit encoding for `csrs 0x800, a0`:

      csr(0x800)    rs1(x10=01010)  f3(010)  rd(x0)    op(0x73)
      [31..20]      [19..15]        [14..12] [11..7]   [6..0]
      = 0x80052073

    We emit this as a raw `.4byte` directive rather than the
    `csrs` mnemonic so the existing
    `riscv64-unknown-elf-as -march=rv64imac` toolchain string
    works without enabling the `Zicsr` extension. The 32-bit value
    is what `as -march=rv64imac_zicsr` produces for the same
    mnemonic; pinning it here is the whole point of PR-K1.

    Probe sequence:
      la a0, zisk_keccak_state    # state pointer
      .4byte 0x80052073           # csrs 0x800, a0 -> _opcode_keccak
      <copy 200 bytes to OUTPUT_ADDR>
      <halt>

    Verified Program body is a single NOP -- everything observable
    happens in raw asm, so the verified semantics carry no claim
    about the probe yet. PR-K2 wires this through verified Instrs
    once the CSR instruction is added to `Rv64.Instr`. -/

/-- Asm prologue: probe the keccak intrinsic and stream the
    post-permutation 200-byte state to ziskemu's public-output
    region. Hard-codes `OUTPUT_ADDR = 0xa0010000` (mirrors the
    constant above). -/
def ziskKeccakProbePrologue : String :=
  "  la a0, zisk_keccak_state\n" ++
  "  .4byte 0x80052073           # csrs 0x800, a0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 25\n" ++
  ".Lzkp_copy_loop:\n" ++
  "  ld t2, 0(a0)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lzkp_copy_loop"

/-- `.data` section: 200 zero bytes labeled `zisk_keccak_state`.
    Lands in ziskemu RAM (0xa0000000..0xc0000000) via the standard
    `-Tdata=0xa0000000` link flag from `Codegen/Driver.lean`. -/
def ziskKeccakProbeDataSection : String :=
  ".section .data\n" ++
  "zisk_keccak_state:\n" ++
  "  .zero 200"

def ziskKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccakProbePrologue
  dataAsm     := ziskKeccakProbeDataSection
}

/-! ## zisk_keccak256_empty — PR-K2 keccak256 sponge over empty input

    First wrapper around PR-K1's intrinsic: the keccak256 sponge
    construction applied to a zero-byte message. Concretely:

      1. Zero the 200-byte state buffer.
      2. Pad: set byte 0 = 0x01, byte 135 = 0x80
         (Ethereum Keccak padding; rate = 1088 bits = 136 bytes).
      3. Trigger `_opcode_keccak` (csrs 0x800, a0).
      4. Copy the first 32 bytes of state to OUTPUT_ADDR -- those
         are the 256-bit hash digest.

    Expected output (32 bytes):
      c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Matches the canonical keccak256("") hash and the value produced
    by `eth_utils.keccak(b"")` / `Cryptodome.Hash.keccak.new(...).digest()`.
    This is the simplest possible exercise of the full sponge wrapper:
    no input blocks to absorb, just the final padded block. Future
    PRs extend this to one-block ("abc") and multi-block inputs. -/

/-- Asm prologue: zero state, apply Ethereum Keccak padding for the
    empty-message case, call the keccak-f intrinsic, copy the 32-byte
    digest to OUTPUT_ADDR. -/
def ziskKeccak256EmptyPrologue : String :=
  "  la s0, k256e_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256e_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256e_zero\n" ++
  "  # apply Ethereum Keccak padding to empty message\n" ++
  "  li t0, 0x01\n" ++
  "  sb t0, 0(s0)              # state[0] = 0x01\n" ++
  "  li t0, 0x80\n" ++
  "  sb t0, 135(s0)            # state[135] = 0x80\n" ++
  "  # call keccak-f via PR-K1 intrinsic (csrs 0x800, a0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # copy first 32 bytes of state to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000         # OUTPUT_ADDR\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256EmptyDataSection : String :=
  ".section .data\n" ++
  "k256e_state:\n" ++
  "  .zero 200"

def ziskKeccak256EmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256EmptyPrologue
  dataAsm     := ziskKeccak256EmptyDataSection
}

/-! ## zisk_keccak256_abc — PR-K2a single-block input

    Same sponge skeleton as PR-K2 but with the 3-byte input "abc"
    (RFC test vector) XORed into state positions 0..3 before the
    padding bytes (`0x01` at byte 3, `0x80` at byte 135). Single
    absorb block, single keccak-f call, then squeeze.

    Expected:
      keccak256(b"abc") =
        4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

    Demonstrates the single-block absorb path (input ≤ rate). The
    multi-block path lands in a follow-up. -/
def ziskKeccak256AbcPrologue : String :=
  "  la s0, k256a_state\n" ++
  "  # zero state\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256a_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256a_zero\n" ++
  "  # input \"abc\" at state[0..3]\n" ++
  "  li t0, 0x61; sb t0, 0(s0)\n" ++
  "  li t0, 0x62; sb t0, 1(s0)\n" ++
  "  li t0, 0x63; sb t0, 2(s0)\n" ++
  "  # Ethereum Keccak padding (length 3 < rate 136)\n" ++
  "  li t0, 0x01; sb t0, 3(s0)\n" ++
  "  li t0, 0x80; sb t0, 135(s0)\n" ++
  "  # call keccak-f\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256AbcDataSection : String :=
  ".section .data\n" ++
  "k256a_state:\n" ++
  "  .zero 200"

def ziskKeccak256AbcProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256AbcPrologue
  dataAsm     := ziskKeccak256AbcDataSection
}

/-! ## zisk_sha256_probe_le — PR-K15 SHA-256 intrinsic probe (LE-u32 layout)

    Earlier PR-S1 v1 (`task #17`) tried the SHA-256 intrinsic at
    CSR `0x805` with the 0.15.0-documented BE-per-u64 packing
    (state[0] = (h0 BE-u32 << 32) | h1 BE-u32, stored LE as a
    single u64). Output didn't match `sha256(b"")`.

    Hypothesis: the installed ziskemu (0.18.0) uses a different
    state packing -- specifically LE-u32 within u64 (state bytes
    are u32 BE in spec, stored as LE u32s -- so the 64-bit memory
    layout is `LE(h0) || LE(h1)` = bytes `67 e6 09 6a 85 ae 67 bb`
    for the first u64). As a u64 value this is
    `0xbb67ae856a09e667`.

    Probe re-runs the empty-message compression with this
    alternative layout. If it matches `sha256(b"")`, the 0.18.0
    intrinsic layout is pinned; if not, document further.

    Expected on success (SHA-256("") in LE-u32 packed memory):
      67 e6 09 6a 85 ae 67 bb 72 f3 6e 3c 3a f5 4f a5
      7f 52 0e 51 8c 68 05 9b ab d9 83 1f 19 cd e0 5b
    Then post-compression state should be SHA-256("")'s words
    packed the same way:
      sha256(empty) = e3 b0 c4 42 98 fc 1c 14 9a fb f4 c8 99 6f
                      b9 24 27 ae 41 e4 64 9b 93 4c a4 95 99 1b
                      78 52 b8 55
    As LE-u32 within u64 (per-byte memory order):
      42 c4 b0 e3 14 1c fc 98 c8 f4 fb 9a 24 b9 6f 99
      e4 41 ae 27 4c 93 9b 64 1b 99 95 a4 55 b8 52 78
-/
def ziskSha256ProbeLePrologue : String :=
  "  la a0, sha256_le_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  # copy 32-byte post-compression state to OUTPUT_ADDR\n" ++
  "  la t0, sha256_le_state\n" ++
  "  li t1, 0xa0010000\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)"

def ziskSha256ProbeLeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_le_state:\n" ++
  "  # state[0..4] = LE-u32-pack (each u32 stored LE in memory)\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_le_input:\n" ++
  "  # input[0] = LE-u32-pack of message u32[0..2]\n" ++
  "  # padded empty: u32[0] = 0x80 (LE bytes [80 00 00 00]) || u32[1] = 0\n" ++
  "  .quad 0x80\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0                     # u32[15] = length BE bits = 0\n" ++
  ".balign 8\n" ++
  "sha256_le_params:\n" ++
  "  .quad sha256_le_state\n" ++
  "  .quad sha256_le_input"

def ziskSha256ProbeLeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256ProbeLePrologue
  dataAsm     := ziskSha256ProbeLeDataSection
}

/-! ## zkvm_sha256 — PR-S2 Merkle-Damgård wrapper

    Parameterised SHA-256 callable matching the zkvm-standards C
    signature:

        zkvm_status zkvm_sha256(const uint8_t* data, size_t len,
                                zkvm_sha256_hash* output);

    Sister to PR-K3's `zkvm_keccak256`. Composes the LE-u32
    intrinsic pinned in PR-S1 (#5286) with the FIPS 180-4
    Merkle-Damgård wrapper:

      1. Initialise state to the SHA-256 IV (LE-u32 packing).
      2. For each full 64-byte input block: copy into the
         intrinsic's `sha256_input` buffer, `csrs 0x805, a0` to
         compress.
      3. Final block: copy <64 remainder bytes, append 0x80,
         append 8-byte big-endian bit-length at offset 56..64.
         If remainder >= 56, use two blocks (current + a fresh
         length-only block).
      4. Squeeze: byte-swap each u32 of the LE-packed state to
         produce canonical SHA-256 wire bytes
         (`e3b0c442 98fc1c14 ...` byte order). The byte-swap uses
         the `xori 3` index trick (within each 4-byte group,
         byte j maps to byte (3 ^ j)).

    Calling convention (RV64 ABI, mirrors `zkvm_keccak256`):
      a0 = data ptr; a1 = len; a2 = output ptr;
      ra = return; returns a0 = ZKVM_EOK = 0. -/

def zkvmSha256Function : String :=
  "zkvm_sha256:\n" ++
  "  # save callee-saved regs (s0..s5)\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp)\n" ++
  "  sd s4, 32(sp)\n" ++
  "  sd s5, 40(sp)\n" ++
  "  # s0 = state ptr; s1 = data ptr; s2 = remaining len;\n" ++
  "  # s3 = output ptr (= caller's a2); s4 = bit-length;\n" ++
  "  # s5 = sha256_input buffer base.\n" ++
  "  la s0, sha256_w_state\n" ++
  "  mv s1, a0\n" ++
  "  mv s2, a1\n" ++
  "  mv s3, a2\n" ++
  "  slli s4, a1, 3\n" ++
  "  la s5, sha256_w_input\n" ++
  "  # initialise state from IV (LE-u32 packed, 4 × u64)\n" ++
  "  la t0, sha256_w_iv\n" ++
  "  ld t1, 0(t0);  sd t1, 0(s0)\n" ++
  "  ld t1, 8(t0);  sd t1, 8(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s0)\n" ++
  "  # absorb full 64-byte blocks\n" ++
  ".Lzkv_sha_loop:\n" ++
  "  li t0, 64\n" ++
  "  blt s2, t0, .Lzkv_sha_final\n" ++
  "  ld t0, 0(s1);  sd t0, 0(s5)\n" ++
  "  ld t0, 8(s1);  sd t0, 8(s5)\n" ++
  "  ld t0, 16(s1); sd t0, 16(s5)\n" ++
  "  ld t0, 24(s1); sd t0, 24(s5)\n" ++
  "  ld t0, 32(s1); sd t0, 32(s5)\n" ++
  "  ld t0, 40(s1); sd t0, 40(s5)\n" ++
  "  ld t0, 48(s1); sd t0, 48(s5)\n" ++
  "  ld t0, 56(s1); sd t0, 56(s5)\n" ++
  "  la a0, sha256_w_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  addi s1, s1, 64\n" ++
  "  addi s2, s2, -64\n" ++
  "  j .Lzkv_sha_loop\n" ++
  ".Lzkv_sha_final:\n" ++
  "  # zero the input buffer\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  "  # byte-copy remaining s2 bytes from s1 to s5\n" ++
  "  mv t0, s5\n" ++
  "  mv t1, s1\n" ++
  "  mv t2, s2\n" ++
  ".Lzkv_sha_bcopy:\n" ++
  "  beqz t2, .Lzkv_sha_pad\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb  t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lzkv_sha_bcopy\n" ++
  ".Lzkv_sha_pad:\n" ++
  "  # write 0x80 at offset s2 in input buffer\n" ++
  "  add t0, s5, s2\n" ++
  "  li  t1, 0x80\n" ++
  "  sb  t1, 0(t0)\n" ++
  "  # if remainder < 56: single final block; else two-block path\n" ++
  "  li  t0, 56\n" ++
  "  blt s2, t0, .Lzkv_sha_writelen\n" ++
  "  # two-block: compress this block (data + 0x80, no length yet)\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # zero input buffer for the second (length-only) block\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  ".Lzkv_sha_writelen:\n" ++
  "  # 8-byte BE bit-length at offset 56..64 of input buffer\n" ++
  "  addi t0, s5, 56\n" ++
  "  srli t1, s4, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s4, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s4, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s4, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s4, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s4, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s4,  8; sb t1, 6(t0)\n" ++
  "  sb   s4, 7(t0)\n" ++
  "  # compress final block\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # squeeze: byte-swap each u32 of state into output\n" ++
  "  # output[i] = state[i ^ 3]   (reverses bytes within each 4-byte group)\n" ++
  "  li  t0, 0\n" ++
  ".Lzkv_sha_squeeze:\n" ++
  "  li  t1, 32\n" ++
  "  beq t0, t1, .Lzkv_sha_return\n" ++
  "  xori t2, t0, 3\n" ++
  "  add t3, s0, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  add t5, s3, t0\n" ++
  "  sb  t4, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lzkv_sha_squeeze\n" ++
  ".Lzkv_sha_return:\n" ++
  "  li  a0, 0\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskZkvmSha256Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # call 1: sha256(empty)\n" ++
  "  la a0, zsha_empty\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 2: sha256(\"abc\")\n" ++
  "  la a0, zsha_abc\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 3: sha256(0xaa × 200)\n" ++
  "  la a0, zsha_aa\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzkv_sha_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzkv_sha_done:"

def ziskZkvmSha256DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  "zsha_empty:\n" ++
  "  .byte 0\n" ++
  "zsha_abc:\n" ++
  "  .ascii \"abc\"\n" ++
  "zsha_aa:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmSha256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmSha256Prologue
  dataAsm     := ziskZkvmSha256DataSection
}

/-! ## zisk_sha256_from_input — PR-S3 host-supplied input

    Mirror of PR-K4 `zisk_keccak256_from_input` for SHA-256:
    hash whatever's at `INPUT_ADDR + 16` (length given at
    `INPUT_ADDR + 8` per ziskemu's input-region layout) and
    write the 32-byte digest to `OUTPUT_ADDR + 0..32`.

    Uses PR-S2's `zkvm_sha256` (the Merkle-Damgård wrapper)
    inlined per-BuildUnit. Test exercises arbitrary input
    lengths via the Python harness (`--shape header` for an
    RLP-encoded amsterdam Header ~658 bytes, `--shape long`
    for 1024 bytes of 0x55). -/
def ziskSha256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzks_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzks_done:"

def ziskSha256FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSha256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSha256FromInputPrologue
  dataAsm     := ziskSha256FromInputDataSection
}

/-! ## zisk_zkvm_keccak256 — PR-K3 parameterised wrapper

    Refactors the three hardcoded sponge probes (PR-K2 empty,
    PR-K2a "abc", PR-K2b multi-block) into a single jal-callable
    function matching the zkvm-standards C signature:

        zkvm_status zkvm_keccak256(const uint8_t* data, size_t len,
                                   zkvm_keccak256_hash* output);

    Calling convention (RV64 ABI):
      a0 = data ptr
      a1 = len
      a2 = output ptr (32 bytes will be written)
      ra = return address
      returns: a0 = 0 on success (ZKVM_EOK = 0)

    Internally clobbers t0..t6, a0..a2. Saves s0/s1/s2/s4 on the
    stack and restores them before returning. Caller is
    responsible for sp pointing at usable RAM.

    The build unit's test driver initialises sp, then makes three
    calls (empty / "abc" / 200×0xaa) writing the three 32-byte
    digests to OUTPUT[0..96]. After the third call, jumps past
    the function definition and falls through to halt.

    Expected OUTPUT[0..96]:
      0..32  : keccak256(b"")               = c5d2460186f7233c...
      32..64 : keccak256(b"abc")            = 4e03657aea45a94f...
      64..96 : keccak256(b"\xaa" * 200)     = ebad1a3694934 0cb... -/

/-- The parameterised `zkvm_keccak256` function definition (raw
    asm). Lives in the prologue after the test driver, guarded by
    a forward jump so it isn't executed on _start fall-through. -/
def zkvmKeccak256Function : String :=
  "zkvm_keccak256:\n" ++
  "  # save s0/s1/s2/s4 (callee-saved per RV64 ABI)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s4, 24(sp)\n" ++
  "  # stash args (a0/a1/a2 get clobbered during the absorb loop)\n" ++
  "  mv s4, a0                # data ptr\n" ++
  "  mv s1, a1                # remaining length\n" ++
  "  mv s2, a2                # output ptr\n" ++
  "  la s0, zk3_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lzk3_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lzk3_zero\n" ++
  "  # absorb full blocks (rate = 136 bytes)\n" ++
  ".Lzk3_full:\n" ++
  "  li t4, 136\n" ++
  "  blt s1, t4, .Lzk3_final\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  li t6, 17\n" ++
  ".Lzk3_xor:\n" ++
  "  ld t0, 0(t5)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  xor t1, t1, t0\n" ++
  "  sd t1, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t5, t5, 8\n" ++
  "  addi t6, t6, -1\n" ++
  "  bnez t6, .Lzk3_xor\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  addi s4, s4, 136\n" ++
  "  addi s1, s1, -136\n" ++
  "  j .Lzk3_full\n" ++
  ".Lzk3_final:\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  beqz s1, .Lzk3_pad\n" ++
  ".Lzk3_bxor:\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  lbu t1, 0(t3)\n" ++
  "  xor t0, t0, t1\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi s1, s1, -1\n" ++
  "  bnez s1, .Lzk3_bxor\n" ++
  ".Lzk3_pad:\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x01\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, s0, 135\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x80\n" ++
  "  sb t0, 0(t3)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to s2 (= output ptr)\n" ++
  "  ld t0, 0(s0);  sd t0, 0(s2)\n" ++
  "  ld t0, 8(s0);  sd t0, 8(s2)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s2)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s2)\n" ++
  "  # return ZKVM_EOK\n" ++
  "  li a0, 0\n" ++
  "  ld s0, 0(sp)\n" ++
  "  ld s1, 8(sp)\n" ++
  "  ld s2, 16(sp)\n" ++
  "  ld s4, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Test driver: initialises sp, calls `zkvm_keccak256` three times
    with the empty / abc / 200×0xaa inputs, then jumps over the
    function definition so we fall through to halt. -/
def ziskZkvmKeccak256Prologue : String :=
  "  # set up a usable stack pointer in RAM\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # call 1: keccak256(empty)\n" ++
  "  la a0, zk3_empty_marker\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 2: keccak256(\"abc\")\n" ++
  "  la a0, zk3_abc_input\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 3: keccak256(0xaa × 200)\n" ++
  "  la a0, zk3_aa_input\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # skip over the function definition, fall through to halt\n" ++
  "  j .Lzk3_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk3_done:"

def ziskZkvmKeccak256DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "zk3_empty_marker:\n" ++
  "  .byte 0\n" ++
  "zk3_abc_input:\n" ++
  "  .ascii \"abc\"\n" ++
  "zk3_aa_input:\n" ++
  "  .fill 200, 1, 0xaa"

def ziskZkvmKeccak256ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskZkvmKeccak256Prologue
  dataAsm     := ziskZkvmKeccak256DataSection
}

/-! ## zisk_keccak256_from_input — PR-K4 host-supplied input

    First real-shape consumer of the parameterised
    `zkvm_keccak256` from PR-K3: hash an arbitrary byte buffer
    that the host streamed in via `ziskemu -i <file>`. ziskemu
    places file bytes 0..8 (the u64 LE length prefix) at
    `INPUT_ADDR + 8..16` and file bytes 8.. (the data) at
    `INPUT_ADDR + 16..`. The probe reads the length, points at
    the data, calls `zkvm_keccak256`, writes the 32-byte digest
    at OUTPUT_ADDR.

    Designed to test header-shaped inputs (typical Ethereum
    header RLP is ~530-540 bytes), but accepts any byte stream.
    The Python harness (`scripts/keccak256-gen-input.py`)
    SSZ/RLP-encodes a real Header dataclass and emits the
    ziskemu-formatted input file. The test script runs ziskemu,
    diffs the OUTPUT digest against the Python-computed
    reference hash. -/
def ziskKeccak256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lzk4_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk4_done:"

/-- `.data` for the from-input probe: 200-byte state buffer used
    by `zkvm_keccak256`. Input data lives in the
    `INPUT_ADDR` region (host-supplied via `ziskemu -i`), not in
    `.data`. -/
def ziskKeccak256FromInputDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskKeccak256FromInputProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccak256FromInputPrologue
  dataAsm     := ziskKeccak256FromInputDataSection
}

/-! ## headers_keccak_chain -- PR-K15 walk an SSZ list section,
    keccak each element, return the last digest + count.

    Walks the SSZ inner-offset table to derive per-element
    bounds (same parsing shape as the SSZ list-merkleize work),
    then calls `zkvm_keccak256(el_i_start, el_i_len, out_ptr)`
    for each element. The output buffer is overwritten on every
    iteration; after the loop, it holds the LAST element's
    digest. Returns the element count `N` in `a0`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 ⇒ empty list)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0.

    No per-element scratch; works for any N. -/
def headersKeccakChainFunction : String :=
  "headers_keccak_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = output ptr\n" ++
  "  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhkc_loop:\n" ++
  "  beq s4, s3, .Lhkc_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhkc_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhkc_have_end\n" ++
  ".Lhkc_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhkc_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # output (overwritten each iter)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhkc_loop\n" ++
  ".Lhkc_n0:\n" ++
  "  sd zero,  0(s2)\n" ++
  "  sd zero,  8(s2)\n" ++
  "  sd zero, 16(s2)\n" ++
  "  sd zero, 24(s2)\n" ++
  "  li s3, 0                   # N = 0\n" ++
  ".Lhkc_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_chain`: probe BuildUnit that reads an
    SSZ list section from host input and writes the count + last
    digest to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : N (u64 LE)
      bytes  8..40 : keccak256(element[N-1]) or 0 if N=0 -/
def ziskHeadersKeccakChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # last_hash output (OUTPUT + 8)\n" ++
  "  jal ra, headers_keccak_chain\n" ++
  "  li t0, 0xa0010000           # write N at OUTPUT + 0\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhkc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakChainFunction ++ "\n" ++
  ".Lhkc_pdone:"

def ziskHeadersKeccakChainDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakChainPrologue
  dataAsm     := ziskHeadersKeccakChainDataSection
}

/-! ## headers_keccak_array -- PR-K16 walk SSZ list section,
    keccak each element, store every digest in caller table.

    Sibling of `headers_keccak_chain` (PR-K15): same SSZ-list
    parsing loop, but each iteration writes the digest to
    `table[i]` instead of overwriting the same slot. Returns the
    element count `N`.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (must hold N*32 bytes)
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. -/
def headersKeccakArrayFunction : String :=
  "headers_keccak_array:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = table base\n" ++
  "  beqz s1, .Lhka_n0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhka_loop:\n" ++
  "  beq s4, s3, .Lhka_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhka_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhka_have_end\n" ++
  ".Lhka_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhka_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  slli t0, s4, 5             # 32*i\n" ++
  "  add a2, s2, t0             # a2 = &table[i]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhka_loop\n" ++
  ".Lhka_n0:\n" ++
  "  li s3, 0\n" ++
  ".Lhka_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_array`: probe BuildUnit that reads an
    SSZ list section from host input and writes (count, table)
    to OUTPUT, capped at N ≤ 7 to fit ziskemu's 256-byte output
    channel.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8     : N (u64 LE)
      bytes  8..8+32*N : N digests of 32 bytes each -/
def ziskHeadersKeccakArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # table at OUTPUT + 8\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write N at OUTPUT + 0\n" ++
  "  j .Lhka_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  ".Lhka_pdone:"

def ziskHeadersKeccakArrayDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakArrayPrologue
  dataAsm     := ziskHeadersKeccakArrayDataSection
}

/-! ## headers_parent_hash -- PR-K17 RLP-walk to extract the
    first 32-byte field of an RLP-encoded Ethereum header
    (`parent_hash`).

    Skips the outer list prefix (0xc0..0xc0+55 short form, 0xf8
    1-byte-length, or 0xf9 2-byte-length forms), expects a
    0xa0 Bytes32 string prefix, then copies the 32 raw bytes
    to the caller's output.

    Calling convention:
      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 on success; 32 bytes at *a2 = parent_hash
        1 on RLP parse failure

    Pure register arithmetic; no scratch memory, no callee-saved
    registers used. Leaf-callable. -/
def headersParentHashFunction : String :=
  "headers_parent_hash:\n" ++
  "  # a0 = header ptr, a1 = header_len, a2 = out ptr\n" ++
  "  lbu t0, 0(a0)                # first byte\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lhph_fail      # not an RLP list (< 0xc0)\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lhph_short     # 0xc0..0xf7 → short list, 1-byte prefix\n" ++
  "  # long list: t0 in [0xf8..0xff].\n" ++
  "  # length_of_length = t0 - 0xf7. Outer prefix = 1 + length_of_length bytes.\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1               # length_of_length\n" ++
  "  li t3, 2                     # cap: support 0xf8 (LoL=1), 0xf9 (LoL=2)\n" ++
  "  bltu t3, t2, .Lhph_fail      # LoL > 2 → unsupported\n" ++
  "  addi t2, t2, 1               # prefix bytes = LoL + 1\n" ++
  "  add a0, a0, t2               # skip prefix\n" ++
  "  sub a1, a1, t2\n" ++
  "  j .Lhph_after_prefix\n" ++
  ".Lhph_short:\n" ++
  "  addi a0, a0, 1               # skip 1-byte prefix\n" ++
  "  addi a1, a1, -1\n" ++
  ".Lhph_after_prefix:\n" ++
  "  # Expect 0xa0 Bytes32 prefix.\n" ++
  "  li t0, 33\n" ++
  "  bltu a1, t0, .Lhph_fail      # not enough bytes for 0xa0 + 32\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  li t2, 0xa0\n" ++
  "  bne t1, t2, .Lhph_fail       # not a Bytes32 string\n" ++
  "  # Copy 32 bytes from a0+1 to a2.\n" ++
  "  ld t0,  1(a0); sd t0,  0(a2)\n" ++
  "  ld t0,  9(a0); sd t0,  8(a2)\n" ++
  "  ld t0, 17(a0); sd t0, 16(a2)\n" ++
  "  ld t0, 25(a0); sd t0, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lhph_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_headers_parent_hash`: probe BuildUnit that reads an
    RLP-encoded header from host input and writes
    `(status, parent_hash)` to OUTPUT.
    Input layout:
      bytes  0.. 8 : header_len (u64)
      bytes  8..   : RLP-encoded header bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 = ok, 1 = parse fail)
      bytes  8..40 : parent_hash (32 bytes; meaningful only on
                     status=0; on failure, contains zeros) -/
def ziskHeadersParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # parent_hash output (OUTPUT + 8)\n" ++
  "  # Pre-zero output[8..40] so a parse failure surfaces as zeros.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write status at OUTPUT + 0\n" ++
  "  j .Lhph_pdone\n" ++
  headersParentHashFunction ++ "\n" ++
  ".Lhph_pdone:"

def ziskHeadersParentHashDataSection : String :=
  ".section .data\n" ++
  "hph_scratch:\n" ++
  "  .zero 8"

def ziskHeadersParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersParentHashPrologue
  dataAsm     := ziskHeadersParentHashDataSection
}

/-! ## headers_validate_chain -- PR-K18 parent_hash chain check

    Composes PR-K16 `headers_keccak_array` (build per-header
    digest table) with PR-K17 `headers_parent_hash` (RLP-extract
    each header's first 32-byte field) to verify the
    `validate_headers` invariant:

        header[i].parent_hash == keccak256(header[i-1])
            for every i in 1..N

    matches the Python check in
    `execution-specs/.../stateless.py::validate_headers`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.headers)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : 8-byte output ptr (receives N as u64 LE)
      ra (input)  : return
      a0 (output) : 0 on success (chain valid) or N ≤ 1
                    1 on mismatch / RLP-decode failure

    Walks the list using the same SSZ inner-offset table as
    PR-K15/K16. Caps at N ≤ 256 (matches `MAX_WITNESS_HEADERS`).

    Uses two `.data` scratch buffers:
      vh_keccak_table          : 256 × 32 = 8 KB
      vh_extracted_parent_hash : 32 B
-/
def headersValidateChainFunction : String :=
  "headers_validate_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = N out ptr\n" ++
  "  # Step 1: keccak each header into vh_keccak_table.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vh_keccak_table\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  mv s3, a0                  # s3 = N\n" ++
  "  sd s3, 0(s2)               # *N_out = N\n" ++
  "  # If N ≤ 1, no chain links to check → ok.\n" ++
  "  li t0, 2\n" ++
  "  bltu s3, t0, .Lvh_ok\n" ++
  "  # Loop i = 1..N.\n" ++
  "  li s4, 1\n" ++
  ".Lvh_loop:\n" ++
  "  beq s4, s3, .Lvh_ok\n" ++
  "  # Find element i bounds from inner-offset table.\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lvh_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lvh_have_end\n" ++
  ".Lvh_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lvh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, vh_extracted_parent_hash\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  bnez a0, .Lvh_fail         # RLP parse failed\n" ++
  "  # Compare extracted parent_hash against vh_keccak_table[i-1].\n" ++
  "  la t0, vh_keccak_table\n" ++
  "  addi t1, s4, -1\n" ++
  "  slli t1, t1, 5             # (i-1) * 32\n" ++
  "  add t0, t0, t1             # &table[i-1]\n" ++
  "  la t1, vh_extracted_parent_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvh_fail\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lvh_loop\n" ++
  ".Lvh_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvh_ret\n" ++
  ".Lvh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_validate_chain`: probe BuildUnit that reads an
    SSZ list of RLP-encoded headers from host input and writes
    (status, N) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 ok / 1 mismatch)
      bytes  8..16 : N (u64 LE; element count) -/
def ziskHeadersValidateChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # N out ptr (OUTPUT + 8)\n" ++
  "  jal ra, headers_validate_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  ".Lvh_pdone:"

def ziskHeadersValidateChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192                 # 256 × 32-byte digests\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32"

def ziskHeadersValidateChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersValidateChainPrologue
  dataAsm     := ziskHeadersValidateChainDataSection
}

/-! ## witness_lookup_by_hash -- PR-K19 (linear-scan flavour)

    Find the entry in an SSZ list section whose keccak256 digest
    matches a caller-supplied target hash. Returns the matched
    entry's (offset, length) within the section, or status=1 on
    miss.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.state /
                    witness.codes shape)
      a1 (input)  : section_len (0 ⇒ guaranteed miss)
      a2 (input)  : 32-byte target hash ptr
      a3 (input)  : u64 out ptr (matched entry's byte offset
                    within the section; meaningful only on hit)
      a4 (input)  : u64 out ptr (matched entry's byte length;
                    meaningful only on hit)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on miss

    Walks every element computing `keccak256(element_bytes)`
    until either a match is found or the list is exhausted.
    O(N) per call; PR-K20+ will replace with a pre-built bucket
    table for O(1) average lookups. -/
def witnessLookupByHashFunction : String :=
  "witness_lookup_by_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # target_hash ptr\n" ++
  "  mv s3, a3                  # out_offset ptr\n" ++
  "  mv s4, a4                  # out_length ptr\n" ++
  "  beqz s1, .Lwlh_miss        # empty section ⇒ miss\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s5, t0, 2             # s5 = N\n" ++
  "  li s6, 0                   # s6 = i\n" ++
  ".Lwlh_loop:\n" ++
  "  beq s6, s5, .Lwlh_miss\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwlh_have_end\n" ++
  ".Lwlh_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwlh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, wlh_scratch_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Compare scratch_hash vs target_hash.\n" ++
  "  la t0, wlh_scratch_hash\n" ++
  "  mv t1, s2\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  # Match. Recompute (offset, length) from i (clobbered above).\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  sd t2, 0(s3)               # *out_offset = inner_off_i\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_last_len\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  sub t4, t4, t2             # length = inner_off_{i+1} - inner_off_i\n" ++
  "  j .Lwlh_store_len\n" ++
  ".Lwlh_last_len:\n" ++
  "  sub t4, s1, t2             # length = section_len - inner_off_i\n" ++
  ".Lwlh_store_len:\n" ++
  "  sd t4, 0(s4)\n" ++
  "  li a0, 0                   # hit\n" ++
  "  j .Lwlh_ret\n" ++
  ".Lwlh_no_match:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwlh_loop\n" ++
  ".Lwlh_miss:\n" ++
  "  li a0, 1                   # miss\n" ++
  ".Lwlh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_lookup_by_hash`: probe BuildUnit. Reads
    (section_len, target_hash, section_bytes) from host input,
    writes (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..40 : target_hash (32 bytes)
      bytes 40..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 hit, 1 miss)
      bytes  8..16 : matched entry offset within section (u64)
      bytes 16..24 : matched entry length (u64) -/
def ziskWitnessLookupByHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a2, a5, 16             # target_hash ptr\n" ++
  "  addi a0, a5, 48             # section ptr\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  # Pre-zero offset/length so a miss surfaces as zeros.\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lwlh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlh_pdone:"

def ziskWitnessLookupByHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessLookupByHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessLookupByHashPrologue
  dataAsm     := ziskWitnessLookupByHashDataSection
}

/-! ## zisk_ssz_pair_hash — PR-S4 SSZ merkleization primitive

    First consumer of the SSZ `hash_tree_root` shim:
    `sha256_pair(L, R) = sha256(L ‖ R)`.

    The shim lives at `Stateless/SSZ/HashTreeRoot/Program.lean`
    (`sszPairHashCallAsm`); this BuildUnit is the executable that
    exercises it end-to-end on ziskemu. The driver reads two
    32-byte values from the host-supplied input region (laid out
    contiguously at INPUT_ADDR + 16..80 so they're already in
    L ‖ R order), passes the buffer base in `a0` and the OUTPUT
    pointer in `a2`, and lets the shim hand off to the PR-S2
    `zkvm_sha256` wrapper.

    ### Fixture (32-byte SSZ "zero leaf" pair)

      L = 0x00..00 (32 bytes)
      R = 0x00..00 (32 bytes)

    Expected (this is `Z_1` in the SSZ zero-hashes sequence):

      sha256(0x00 * 64) =
        f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b

    The test script feeds those 64 zero bytes via `ziskemu -i` and
    diffs the 32-byte digest at OUTPUT_ADDR against Python's
    `hashlib.sha256(b"\\x00" * 64).digest()`.

    ### Why this isn't redundant with the PR-S2 in-data fixture

    PR-S2 tested `zkvm_sha256` on `.data`-resident constants;
    PR-S3 tested it on host-supplied input. PR-S4 additionally
    pins the `ssz_pair_hash` *symbol* -- the named entry point
    that higher SSZ machinery (PR-S5+ merkleize, mix_in_length)
    will call. Once that symbol exists, the merkleize loop is a
    straightforward "load chunk, call `ssz_pair_hash`, store
    result" iteration; no further sha256 layout decisions.
-/
def ziskSszPairHashPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # point at the 64-byte L||R buffer in host input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  addi a0, a3, 16             # a0 = L||R ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  EvmAsm.Stateless.SSZ.HashTreeRoot.sszPairHashCallAsm ++ "\n" ++
  "  j .Lzs4_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzs4_done:"

/-- `.data` for the SSZ pair-hash probe: same scratch buffers
    used by `zkvm_sha256` (IV, state, input block, params). The
    L‖R bytes come from host input, not from `.data`. -/
def ziskSszPairHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"

def ziskSszPairHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszPairHashPrologue
  dataAsm     := ziskSszPairHashDataSection
}

/-! ## ssz_zero_hashes — PR-S5 precomputed SSZ Z_0..Z_31 table

    Pre-computed SSZ "zero hashes" sequence:
      Z_0 = 0x00..00 (32 zero bytes)
      Z_i = sha256(Z_{i-1} ‖ Z_{i-1})

    Emitted as a single 1024-byte `.rodata` block. Entry `i` lives
    at `ssz_zero_hashes + i * 32`. Cached at codegen time so the
    PR-S6 merkleize loop can short-circuit all-zero subtrees of
    depth ≤ 31 without re-running SHA-256.

    Values generated once with Python:

        import hashlib
        z = [b"\x00" * 32]
        for _ in range(31):
            z.append(hashlib.sha256(z[-1] + z[-1]).digest())

    `z[1]` matches the PR-S4 fixture (`f5a5fd42..fb4b`), and the
    full table is regression-checked by the
    `zisk_ssz_zero_hashes` probe BuildUnit below: it accepts a
    depth `i` via host input, looks up Z_i, and writes 32 bytes
    to OUTPUT. The check script iterates i = 0..31 and diffs
    each Z_i against Python's recomputation.
-/
def sszZeroHashesDataSection : String :=
  ".section .rodata\n" ++
  ".balign 32\n" ++
  "ssz_zero_hashes:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    # Z_0\n" ++
  "  .byte 0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30, 0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09, 0x97, 0x9b, 0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8, 0xea, 0x98, 0x31, 0xa9, 0x27, 0x59, 0xfb, 0x4b    # Z_1\n" ++
  "  .byte 0xdb, 0x56, 0x11, 0x4e, 0x00, 0xfd, 0xd4, 0xc1, 0xf8, 0x5c, 0x89, 0x2b, 0xf3, 0x5a, 0xc9, 0xa8, 0x92, 0x89, 0xaa, 0xec, 0xb1, 0xeb, 0xd0, 0xa9, 0x6c, 0xde, 0x60, 0x6a, 0x74, 0x8b, 0x5d, 0x71    # Z_2\n" ++
  "  .byte 0xc7, 0x80, 0x09, 0xfd, 0xf0, 0x7f, 0xc5, 0x6a, 0x11, 0xf1, 0x22, 0x37, 0x06, 0x58, 0xa3, 0x53, 0xaa, 0xa5, 0x42, 0xed, 0x63, 0xe4, 0x4c, 0x4b, 0xc1, 0x5f, 0xf4, 0xcd, 0x10, 0x5a, 0xb3, 0x3c    # Z_3\n" ++
  "  .byte 0x53, 0x6d, 0x98, 0x83, 0x7f, 0x2d, 0xd1, 0x65, 0xa5, 0x5d, 0x5e, 0xea, 0xe9, 0x14, 0x85, 0x95, 0x44, 0x72, 0xd5, 0x6f, 0x24, 0x6d, 0xf2, 0x56, 0xbf, 0x3c, 0xae, 0x19, 0x35, 0x2a, 0x12, 0x3c    # Z_4\n" ++
  "  .byte 0x9e, 0xfd, 0xe0, 0x52, 0xaa, 0x15, 0x42, 0x9f, 0xae, 0x05, 0xba, 0xd4, 0xd0, 0xb1, 0xd7, 0xc6, 0x4d, 0xa6, 0x4d, 0x03, 0xd7, 0xa1, 0x85, 0x4a, 0x58, 0x8c, 0x2c, 0xb8, 0x43, 0x0c, 0x0d, 0x30    # Z_5\n" ++
  "  .byte 0xd8, 0x8d, 0xdf, 0xee, 0xd4, 0x00, 0xa8, 0x75, 0x55, 0x96, 0xb2, 0x19, 0x42, 0xc1, 0x49, 0x7e, 0x11, 0x4c, 0x30, 0x2e, 0x61, 0x18, 0x29, 0x0f, 0x91, 0xe6, 0x77, 0x29, 0x76, 0x04, 0x1f, 0xa1    # Z_6\n" ++
  "  .byte 0x87, 0xeb, 0x0d, 0xdb, 0xa5, 0x7e, 0x35, 0xf6, 0xd2, 0x86, 0x67, 0x38, 0x02, 0xa4, 0xaf, 0x59, 0x75, 0xe2, 0x25, 0x06, 0xc7, 0xcf, 0x4c, 0x64, 0xbb, 0x6b, 0xe5, 0xee, 0x11, 0x52, 0x7f, 0x2c    # Z_7\n" ++
  "  .byte 0x26, 0x84, 0x64, 0x76, 0xfd, 0x5f, 0xc5, 0x4a, 0x5d, 0x43, 0x38, 0x51, 0x67, 0xc9, 0x51, 0x44, 0xf2, 0x64, 0x3f, 0x53, 0x3c, 0xc8, 0x5b, 0xb9, 0xd1, 0x6b, 0x78, 0x2f, 0x8d, 0x7d, 0xb1, 0x93    # Z_8\n" ++
  "  .byte 0x50, 0x6d, 0x86, 0x58, 0x2d, 0x25, 0x24, 0x05, 0xb8, 0x40, 0x01, 0x87, 0x92, 0xca, 0xd2, 0xbf, 0x12, 0x59, 0xf1, 0xef, 0x5a, 0xa5, 0xf8, 0x87, 0xe1, 0x3c, 0xb2, 0xf0, 0x09, 0x4f, 0x51, 0xe1    # Z_9\n" ++
  "  .byte 0xff, 0xff, 0x0a, 0xd7, 0xe6, 0x59, 0x77, 0x2f, 0x95, 0x34, 0xc1, 0x95, 0xc8, 0x15, 0xef, 0xc4, 0x01, 0x4e, 0xf1, 0xe1, 0xda, 0xed, 0x44, 0x04, 0xc0, 0x63, 0x85, 0xd1, 0x11, 0x92, 0xe9, 0x2b    # Z_10\n" ++
  "  .byte 0x6c, 0xf0, 0x41, 0x27, 0xdb, 0x05, 0x44, 0x1c, 0xd8, 0x33, 0x10, 0x7a, 0x52, 0xbe, 0x85, 0x28, 0x68, 0x89, 0x0e, 0x43, 0x17, 0xe6, 0xa0, 0x2a, 0xb4, 0x76, 0x83, 0xaa, 0x75, 0x96, 0x42, 0x20    # Z_11\n" ++
  "  .byte 0xb7, 0xd0, 0x5f, 0x87, 0x5f, 0x14, 0x00, 0x27, 0xef, 0x51, 0x18, 0xa2, 0x24, 0x7b, 0xbb, 0x84, 0xce, 0x8f, 0x2f, 0x0f, 0x11, 0x23, 0x62, 0x30, 0x85, 0xda, 0xf7, 0x96, 0x0c, 0x32, 0x9f, 0x5f    # Z_12\n" ++
  "  .byte 0xdf, 0x6a, 0xf5, 0xf5, 0xbb, 0xdb, 0x6b, 0xe9, 0xef, 0x8a, 0xa6, 0x18, 0xe4, 0xbf, 0x80, 0x73, 0x96, 0x08, 0x67, 0x17, 0x1e, 0x29, 0x67, 0x6f, 0x8b, 0x28, 0x4d, 0xea, 0x6a, 0x08, 0xa8, 0x5e    # Z_13\n" ++
  "  .byte 0xb5, 0x8d, 0x90, 0x0f, 0x5e, 0x18, 0x2e, 0x3c, 0x50, 0xef, 0x74, 0x96, 0x9e, 0xa1, 0x6c, 0x77, 0x26, 0xc5, 0x49, 0x75, 0x7c, 0xc2, 0x35, 0x23, 0xc3, 0x69, 0x58, 0x7d, 0xa7, 0x29, 0x37, 0x84    # Z_14\n" ++
  "  .byte 0xd4, 0x9a, 0x75, 0x02, 0xff, 0xcf, 0xb0, 0x34, 0x0b, 0x1d, 0x78, 0x85, 0x68, 0x85, 0x00, 0xca, 0x30, 0x81, 0x61, 0xa7, 0xf9, 0x6b, 0x62, 0xdf, 0x9d, 0x08, 0x3b, 0x71, 0xfc, 0xc8, 0xf2, 0xbb    # Z_15\n" ++
  "  .byte 0x8f, 0xe6, 0xb1, 0x68, 0x92, 0x56, 0xc0, 0xd3, 0x85, 0xf4, 0x2f, 0x5b, 0xbe, 0x20, 0x27, 0xa2, 0x2c, 0x19, 0x96, 0xe1, 0x10, 0xba, 0x97, 0xc1, 0x71, 0xd3, 0xe5, 0x94, 0x8d, 0xe9, 0x2b, 0xeb    # Z_16\n" ++
  "  .byte 0x8d, 0x0d, 0x63, 0xc3, 0x9e, 0xba, 0xde, 0x85, 0x09, 0xe0, 0xae, 0x3c, 0x9c, 0x38, 0x76, 0xfb, 0x5f, 0xa1, 0x12, 0xbe, 0x18, 0xf9, 0x05, 0xec, 0xac, 0xfe, 0xcb, 0x92, 0x05, 0x76, 0x03, 0xab    # Z_17\n" ++
  "  .byte 0x95, 0xee, 0xc8, 0xb2, 0xe5, 0x41, 0xca, 0xd4, 0xe9, 0x1d, 0xe3, 0x83, 0x85, 0xf2, 0xe0, 0x46, 0x61, 0x9f, 0x54, 0x49, 0x6c, 0x23, 0x82, 0xcb, 0x6c, 0xac, 0xd5, 0xb9, 0x8c, 0x26, 0xf5, 0xa4    # Z_18\n" ++
  "  .byte 0xf8, 0x93, 0xe9, 0x08, 0x91, 0x77, 0x75, 0xb6, 0x2b, 0xff, 0x23, 0x29, 0x4d, 0xbb, 0xe3, 0xa1, 0xcd, 0x8e, 0x6c, 0xc1, 0xc3, 0x5b, 0x48, 0x01, 0x88, 0x7b, 0x64, 0x6a, 0x6f, 0x81, 0xf1, 0x7f    # Z_19\n" ++
  "  .byte 0xcd, 0xdb, 0xa7, 0xb5, 0x92, 0xe3, 0x13, 0x33, 0x93, 0xc1, 0x61, 0x94, 0xfa, 0xc7, 0x43, 0x1a, 0xbf, 0x2f, 0x54, 0x85, 0xed, 0x71, 0x1d, 0xb2, 0x82, 0x18, 0x3c, 0x81, 0x9e, 0x08, 0xeb, 0xaa    # Z_20\n" ++
  "  .byte 0x8a, 0x8d, 0x7f, 0xe3, 0xaf, 0x8c, 0xaa, 0x08, 0x5a, 0x76, 0x39, 0xa8, 0x32, 0x00, 0x14, 0x57, 0xdf, 0xb9, 0x12, 0x8a, 0x80, 0x61, 0x14, 0x2a, 0xd0, 0x33, 0x56, 0x29, 0xff, 0x23, 0xff, 0x9c    # Z_21\n" ++
  "  .byte 0xfe, 0xb3, 0xc3, 0x37, 0xd7, 0xa5, 0x1a, 0x6f, 0xbf, 0x00, 0xb9, 0xe3, 0x4c, 0x52, 0xe1, 0xc9, 0x19, 0x5c, 0x96, 0x9b, 0xd4, 0xe7, 0xa0, 0xbf, 0xd5, 0x1d, 0x5c, 0x5b, 0xed, 0x9c, 0x11, 0x67    # Z_22\n" ++
  "  .byte 0xe7, 0x1f, 0x0a, 0xa8, 0x3c, 0xc3, 0x2e, 0xdf, 0xbe, 0xfa, 0x9f, 0x4d, 0x3e, 0x01, 0x74, 0xca, 0x85, 0x18, 0x2e, 0xec, 0x9f, 0x3a, 0x09, 0xf6, 0xa6, 0xc0, 0xdf, 0x63, 0x77, 0xa5, 0x10, 0xd7    # Z_23\n" ++
  "  .byte 0x31, 0x20, 0x6f, 0xa8, 0x0a, 0x50, 0xbb, 0x6a, 0xbe, 0x29, 0x08, 0x50, 0x58, 0xf1, 0x62, 0x12, 0x21, 0x2a, 0x60, 0xee, 0xc8, 0xf0, 0x49, 0xfe, 0xcb, 0x92, 0xd8, 0xc8, 0xe0, 0xa8, 0x4b, 0xc0    # Z_24\n" ++
  "  .byte 0x21, 0x35, 0x2b, 0xfe, 0xcb, 0xed, 0xdd, 0xe9, 0x93, 0x83, 0x9f, 0x61, 0x4c, 0x3d, 0xac, 0x0a, 0x3e, 0xe3, 0x75, 0x43, 0xf9, 0xb4, 0x12, 0xb1, 0x61, 0x99, 0xdc, 0x15, 0x8e, 0x23, 0xb5, 0x44    # Z_25\n" ++
  "  .byte 0x61, 0x9e, 0x31, 0x27, 0x24, 0xbb, 0x6d, 0x7c, 0x31, 0x53, 0xed, 0x9d, 0xe7, 0x91, 0xd7, 0x64, 0xa3, 0x66, 0xb3, 0x89, 0xaf, 0x13, 0xc5, 0x8b, 0xf8, 0xa8, 0xd9, 0x04, 0x81, 0xa4, 0x67, 0x65    # Z_26\n" ++
  "  .byte 0x7c, 0xdd, 0x29, 0x86, 0x26, 0x82, 0x50, 0x62, 0x8d, 0x0c, 0x10, 0xe3, 0x85, 0xc5, 0x8c, 0x61, 0x91, 0xe6, 0xfb, 0xe0, 0x51, 0x91, 0xbc, 0xc0, 0x4f, 0x13, 0x3f, 0x2c, 0xea, 0x72, 0xc1, 0xc4    # Z_27\n" ++
  "  .byte 0x84, 0x89, 0x30, 0xbd, 0x7b, 0xa8, 0xca, 0xc5, 0x46, 0x61, 0x07, 0x21, 0x13, 0xfb, 0x27, 0x88, 0x69, 0xe0, 0x7b, 0xb8, 0x58, 0x7f, 0x91, 0x39, 0x29, 0x33, 0x37, 0x4d, 0x01, 0x7b, 0xcb, 0xe1    # Z_28\n" ++
  "  .byte 0x88, 0x69, 0xff, 0x2c, 0x22, 0xb2, 0x8c, 0xc1, 0x05, 0x10, 0xd9, 0x85, 0x32, 0x92, 0x80, 0x33, 0x28, 0xbe, 0x4f, 0xb0, 0xe8, 0x04, 0x95, 0xe8, 0xbb, 0x8d, 0x27, 0x1f, 0x5b, 0x88, 0x96, 0x36    # Z_29\n" ++
  "  .byte 0xb5, 0xfe, 0x28, 0xe7, 0x9f, 0x1b, 0x85, 0x0f, 0x86, 0x58, 0x24, 0x6c, 0xe9, 0xb6, 0xa1, 0xe7, 0xb4, 0x9f, 0xc0, 0x6d, 0xb7, 0x14, 0x3e, 0x8f, 0xe0, 0xb4, 0xf2, 0xb0, 0xc5, 0x52, 0x3a, 0x5c    # Z_30\n" ++
  "  .byte 0x98, 0x5e, 0x92, 0x9f, 0x70, 0xaf, 0x28, 0xd0, 0xbd, 0xd1, 0xa9, 0x0a, 0x80, 0x8f, 0x97, 0x7f, 0x59, 0x7c, 0x7c, 0x77, 0x8c, 0x48, 0x9e, 0x98, 0xd3, 0xbd, 0x89, 0x10, 0xd3, 0x1a, 0xc0, 0xf7    # Z_31"

/-- `zisk_ssz_zero_hashes`: probe BuildUnit that reads a u64
    depth index from `INPUT_ADDR + 8` (LE; first 8 bytes of the
    ziskemu input file) and writes the 32 bytes of `Z_i` to
    `OUTPUT_ADDR`. -/
def ziskSszZeroHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a0, 8(a3)                # a0 = depth index i (u64 LE)\n" ++
  "  slli a0, a0, 5              # a0 = i * 32 (byte offset)\n" ++
  "  la a1, ssz_zero_hashes\n" ++
  "  add a1, a1, a0              # a1 = &Z_i\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  ld t0, 0(a1);  sd t0, 0(a2)\n" ++
  "  ld t0, 8(a1);  sd t0, 8(a2)\n" ++
  "  ld t0, 16(a1); sd t0, 16(a2)\n" ++
  "  ld t0, 24(a1); sd t0, 24(a2)"

def ziskSszZeroHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszZeroHashesPrologue
  dataAsm     := sszZeroHashesDataSection
}

/-! ## ssz_merkleize_pow2 — PR-S6 pair-hash reduction loop

    SSZ pairwise merkleization for a power-of-two chunk count.
    Implements:

        while n > 1:
            for i in 0..n/2:
                chunks[i] = sha256_pair(chunks[2i], chunks[2i+1])
            n = n / 2
        root = chunks[0]

    Reads `n * 32` bytes from the caller's input pointer into
    `ssz_merkleize_scratch` (a 1024-byte working buffer), then
    reduces in place. Final root is copied to the caller's output
    pointer; the scratch buffer's first 32 bytes hold the same
    root after the call (intentional, reusable by chained
    merkleizers).

    Calling convention:
      a0 (input)  : ptr to `n * 32` chunk bytes
      a1 (input)  : n (power of two; 1 ≤ n ≤ 32)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (ZKVM_EOK)

    Clobbers t0..t6, a0..a2. Saves/restores s0..s6 and ra via
    its own 64-byte stack frame. Requires `sp` to point at
    writable RAM. -/
def sszMerkleizePow2Function : String :=
  "ssz_merkleize_pow2:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  # s0 = n (current chunk count); s5 = scratch base; s6 = caller out ptr\n" ++
  "  mv s0, a1\n" ++
  "  mv s6, a2\n" ++
  "  la s5, ssz_merkleize_scratch\n" ++
  "  # copy n*32 input bytes into scratch (in 8-byte units)\n" ++
  "  mv t0, a0\n" ++
  "  mv t1, s5\n" ++
  "  slli t2, s0, 5             # t2 = n * 32 bytes to copy\n" ++
  ".Lmrk_copy:\n" ++
  "  beqz t2, .Lmrk_iter\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -8\n" ++
  "  j .Lmrk_copy\n" ++
  ".Lmrk_iter:\n" ++
  "  # if n == 1: root is at scratch[0..32]\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lmrk_done\n" ++
  "  # pair-hash adjacent chunks into the lower half of scratch\n" ++
  "  srli s1, s0, 1             # s1 = n/2 = pair count\n" ++
  "  mv s2, s5                  # s2 = src pair ptr (64-byte step)\n" ++
  "  mv s3, s5                  # s3 = dst slot ptr (32-byte step)\n" ++
  ".Lmrk_pair:\n" ++
  "  beqz s1, .Lmrk_advance\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  li a1, 64\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  addi s2, s2, 64\n" ++
  "  addi s3, s3, 32\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lmrk_pair\n" ++
  ".Lmrk_advance:\n" ++
  "  srli s0, s0, 1             # n /= 2\n" ++
  "  j .Lmrk_iter\n" ++
  ".Lmrk_done:\n" ++
  "  # copy 32 bytes scratch[0..32] -> caller out ptr (s6)\n" ++
  "  ld t0,  0(s5);  sd t0,  0(s6)\n" ++
  "  ld t0,  8(s5);  sd t0,  8(s6)\n" ++
  "  ld t0, 16(s5);  sd t0, 16(s6)\n" ++
  "  ld t0, 24(s5);  sd t0, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ssz_merkleize_pow2`: probe BuildUnit that reads `n`
    from `INPUT_ADDR + 8` (u64 LE) and `n * 32` chunk bytes
    starting at `INPUT_ADDR + 16`, then calls `ssz_merkleize_pow2`
    and writes the 32-byte root to `OUTPUT_ADDR`.

    Test fixtures (in `scripts/codegen-zisk-ssz-merkleize-pow2-check.sh`):
      * n = 1, single zero chunk           → Z_0
      * n = 2, two zero chunks             → Z_1
      * n = 4, four zero chunks            → Z_2
      * n = 8, eight zero chunks           → Z_3
      * n = 16, sixteen zero chunks        → Z_4
      * n = 32, thirty-two zero chunks     → Z_5

    These align with the PR-S5 `Z_d` table values, so a passing
    probe confirms the merkleize loop walks the tree correctly. -/
def ziskSszMerkleizePow2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = n\n" ++
  "  addi a0, a3, 16             # a0 = chunks ptr\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, ssz_merkleize_pow2\n" ++
  "  j .Lzs6_done\n" ++
  zkvmSha256Function ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  ".Lzs6_done:"

def ziskSszMerkleizePow2DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 1024"

def ziskSszMerkleizePow2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszMerkleizePow2Prologue
  dataAsm     := ziskSszMerkleizePow2DataSection
}

/-! ## stateless_guest body — PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/
def statelessGuestEpilogue : String :=
  "  # PR-K7: overwrite OUTPUT[0..32] with keccak256 of the FIRST\n" ++
  "  # element of witness.headers (witness.headers[0]) if the list\n" ++
  "  # is non-empty; else keccak256(empty).\n" ++
  "  # \n" ++
  "  # Navigation:\n" ++
  "  #   ssz_start  = INPUT_ADDR + 16\n" ++
  "  #   offset_1   = LWU @ ssz_start +  4   (witness offset)\n" ++
  "  #   witness    = ssz_start + offset_1\n" ++
  "  #   inner_off2 = LWU @ witness  +  8   (headers offset)\n" ++
  "  #   hdrs_start = witness + inner_off2\n" ++
  "  #   offset_3   = LWU @ ssz_start + 16  (witness end)\n" ++
  "  #   hdrs_end   = ssz_start + offset_3\n" ++
  "  #   hdrs_len   = hdrs_end - hdrs_start\n" ++
  "  #   if hdrs_len > 0:\n" ++
  "  #     first_off  = LWU @ hdrs_start    (inner offset[0] = 4 * N)\n" ++
  "  #     el0_start  = hdrs_start + first_off\n" ++
  "  #     if first_off == 4 (N == 1):\n" ++
  "  #       el0_end  = hdrs_end\n" ++
  "  #     else (N >= 2):\n" ++
  "  #       el0_end  = hdrs_start + LWU @ hdrs_start + 4 (inner offset[1])\n" ++
  "  #     el0_len    = el0_end - el0_start\n" ++
  "  #   else:\n" ++
  "  #     hash empty (el0_len = 0)\n" ++
  "  li sp, 0xa0050000\n" ++
  "  li t3, 0x40000000\n" ++
  "  addi t3, t3, 16             # t3 = ssz_start\n" ++
  "  lwu t4, 4(t3)               # outer offset_1\n" ++
  "  add t5, t3, t4              # t5 = witness_addr\n" ++
  "  lwu t6, 8(t5)               # inner offset_2 (headers offset)\n" ++
  "  add a0, t5, t6              # a0 = hdrs_start (tentative data ptr)\n" ++
  "  lwu t6, 16(t3)              # outer offset_3 (witness end)\n" ++
  "  add t6, t3, t6              # t6 = hdrs_end\n" ++
  "  sub a1, t6, a0              # a1 = hdrs_len (tentative len)\n" ++
  "  beqz a1, .Lsg_call_keccak   # empty headers: hash empty\n" ++
  "  # Non-empty headers: read first inner offset to find element 0\n" ++
  "  lwu t4, 0(a0)               # t4 = first_inner_offset = 4 * N\n" ++
  "  add t5, a0, t4              # t5 = el0_start\n" ++
  "  li t3, 4\n" ++
  "  beq t4, t3, .Lsg_one_elem   # N == 1 → el0_end = hdrs_end (t6 already)\n" ++
  "  lwu t4, 4(a0)               # t4 = second_inner_offset\n" ++
  "  add t6, a0, t4              # t6 = el0_end (override)\n" ++
  ".Lsg_one_elem:\n" ++
  "  sub a1, t6, t5              # a1 = el0_len\n" ++
  "  mv a0, t5                   # a0 = el0_start\n" ++
  ".Lsg_call_keccak:\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR (hash field)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lsg_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lsg_done:"

def statelessGuestDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  dataAsm     := statelessGuestDataSection
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
  | "evm_sdiv"                  => some evmSdivV4Unit
  | "evm_sdiv_from_input"       => some evmSdivV4FromInputUnit
  | "evm_sdiv_v4"               => some evmSdivV4Unit
  | "evm_sdiv_v4_from_input"    => some evmSdivV4FromInputUnit
  | "evm_smod"                  => some evmSmodV4Unit
  | "evm_smod_from_input"       => some evmSmodV4FromInputUnit
  | "evm_smod_v4"               => some evmSmodV4Unit
  | "evm_smod_v4_from_input"    => some evmSmodV4FromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | "runtime_dispatcher"        => some runtimeDispatcherUnit
  | "stateless_guest"           => some statelessGuestUnit
  | "zisk_keccak_probe"         => some ziskKeccakProbeUnit
  | "zisk_keccak256_empty"      => some ziskKeccak256EmptyProbeUnit
  | "zisk_keccak256_abc"        => some ziskKeccak256AbcProbeUnit
  | "zisk_zkvm_keccak256"       => some ziskZkvmKeccak256ProbeUnit
  | "zisk_sha256_probe_le"      => some ziskSha256ProbeLeUnit
  | "zisk_zkvm_sha256"          => some ziskZkvmSha256ProbeUnit
  | "zisk_keccak256_from_input" => some ziskKeccak256FromInputProbeUnit
  | "zisk_headers_keccak_chain" => some ziskHeadersKeccakChainProbeUnit
  | "zisk_headers_keccak_array" => some ziskHeadersKeccakArrayProbeUnit
  | "zisk_headers_parent_hash"  => some ziskHeadersParentHashProbeUnit
  | "zisk_headers_validate_chain" => some ziskHeadersValidateChainProbeUnit
  | "zisk_witness_lookup_by_hash" => some ziskWitnessLookupByHashProbeUnit
  | "zisk_sha256_from_input"    => some ziskSha256FromInputProbeUnit
  | "zisk_ssz_pair_hash"        => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes"      => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2"   => some ziskSszMerkleizePow2ProbeUnit
  | _                           => none

/-- List of known program names, for use in CLI usage strings. -/
def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div", "evm_mod", "evm_sdiv", "evm_sdiv_v4", "input_echo",
   "evm_add_from_input", "evm_div_from_input", "evm_mod_from_input",
   "evm_sdiv_from_input", "evm_sdiv_v4_from_input",
   "evm_smod", "evm_smod_from_input",
   "evm_smod_v4", "evm_smod_v4_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2",
   "runtime_dispatcher",
   "stateless_guest",
   "zisk_keccak_probe",
   "zisk_keccak256_empty",
   "zisk_keccak256_abc",
   "zisk_zkvm_keccak256",
   "zisk_sha256_probe_le",
   "zisk_zkvm_sha256",
   "zisk_keccak256_from_input",
   "zisk_headers_keccak_chain",
   "zisk_headers_keccak_array",
   "zisk_headers_parent_hash",
   "zisk_headers_validate_chain",
   "zisk_witness_lookup_by_hash",
   "zisk_sha256_from_input",
   "zisk_ssz_pair_hash",
   "zisk_ssz_zero_hashes",
   "zisk_ssz_merkleize_pow2"]

end EvmAsm.Codegen
