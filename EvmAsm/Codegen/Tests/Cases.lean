/-
  EvmAsm.Codegen.Tests.Cases

  Per-opcode regression test registry. Each `OpcodeTestCase` is a
  bytecode + expected output bytes; the bash runner
  (`scripts/codegen-opcodes-check.sh`) iterates the list, emitting
  one ELF per case via `lake exe codegen --test-case <name>` and
  diffing the first 32 bytes of `ziskemu`'s public output against
  `expectedOutHex`.

  Adding a regression test = appending one record to
  `opcodeTestCases` below.
-/

import EvmAsm.Codegen.Programs

namespace EvmAsm.Codegen.Tests

open EvmAsm.Codegen

/-- One per-opcode regression test wrapped around the M5b dispatcher
    (`tinyInterpRegistry`). The bytecode bakes into `.data`; the
    expected output is the first 32 bytes of `OUTPUT_ADDR` (i.e. the
    EVM stack top after STOP, written by `evmAddEpilogue`). -/
structure OpcodeTestCase where
  /-- Identifier (becomes `gen-out/<name>.{s,o,elf,output}`). -/
  name           : String
  /-- EVM bytecode as a comma-separated `.byte` directive payload
      (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`). -/
  bytecode       : String
  /-- Expected first 32 bytes of `OUTPUT_ADDR` as 64 hex chars. -/
  expectedOutHex : String

/-- Registry of test cases. M5a/M5b's two original bytecodes are
    migrated as `add_basic` / `add_chain`; M6b adds ~20 more — one
    per singleton opcode, one per parametric family, plus a kitchen-
    sink case that chains multiple opcodes.

    EVM convention reminder: stack values are 256-bit big-endian;
    `OUTPUT_ADDR` receives the post-STOP stack top as 32 bytes,
    interpreted as four little-endian u64 limbs. So `0x42` on the
    EVM stack surfaces as `42 00 00 00 00 00 00 00 ...` (low byte
    first in the LE limb encoding).

    Binary opcodes pop top (`a`) then second (`b`); the order
    matters for non-commutative ones (`SUB`, `DIV`, `MOD`, `SHR`,
    comparisons). For SUB specifically: pushes `a - b` where `a`
    was the top — so `PUSH1 0x03; PUSH1 0x05; SUB` yields `5 - 3 = 2`. -/
def opcodeTestCases : List OpcodeTestCase :=
  [ -- ## Baseline (migrated from M5a/M5b)
    -- PUSH1 0xff; PUSH1 0x01; ADD; STOP → 0x100
    { name           := "add_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"
      expectedOutHex := "0001000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP → 0x60
    { name           := "add_chain"
      bytecode       := "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
    -- ## Singletons (16, one per fixed-shape opcode)
  , -- PUSH1 0x03; PUSH1 0x05; SUB; STOP → 5 - 3 = 2
    { name           := "sub_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x03, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x04; MUL; STOP → 4 * 3 = 12 = 0x0c
    { name           := "mul_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x04, 0x02, 0x00"
      expectedOutHex := "0c00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x7f; PUSH1 0x00; SIGNEXTEND; STOP — byte 0 of 0x7f has
    -- high bit 0, so sign-extension is a no-op → 0x7f.
    { name           := "signextend_basic"
      bytecode       := "0x60, 0x7f, 0x60, 0x00, 0x0b, 0x00"
      expectedOutHex := "7f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x03; LT; STOP → 3 < 5 = 1
    { name           := "lt_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x03, 0x10, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; GT; STOP → 5 > 3 = 1
    { name           := "gt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x11, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x01; SLT; STOP — signed `a < b` with a=1, b=2 → 1
    { name           := "slt_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x01, 0x12, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; SGT; STOP — signed `a > b` with a=5, b=3 → 1
    { name           := "sgt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x13, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x42; EQ; STOP → 1
    { name           := "eq_basic"
      bytecode       := "0x60, 0x42, 0x60, 0x42, 0x14, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; ISZERO; STOP → 1
    { name           := "iszero_basic"
      bytecode       := "0x60, 0x00, 0x15, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; AND; STOP → 0xff & 0x0f = 0x0f
    { name           := "and_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x16, 0x00"
      expectedOutHex := "0f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xa0; OR; STOP → 0xa0 | 0x0f = 0xaf
    { name           := "or_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xa0, 0x17, 0x00"
      expectedOutHex := "af00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; XOR; STOP → 0xff ^ 0x0f = 0xf0
    { name           := "xor_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x18, 0x00"
      expectedOutHex := "f000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; NOT; STOP → ~0 (32 bytes of 0xff)
    { name           := "not_basic"
      bytecode       := "0x60, 0x00, 0x19, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH32 0x0102…20; PUSH1 0x1f; BYTE; STOP — byte 31 (LSByte
    -- big-endian) of 0x0102…1f20 is 0x20.
    { name           := "byte_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x60, 0x1f, 0x1a, 0x00"
      expectedOutHex := "2000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x80; PUSH1 0x04; SHR; STOP — shift=4 on top, value=0x80
    -- → 0x80 >> 4 = 0x08.
    { name           := "shr_basic"
      bytecode       := "0x60, 0x80, 0x60, 0x04, 0x1c, 0x00"
      expectedOutHex := "0800000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0xff; POP; STOP — POP removes 0xff, leaves 0x42
    { name           := "pop_basic"
      bytecode       := "0x60, 0x42, 0x60, 0xff, 0x50, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## Family representatives (3, one per parametric family)
  , -- PUSH32 0x0102…20; STOP — the 32 immediate bytes are read
    -- big-endian into the EVM word; surfaced LE in OUTPUT_ADDR.
    { name           := "push32_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x00"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH1 0x42; DUP1; ADD; STOP — DUP1 makes stack [0x42, 0x42];
    -- ADD → 0x84.
    { name           := "dup1_basic"
      bytecode       := "0x60, 0x42, 0x80, 0x01, 0x00"
      expectedOutHex := "8400000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x02; SWAP1; SUB; STOP — SWAP1 yields top=5,
    -- second=2; SUB → 5 - 2 = 3.
    { name           := "swap1_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x02, 0x90, 0x03, 0x00"
      expectedOutHex := "0300000000000000000000000000000000000000000000000000000000000000" }
    -- ## Kitchen sink (cross-family chain)
  , -- PUSH1 0x03; PUSH1 0x05; MUL; PUSH1 0x10; SUB; STOP
    -- MUL: 5*3=15=0x0f. SUB: 0x10 - 0x0f = 0x01.
    { name           := "arith_mix"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x02, 0x60, 0x10, 0x03, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## M7 memory opcodes (MLOAD / MSTORE / MSTORE8)
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x00; MLOAD; STOP
    -- MSTORE writes 0x42 big-endian to memory[0..32]; MLOAD reads it
    -- back to the stack. EVM word = 0x42, on the stack as four LE u64
    -- limbs with limb 0 = 0x42 (decimal 66).
    { name           := "mstore_mload"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; PUSH1 0x00; MSTORE8; PUSH1 0x00; MLOAD; STOP
    -- MSTORE8 writes one byte (0xff) at memory[0]. MLOAD reads 32 bytes
    -- big-endian → EVM word = 0xff · 2^248. As LE limbs that's
    -- [0, 0, 0, 0xff00000000000000]; limb 3 written to bytes 24..31
    -- in LE order ends with 0xff at byte 31.
    { name           := "mstore8_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x00, 0x53, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "00000000000000000000000000000000000000000000000000000000000000ff" }
    -- ## M8 unsigned division opcodes
    -- (SDIV / SMOD deferred: their verified bodies use a saved-ra-ret
    -- pattern that bypasses the dispatcher's standard wrapper tail;
    -- integrating them needs a trampoline approach planned as the
    -- next codegen PR.)
  , -- PUSH1 0x02; PUSH1 0x0a; DIV; STOP — 10 / 2 = 5
    { name           := "div_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"
      expectedOutHex := "0500000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x0a; MOD; STOP — 10 % 3 = 1
    { name           := "mod_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x0a, 0x06, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  ]

/-- Find a test case by name. -/
def lookupTestCase (name : String) : Option OpcodeTestCase :=
  opcodeTestCases.find? (fun tc => tc.name == name)

/-- All test case names, one per line — emitted by
    `--list-test-cases` for the bash runner to enumerate. -/
def testCaseNames : List String :=
  opcodeTestCases.map OpcodeTestCase.name

/-- Build a `BuildUnit` that runs `tc.bytecode` through the M5b
    dispatcher (`tinyInterpRegistry`). The exit body is
    `evmAddEpilogue`, which copies the 32 bytes at `[x12]` (the post-
    STOP stack top) to `OUTPUT_ADDR`. -/
def buildTestCaseUnit (tc : OpcodeTestCase) : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tc.bytecode

end EvmAsm.Codegen.Tests
