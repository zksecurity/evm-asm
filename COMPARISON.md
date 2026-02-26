# EVM Opcode Assembly Comparison: evm-asm vs Compiled Rust (ethrex-style)

## Overview

This document compares hand-written RISC-V assembly for EVM opcodes (evm-asm) against
LLVM-compiled Rust using `ethereum-types::U256` (as used by ethrex) targeting `riscv32im`.

**evm-asm**: Hand-written straight-line RV32IM assembly in Lean 4. 256-bit values stored
as 8 little-endian 32-bit limbs in memory. Register x12 = EVM stack pointer. All
instructions are straight-line (no branches) except SHR which uses dispatch jumps.

**Compiled Rust**: `ethereum-types::U256` (internally `[u64; 4]`) compiled with
`rustc --target riscv32im-unknown-none-elf -O2` (opt-level=2, thin LTO, codegen-units=1,
panic=abort). On riscv32, each u64 decomposes into 2×u32 registers, so also effectively
8×32-bit limbs, but the u64 grouping creates extra carry/borrow logic.

**Three comparison layers**:
- **Layer 1**: Pure U256 arithmetic (fair algorithm-vs-algorithm comparison)
- **Layer 2**: With stack operations (slice indexing + offset management)
- **Layer 3**: Full handler with gas checking + stack bounds + error codes

## Summary Table

| Opcode | evm-asm | Rust L1 | Rust L2 | Rust L3 | L1/asm | L3/asm | Notes |
|--------|--------:|--------:|--------:|--------:|-------:|-------:|-------|
| POP    |       1 |       2 |       4 |      19 |   2.0x |  19.0x | evm-asm: 1 ADDI; Rust: li+ret |
| PUSH0  |       9 |       9 |      19 |      35 |   1.0x |   3.9x | Identical at L1 |
| DUP1   |      17 |      17 |      34 |      38 |   1.0x |   2.2x | Identical at L1 |
| SWAP1  |      32 |     129 |      67 |      80 |   4.0x |   2.5x | Rust L1: byte-level lbu/sb! |
| ADD    |      62 |      87 |     112 |     122 |   1.4x |   2.0x | u64 carry chain adds branches |
| SUB    |      62 |     100 |     125 |     135 |   1.6x |   2.2x | u64 borrow chain + spills |
| AND    |      33 |      33 |      60 |      71 |   1.0x |   2.2x | Identical at L1 |
| OR     |      33 |      33 |      60 |      71 |   1.0x |   2.2x | Identical at L1 |
| XOR    |      33 |      33 |      60 |      71 |   1.0x |   2.2x | Identical at L1 |
| NOT    |      24 |      25 |      33 |      44 |   1.0x |   1.8x | Near-identical at L1 |
| ISZERO |      24 |      32 |      57 |      68 |   1.3x |   2.8x | Rust uses early-exit branches |
| LT     |      54 |    ~68* |      97 |     107 |   1.3x |   2.0x | *includes partial_cmp callee |
| GT     |      54 |    ~72* |     101 |     111 |   1.3x |   2.1x | *includes partial_cmp callee |
| EQ     |      41 |   ~29+M |      96 |     107 |  ~1.5x |   2.6x | Rust calls memcmp |
| SHR    |   23-78† |     226 |     272 |     293 |  ~3.6x |   4.7x | evm-asm: †executed path varies |

\* LT/GT call `U256::partial_cmp` (~40 additional instructions in callee).
† SHR evm-asm: 302 static instructions, but 23-78 executed depending on shift amount.

## Analysis

### Key Finding: Bitwise Operations are Optimal in Both

For AND, OR, XOR, the compiler produces **exactly the same instruction count** (33) as
the hand-written assembly at Layer 1. The compiler batches all loads before ALU operations
(better for pipelining), while evm-asm interleaves load-compute-store per limb. Both
produce 16 LW + 8 ALU + 8 SW + 1 ret/ADDI = 33.

NOT is essentially identical: Rust uses 25 instructions (8 LW + 8 NOT + 8 SW + 1 ret)
vs evm-asm's 24 (8 LW + 8 XORI + 8 SW). The single extra instruction is `ret`.

DUP1 is also identical at 17 instructions. PUSH0 at 9 instructions.

### Arithmetic: u64 Representation Hurts on riscv32

**ADD**: evm-asm uses a clean 8-limb carry chain (62 instructions, 0 branches):
```
Limb 0:   LW a, LW b, ADD, SLTU(carry), SW       — 5 instrs
Limbs 1-7: LW a, LW b, ADD, SLTU, ADD(carry), SLTU, OR(carry), SW  — 8 instrs each
ADDI sp                                            — 1 instr
Total: 5 + 7×8 + 1 = 62
```

Rust's `u256_add` produces 87 instructions with 14 branches. The extra complexity comes
from the `[u64; 4]` internal representation: on riscv32, adding two u64 values requires
a 2-register add with carry, and propagating carry across u64 boundaries creates
conditional branches (checking whether the high half carry propagates).

**SUB**: Even worse — Rust produces 100 instructions with 13 branches (evm-asm: 62).
The u64 borrow propagation requires register spills (4 callee-saved registers pushed
to stack).

### SWAP1: Dramatic Difference from Byte-Level Operations

The most striking difference: Rust's `core::mem::swap` for `U256` compiles to
**byte-level** load/store operations (`lbu`/`sb`) rather than word-level (`lw`/`sw`).
This produces 129 instructions (64 `lbu` + 64 `sb` + 1 `ret`) vs evm-asm's 32
instructions (16 `lw` + 16 `sw`).

This is a **4.0x penalty** at Layer 1, and each byte operation moves 1/4 the data.
In a zkVM where each instruction has roughly equal cost, this is even worse than 4x
because 4 byte loads ≠ 1 word load in useful work.

Interestingly, at Layer 2 (stack_op_swap1 = 67 instrs), the slice-based `swap()` uses
word-level operations, making it more efficient than the Layer 1 pure pointer swap.

### Comparison Operations: Call Overhead

LT, GT, and EQ in Rust delegate to library functions:
- **LT/GT**: Call `U256::partial_cmp` (~40 instructions with 4 branches) then check result
- **EQ**: Calls `memcmp` (external, potentially optimized)

The `partial_cmp` function compares from the most-significant u64 downward, using
early exit when a difference is found. This means:
- Best case (differ in top u64): ~13 executed instructions
- Worst case (equal through all u64s): ~37 executed instructions

In contrast, evm-asm's LT processes all 8 limbs unconditionally (54 instructions),
which is deterministic and predictable for zkVM cost estimation.

### SHR: Both Are Complex, Different Tradeoffs

**evm-asm** (302 static instructions, 23-78 executed):
- Dispatch on `limb_shift` (0-7) via cascade of BEQ branches
- Each path has straight-line merge operations for the relevant limbs
- Most paths execute far fewer than 302 instructions

**Rust** (226 static instructions + calls):
- Delegates to `U256::shr` which processes u64-level shifts
- Includes panic path for `as_u32()` overflow
- More branches due to u64-level shift logic

The evm-asm approach trades code size (302 total) for execution efficiency (23-78
executed). The Rust approach has smaller static size but more branches per execution.

### Layer 2 vs Layer 3 Overhead

The overhead from stack operations (Layer 2) and full handler (Layer 3) is consistent:

| Component | Typical overhead |
|-----------|----------------:|
| Stack bounds check | 3-5 instrs (load len, compare, branch) |
| Gas deduction | 3-5 instrs (load gas, sub, compare, branch) |
| Error return paths | 5-10 instrs (store error code, cleanup, ret) |
| Function prologue/epilogue | 4-8 instrs (save/restore ra, frame) |
| Slice indexing (× element size) | 3-6 instrs per access |

Typical Layer 3/Layer 1 ratio: **1.5-2.5x** for most opcodes.

### Branch Count Impact on zkVM Cost

In a zkVM (SP1, RISC Zero), every instruction costs roughly the same to prove.
**Branches are not free** — they still consume a cycle. The key question is whether
branching code executes fewer total instructions than straight-line code.

| Opcode | evm-asm branches | Rust L1 branches | Winner |
|--------|----------------:|------------------:|--------|
| ADD    | 0               | 14                | evm-asm (fewer total instrs) |
| SUB    | 0               | 13                | evm-asm (fewer total instrs) |
| AND    | 0               | 0                 | Tie |
| OR     | 0               | 0                 | Tie |
| XOR    | 0               | 0                 | Tie |
| NOT    | 0               | 0                 | Tie |
| ISZERO | 0               | 5                 | evm-asm (fewer total instrs) |
| LT     | 0               | 2+4(callee)       | evm-asm (fewer total instrs) |
| GT     | 0               | 3+4(callee)       | evm-asm (fewer total instrs) |
| EQ     | 0               | 2+?(memcmp)       | Depends on memcmp impl |
| SHR    | 2-13(executed)  | 32                 | evm-asm (fewer executed) |

For most opcodes, evm-asm's straight-line approach wins because it avoids branch
instructions entirely while still using fewer total instructions.

## Per-Opcode Assembly Comparison

### ADD

**evm-asm** (62 instructions, 0 branches):
```asm
# Limb 0: sum, carry
lw   x7, 0(x12)        # a[0]
lw   x6, 32(x12)       # b[0]
add  x7, x7, x6        # sum = a[0]+b[0]
sltu x5, x7, x6        # carry = sum < b[0]
sw   x12, x7, 32       # result[0] = sum
# Limb 1: sum + carry_in, carry_out = carry1 | carry2
lw   x7, 4(x12)        # a[1]
lw   x6, 36(x12)       # b[1]
add  x7, x7, x6        # psum = a[1]+b[1]
sltu x11, x7, x6       # carry1 = psum < b[1]
add  x7, x7, x5        # result = psum + carry_in
sltu x6, x7, x5        # carry2 = result < carry_in
or   x5, x11, x6       # carry_out = carry1 | carry2
sw   x12, x7, 36       # result[1]
# ... (limbs 2-7 identical pattern) ...
addi x12, x12, 32      # pop operand
```

**Compiled Rust** (87 instructions, 14 branches):
```asm
# Loads a[0..1] and b[0..1] as u64 pairs
lw   a3, 0(a1)         # a.0[0] (low half of first u64)
lw   a4, 4(a1)         # a.0[0] (high half)
lw   a5, 4(a2)         # b.0[0] (high half)
lw   a6, 0(a2)         # b.0[0] (low half)
add  a4, a5, a4        # high = a_hi + b_hi
add  a3, a6, a3        # low = a_lo + b_lo
sltu a7, a3, a6        # carry from low addition
add  a4, a4, a7        # high += carry
beq  a4, a5, .L_carry  # if high==b_hi, carry depends on low
sltu a7, a4, a5        # else carry = high < b_hi
# ... complex carry propagation with branches ...
```

The u64 internal representation means the compiler must handle carry propagation
both *within* each u64 (low→high half) and *between* u64s, creating conditional
control flow. The evm-asm 32-bit limb approach eliminates this entirely.

### AND / OR / XOR (identical structure)

**evm-asm** (33 instructions):
```asm
# Per limb: LW a, LW b, OP, SW — repeated 8 times
lw   x7, 0(x12)        # a[0]
lw   x6, 32(x12)       # b[0]
and  x7, x7, x6        # a[0] & b[0]
sw   x12, x7, 32       # result[0]
# ... (limbs 1-7) ...
addi x12, x12, 32      # pop operand
```

**Compiled Rust** (33 instructions):
```asm
# Batch loads, then ALU, then stores
lw   a3, 0(a1)         # a[0]
lw   a4, 4(a1)         # a[1]
lw   a5, 8(a1)         # a[2]
lw   a6, 12(a1)        # a[3]
lw   a7, 0(a2)         # b[0]
lw   t0, 4(a2)         # b[1]
lw   t1, 8(a2)         # b[2]
lw   t2, 12(a2)        # b[3]
and  a3, a7, a3        # a[0] & b[0]
lw   a7, 16(a1)        # a[4]
# ... interleaved loads and ops ...
sw   a3, 0(a0)         # result[0]
sw   a4, 4(a0)         # result[1]
# ... stores ...
ret
```

Both produce exactly 33 instructions: 16 LW + 8 AND + 8 SW + 1 (ADDI/ret).
The compiler achieves optimal code here because bitwise operations on `[u64; 4]`
decompose cleanly into independent 32-bit operations with no carries.

### NOT

**evm-asm** (24 instructions):
```asm
lw   x7, 0(x12)
xori x7, x7, -1        # NOT via XOR with all-ones
sw   x12, x7, 0
# ... 7 more limbs ...
```

**Compiled Rust** (25 instructions):
```asm
lw   a2, 0(a1)
# ... load all 8 limbs ...
not  a2, a2            # pseudo-instruction for xori a2, a2, -1
# ... NOT all 8 ...
sw   a2, 0(a0)
# ... store all 8 ...
ret
```

Effectively identical. The 1-instruction difference is the `ret` vs evm-asm's
in-place operation (no function call overhead since it's inlined in the dispatcher).

### ISZERO

**evm-asm** (24 instructions, 0 branches):
```asm
# OR-reduce all 8 limbs into x7
lw   x7, 0(x12)
lw   x6, 4(x12)
or   x7, x7, x6
lw   x6, 8(x12)
or   x7, x7, x6
# ... load+OR limbs 3-7 ...
sltiu x7, x7, 1        # x7 = (x7 == 0) ? 1 : 0
# Store 256-bit result
sw   x12, x7, 0        # result[0] = boolean
sw   x12, x0, 4        # result[1..7] = 0
# ... 6 more zero stores ...
```

**Compiled Rust** (32 instructions, 5 branches):
```asm
# Check pairs with early exit
lw   a2, 0(a1)
lw   a3, 4(a1)
or   a2, a2, a3
bnez a2, .not_zero      # early exit if nonzero
lw   a2, 8(a1)
lw   a3, 12(a1)
or   a2, a2, a3
bnez a2, .not_zero
# ... check remaining pairs ...
```

Rust uses early-exit branches (checking 2 limbs at a time), which could be faster
for non-zero values but adds branch prediction complexity. For zkVM where every
instruction counts equally, evm-asm's branchless approach is preferable.

### SWAP1

**evm-asm** (32 instructions):
```asm
# Per limb: LW from top, LW from second, SW to top, SW to second
lw   x7, 0(x12)
lw   x6, 32(x12)
sw   x12, x6, 0
sw   x12, x7, 32
# ... 7 more limb swaps ...
```

**Compiled Rust** (129 instructions!):
```asm
# Byte-by-byte swap via core::mem::swap
lbu  a2, 0(a0)         # load byte 0 of a
lbu  a3, 1(a0)
lbu  a4, 2(a0)
lbu  a5, 3(a0)
lbu  a6, 0(a1)         # load byte 0 of b
lbu  a7, 1(a1)
lbu  t0, 2(a1)
lbu  t1, 3(a1)
sb   a6, 0(a0)         # store b's bytes to a
sb   a7, 1(a0)
sb   t0, 2(a0)
sb   t1, 3(a0)
# ... 28 more bytes to swap (7 more groups of 4) ...
```

This is the most dramatic difference: **4.0x** more instructions because
`core::mem::swap` generates byte-level operations for the 32-byte U256 type,
while evm-asm uses word-level loads/stores. Each `lbu`/`sb` moves 1 byte vs
`lw`/`sw` moving 4 bytes.

### SHR

**evm-asm** (302 static, 23-78 executed):
Phase A checks if shift >= 256, Phase B extracts bit_shift/limb_shift,
Phase C dispatches to one of 8 shift bodies (ls0-ls7), each body processes
only the relevant limbs using `srl`/`sll`/`and`/`or` merge operations.

**Compiled Rust** (226 static, many branches + calls):
Uses U256::shr which operates at the u64 level, plus calls `partial_cmp`
for the >= 256 check, and includes a panic path for `as_u32()` overflow.
The u64-level shift logic creates additional complexity on riscv32.

## Cross-Cutting Analysis

### U256 Internal Representation

| Aspect | evm-asm | Rust (ethereum-types) |
|--------|---------|----------------------|
| Internal type | 8 × u32 in memory | [u64; 4] → 8 × u32 on rv32 |
| Layout | Little-endian limbs at sp | Little-endian limbs on stack/heap |
| Carry propagation | Per-32-bit limb (uniform) | Per-64-bit u64 (2-step on rv32) |
| Register pressure | x5,x6,x7,x11,x12 (5 regs) | Uses a0-a7,t0-t6,s0-s4 (up to 18) |

The u64 internal representation is the primary source of overhead for arithmetic
operations. On riscv32, every u64 operation becomes a 2-register operation with
carry propagation, and cross-u64 carries require conditional branches.

### Stack Architecture

| Aspect | evm-asm | Rust |
|--------|---------|------|
| Stack pointer | Dedicated register (x12) | Via function arguments |
| Element access | Direct offset from x12 | Slice pointer + index * 32 |
| Push/Pop | ADDI x12, ±32 | Modify offset variable |
| Bounds checking | None (trusted) | Slice bounds check (can panic) |

evm-asm's dedicated stack pointer register (x12) allows single-instruction
stack manipulation (POP = 1 instruction). Rust's slice-based approach requires
loading the pointer, computing the offset, and potentially checking bounds.

### Overhead Budget (Layer 3 vs Layer 1)

| Overhead source | Typical cost |
|-----------------|------------:|
| Gas deduction (load + sub + compare) | 3-5 instrs |
| Gas underflow branch | 1-2 instrs |
| Stack depth check (load + compare) | 2-4 instrs |
| Stack underflow branch | 1-2 instrs |
| Function prologue (save ra, s-regs) | 2-6 instrs |
| Function epilogue (restore + ret) | 2-6 instrs |
| Error return paths | 2-4 instrs per path |
| **Total overhead** | **~15-40 instrs** |

### zkVM Cost Model Implications

In zero-knowledge virtual machines (SP1, RISC Zero), the cost model is:
- Each instruction takes ~1 cycle to prove
- Memory operations (LW/SW) ≈ ALU operations in cost
- Branches cost the same as other instructions (no prediction benefit)
- Function calls (CALL/RET) are just branch + register save, same cost

Under this model:
1. **Straight-line code is king**: No wasted cycles on untaken branches
2. **Fewer instructions = lower cost**: Even if the branch is predicted correctly
   on a real CPU, in zkVM every instruction in the trace is proven
3. **evm-asm's approach is well-suited**: Straight-line, minimal register pressure,
   no function calls for simple operations

### Recommendations

For a zkVM EVM implementation optimizing for prover cost:

1. **Use 32-bit limb representation** (8 × u32) rather than 64-bit (4 × u64) to
   avoid the carry/borrow branch overhead on riscv32.

2. **Avoid `core::mem::swap`** for U256 — use explicit word-level swap loops instead.

3. **Prefer straight-line code** over early-exit branches for operations that always
   process all limbs (ADD, SUB, AND, OR, XOR, NOT, ISZERO, EQ).

4. **For comparison operations (LT/GT)**, straight-line borrow-chain (evm-asm style)
   is better than the library's top-down early-exit comparison.

5. **Bitwise operations are already optimal** in compiled Rust — no hand-tuning needed.

## Reproduction

### Building the Rust crate
```bash
cd rust-u256-asm
rustup target add riscv32im-unknown-none-elf
RUSTFLAGS="--emit asm" cargo build --release --target riscv32im-unknown-none-elf
# Assembly output: target/riscv32im-unknown-none-elf/release/deps/u256_asm_compare-*.s
```

### evm-asm source
Located in `evm-asm/EvmAsm/Evm/`:
- `Arithmetic.lean` — ADD, SUB
- `Bitwise.lean` — AND, OR, XOR, NOT
- `Comparison.lean` — ISZERO, LT, GT, EQ
- `StackOps.lean` — POP, PUSH0, DUP1, SWAP1
- `Shift.lean` — SHR
