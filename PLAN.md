# PLAN: Verified RISC-V EVM Implementation

> **Agent instruction**: Keep this file up to date as you work. When you finish
> implementing an opcode or task, move it to the "Done" list under
> "Current Status", update any counts or details that changed, and note any
> new sub-tasks you discovered. Check this file at the start of each session
> to pick up where the last agent left off.

Goal: implement and verify the EVM state transition function as RISC-V macro
assembly programs, for use as a zkEVM. Each EVM opcode becomes a verified
RISC-V subroutine operating on 256-bit stack words in memory.

Reference spec: `execution-specs/src/ethereum/forks/shanghai/vm/` (Python).

## Current Status

**Done (10 opcodes with full 256-bit specs):**
- Arithmetic: ADD, SUB
- Bitwise: AND, OR, XOR, NOT
- Comparison: ISZERO, LT, GT, EQ

**Infrastructure:**
- EvmWord = BitVec 256, stored as 8 little-endian 32-bit limbs
- Stack pointer in x12, stack grows upward, 32 bytes per element
- evmWordIs/evmStackIs separation logic assertions
- xperm/xsimp tactics for automated proof composition
- cpsTriple_seq_with_perm for composing multi-limb specs

---

## Phase 1: Complete Comparison & Simple Arithmetic

Each task below is one file change. Follow the existing patterns in
`Evm/Comparison.lean` and `Evm/Arithmetic.lean`.

### 1.1 GT (Greater Than)
- **File**: `Evm/Comparison.lean`
- **Approach**: GT(a,b) = LT(b,a). Swap operand load order, reuse LT's
  borrow-chain logic. Same instruction count as LT (54 instr).
- **Reference**: `execution-specs/.../instructions/comparison.py:greater_than`
- **Pattern**: Copy `evm_lt` program, swap the LW offsets for a and b limbs.
  Write `gt_limb0_spec`, `gt_limb_carry_spec`, then compose.

### 1.2 EQ (Equality)
- **File**: `Evm/Comparison.lean`
- **Approach**: XOR all 8 limb pairs, OR-reduce to single word, SLTIU to
  boolean. ~33 instr (8×LW+LW+XOR + 7×OR + SLTIU + 8×SW + ADDI).
- **Reference**: `execution-specs/.../instructions/comparison.py:equal`
- **Pattern**: Similar to ISZERO but XOR pairs first.

### 1.3 SLT (Signed Less Than)
- **File**: `Evm/Comparison.lean`
- **Approach**: Compare MSB limbs (limb 7) with signed comparison (SLT
  instruction), then if equal fall through to unsigned comparison of
  remaining limbs. Uses BEQ/BNE branching + cpsBranch.
- **Reference**: `execution-specs/.../instructions/comparison.py:signed_less_than`

### 1.4 SGT (Signed Greater Than)
- **File**: `Evm/Comparison.lean`
- **Approach**: SGT(a,b) = SLT(b,a). Swap operand order like GT.

---

## Phase 2: Stack Manipulation

These are critical — almost every EVM program uses PUSH/DUP/SWAP/POP.

### 2.1 POP
- **File**: `Evm/StackOps.lean` (new)
- **Approach**: Just advance sp by 32 bytes (`ADDI x12, x12, 32`).
  1 instruction. Trivial spec.
- **Reference**: `execution-specs/.../instructions/stack.py:pop`

### 2.2 PUSH0
- **File**: `Evm/StackOps.lean`
- **Approach**: Decrement sp by 32, store 0 to all 8 limbs.
  `ADDI x12, x12, -32` + 8×(`SW x0, x12, offset`). 9 instructions.
- **Note**: Only PUSH0 for now. PUSH1-32 need EVM bytecode parsing
  infrastructure (the immediate comes from EVM code, not RISC-V code).

### 2.3 DUP1
- **File**: `Evm/StackOps.lean`
- **Approach**: Decrement sp by 32, copy 8 limbs from old top to new top.
  `ADDI x12, x12, -32` + 8×(`LW x7, x12, old_offset` + `SW x12, x7, new_offset`).
  17 instructions.
- **Pattern**: DUP2-16 are similar but with different source offsets.
  Implement DUP1 first, then generalize to `dup_n_spec`.

### 2.4 SWAP1
- **File**: `Evm/StackOps.lean`
- **Approach**: Swap 8 limb pairs between top two stack elements.
  8×(`LW x7, x12, top_off` + `LW x6, x12, second_off` +
  `SW x12, x6, top_off` + `SW x12, x7, second_off`). 32 instructions.
- **Pattern**: SWAP2-16 differ only in the second element's offset.

### 2.5 Generalize DUP/SWAP
- **File**: `Evm/StackOps.lean`
- **Approach**: Write `evm_dup (n : Nat)` and `evm_swap (n : Nat)` as
  Lean functions producing `Program`. Prove generic specs parameterized by n.
  This covers DUP1-16 and SWAP1-16 (32 opcodes) with one proof each.

---

## Phase 3: Remaining Bitwise Operations

### 3.1 BYTE (Extract byte from word)
- **File**: `Evm/Bitwise.lean`
- **Approach**: Input is byte index i (0-31, big-endian) and value x.
  If i >= 32, result is 0. Otherwise, extract byte at position (31-i).
  Need shift-and-mask logic. Use SRL + ANDI per limb.
- **Reference**: `execution-specs/.../instructions/bitwise.py:get_byte`

### 3.2 SHL (Shift Left)
- **File**: `Evm/Shift.lean` (new)
- **Approach**: If shift >= 256, result is 0. Otherwise, shift amount =
  shift_limbs × 32 + shift_bits. Move limbs, then shift within limbs
  (SLL + SRL for cross-limb bits). Uses loops or unrolled code.
- **Reference**: `execution-specs/.../instructions/bitwise.py:bitwise_shl`
- **Note**: This is significantly more complex than AND/OR/XOR. Consider
  special-casing small shifts (< 32 bits) first.

### 3.3 SHR (Shift Right Logical)
- **File**: `Evm/Shift.lean`
- **Approach**: Mirror of SHL but in the opposite direction.
- **Reference**: `execution-specs/.../instructions/bitwise.py:bitwise_shr`

### 3.4 SAR (Shift Right Arithmetic)
- **File**: `Evm/Shift.lean`
- **Approach**: Like SHR but fills with sign bit instead of 0.
- **Reference**: `execution-specs/.../instructions/bitwise.py:bitwise_sar`

---

## Phase 4: Remaining Arithmetic

### 4.1 MUL (256-bit Multiply)
- **File**: `Evm/Multiply.lean` (new)
- **Approach**: Schoolbook multiplication of 8×8 limbs using RISC-V MUL/MULHU.
  Only need low 256 bits (8 output limbs). Each partial product is
  `a_i × b_j` contributing to limb `(i+j)` with carry to `(i+j+1)`.
  ~200+ instructions. Consider a loop-based approach.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:mul`
- **Note**: This is the hardest single opcode. Break into sub-tasks:
  1. Single-limb multiply helper (MUL + MULHU for lo/hi)
  2. Accumulate partial products with carry chain
  3. Full 8×8 composition

### 4.2 DIV and MOD
- **File**: `Evm/DivMod.lean` (new)
- **Approach**: 256-bit unsigned division. Use shift-and-subtract algorithm
  (binary long division). ~500+ instructions unrolled, or loop-based.
  DIV returns quotient, MOD returns remainder. Implement together since
  division produces both.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:div`, `:mod`
- **Note**: Division by zero returns 0 (EVM convention, not trap).

### 4.3 SDIV and SMOD (Signed)
- **File**: `Evm/DivMod.lean`
- **Approach**: Check signs of operands, compute unsigned div/mod,
  apply sign correction. Reuse DIV/MOD.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:sdiv`, `:smod`

### 4.4 ADDMOD and MULMOD
- **File**: `Evm/ModArith.lean` (new)
- **Approach**: ADDMOD(a,b,N) = (a+b) mod N. Need 257-bit intermediate
  (carry bit from 256-bit add). MULMOD needs 512-bit intermediate.
  Both use DIV/MOD as subroutine.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:addmod`, `:mulmod`

### 4.5 EXP (Exponentiation)
- **File**: `Evm/Exp.lean` (new)
- **Approach**: Square-and-multiply using MUL. Loop over exponent bits.
  Needs loop infrastructure.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:exp`

### 4.6 SIGNEXTEND
- **File**: `Evm/Arithmetic.lean`
- **Approach**: Sign-extend byte b of value x. If b >= 31, no-op.
  Otherwise, extract bit at position `b*8+7`, extend it to fill
  higher bytes. Shift/mask logic per limb.
- **Reference**: `execution-specs/.../instructions/arithmetic.py:signextend`

---

## Phase 5: EVM Memory Operations

The EVM has its own memory (byte-addressable, expandable). This is separate
from the RISC-V memory used for the stack. We need to model it.

### 5.1 EVM Memory Model
- **File**: `Evm/Memory.lean` (new)
- **Approach**: Define `EvmMemory` as a region of RISC-V memory.
  EVM memory is byte-addressable; our RISC-V memory is word-addressable.
  Use LB/SB/LBU instructions for byte access.
  Define `evmMemIs(base, offset, value)` assertion.
- **Note**: EVM memory auto-extends and is zero-initialized. Model a
  fixed maximum size region.

### 5.2 MLOAD
- **File**: `Evm/Memory.lean`
- **Approach**: Pop offset from stack, load 32 bytes from EVM memory,
  push as 256-bit word. Uses LBU × 32 + shift/OR to assemble.
- **Reference**: `execution-specs/.../instructions/memory.py:mload`

### 5.3 MSTORE
- **File**: `Evm/Memory.lean`
- **Approach**: Pop offset and value, store 32 bytes to EVM memory.
  Uses SB × 32 to disassemble word into bytes.
- **Reference**: `execution-specs/.../instructions/memory.py:mstore`

### 5.4 MSTORE8
- **File**: `Evm/Memory.lean`
- **Approach**: Pop offset and value, store low byte. Single SB.
- **Reference**: `execution-specs/.../instructions/memory.py:mstore8`

---

## Phase 6: Control Flow

EVM bytecode has its own control flow (JUMP/JUMPI). To implement this,
we need an EVM interpreter loop in RISC-V that dispatches opcodes.

### 6.1 Opcode Dispatch Table
- **File**: `Evm/Dispatch.lean` (new)
- **Approach**: Define a RISC-V subroutine that reads the current EVM
  opcode from the EVM code array, then branches to the appropriate
  handler. Use a jump table or cascading BEQ comparisons.
- **Note**: This is the core of the EVM interpreter loop.

### 6.2 STOP
- **File**: `Evm/ControlFlow.lean` (new)
- **Approach**: Set a "halted" flag, break out of the dispatch loop.
  Maps to ECALL/HALT in our RISC-V model.
- **Reference**: `execution-specs/.../instructions/control_flow.py:stop`

### 6.3 JUMP and JUMPI
- **File**: `Evm/ControlFlow.lean`
- **Approach**: JUMP pops destination, validates it's a JUMPDEST, sets
  EVM PC. JUMPI additionally pops a condition. These modify the EVM PC
  (stored in a register or memory location), not the RISC-V PC directly.
- **Reference**: `execution-specs/.../instructions/control_flow.py:jump`, `:jumpi`

### 6.4 EVM Interpreter Main Loop
- **File**: `Evm/Interpreter.lean` (new)
- **Approach**: A RISC-V loop that:
  1. Reads current EVM opcode from code[evm_pc]
  2. Dispatches to the appropriate handler subroutine (JAL)
  3. Increments evm_pc (unless JUMP/JUMPI modified it)
  4. Checks for STOP/RETURN/REVERT
  5. Repeats
- **Spec**: Relates N steps of this loop to N steps of the reference
  EVM interpreter.
- **Note**: This is the most architecturally significant piece. All
  previous opcode implementations become subroutines called from here.

---

## Phase 7: Environment & Block Operations

These opcodes read context data (caller, value, block number, etc.)
that must be provided as input to the RISC-V program.

### 7.1 Environment Context Layout
- **File**: `Evm/Environment.lean` (new)
- **Approach**: Define a memory layout for environment data:
  - msg.caller (20 bytes, padded to 256 bits)
  - msg.value (256 bits)
  - msg.data (calldata, variable length)
  - block.number, block.timestamp, etc.
  Store at a known base address. Define `envIs` assertion.

### 7.2 Simple Environment Opcodes
- **File**: `Evm/Environment.lean`
- **Opcodes**: ADDRESS, CALLER, CALLVALUE, ORIGIN, GASPRICE,
  COINBASE, TIMESTAMP, NUMBER, CHAINID, BASEFEE, SELFBALANCE
- **Approach**: Each is a load from the environment memory region,
  push onto stack. Straightforward LW × 8 + SP decrement.
- **Reference**: `execution-specs/.../instructions/environment.py`,
  `execution-specs/.../instructions/block.py`

### 7.3 CALLDATALOAD, CALLDATASIZE, CALLDATACOPY
- **File**: `Evm/Environment.lean`
- **Approach**: CALLDATALOAD reads 32 bytes from calldata at offset.
  CALLDATASIZE pushes the length. CALLDATACOPY copies to EVM memory.
  These need the calldata region in the environment layout.

---

## Phase 8: Storage and System Operations

These require modeling persistent state and cross-contract calls.

### 8.1 Storage Model
- **File**: `Evm/Storage.lean` (new)
- **Approach**: Storage is a key→value mapping (256-bit → 256-bit).
  Model via syscalls: SLOAD/SSTORE use ECALL to read/write storage
  through the host (similar to how SP1 handles precompiles).
- **Reference**: `execution-specs/.../instructions/storage.py`

### 8.2 SLOAD and SSTORE
- **File**: `Evm/Storage.lean`
- **Approach**: Pop key (and value for SSTORE), issue ECALL to host.
  Host provides/accepts the storage value. Spec relates to abstract
  storage model.

### 8.3 LOG0-LOG4
- **File**: `Evm/Log.lean` (new)
- **Approach**: Pop offset+size (+ topics), read EVM memory region,
  emit via ECALL. LOGn has n topic words.
- **Reference**: `execution-specs/.../instructions/log.py`

### 8.4 CALL, STATICCALL, DELEGATECALL
- **File**: `Evm/System.lean` (new)
- **Approach**: These create child EVM frames. Model as syscalls that
  invoke the interpreter recursively or delegate to host.
  This is the most complex part of the EVM.
- **Reference**: `execution-specs/.../instructions/system.py`
- **Note**: Consider deferring full CALL semantics and using host
  syscalls as a bridge initially.

### 8.5 CREATE, CREATE2
- **File**: `Evm/System.lean`
- **Approach**: Similar to CALL but deploys new code.
  Defer to host syscall initially.

### 8.6 RETURN and REVERT
- **File**: `Evm/ControlFlow.lean`
- **Approach**: Pop offset+size, copy EVM memory to return buffer,
  halt execution. REVERT also reverts state changes.
- **Reference**: `execution-specs/.../instructions/system.py:return_`, `:revert`

---

## Phase 9: KECCAK256 (Hashing)

### 9.1 KECCAK256
- **File**: `Evm/Keccak.lean` (new)
- **Approach**: Pop offset+size, hash EVM memory region.
  KECCAK is too complex to implement in RISC-V inline. Use ECALL
  to delegate to host (like SP1's precompile approach).
  The spec says: given input bytes, the result equals keccak256(input).
- **Reference**: `execution-specs/.../instructions/keccak.py`
- **Note**: For zkEVM, KECCAK is typically a precompile/syscall because
  the hash circuit is handled separately.

---

## Phase 10: Gas Metering

### 10.1 Gas Counter
- **File**: `Evm/Gas.lean` (new)
- **Approach**: Maintain gas counter in a register or memory location.
  Each opcode handler decrements gas by the appropriate cost before
  executing. If gas goes below zero, halt with out-of-gas error.
- **Reference**: `execution-specs/.../vm/gas.py`
- **Note**: Gas costs vary by opcode and sometimes by operand (e.g.,
  EXP gas depends on exponent size). Start with static costs.

### 10.2 Dynamic Gas (Memory Expansion, Storage)
- **File**: `Evm/Gas.lean`
- **Approach**: Memory expansion cost = quadratic in memory size.
  Storage gas depends on cold/warm access (EIP-2929).
  Implement after static gas works.

---

## Phase 11: Integration & Testing

### 11.1 Full Opcode Table
- **File**: `Evm/Opcodes.lean` (new)
- **Approach**: Map opcode byte → RISC-V subroutine address.
  Match the `op_implementation` table in
  `execution-specs/.../instructions/__init__.py`.

### 11.2 Single-Transaction Execution
- **File**: `Evm/Transaction.lean` (new)
- **Approach**: Given a transaction (to, value, data, gas), set up
  the environment, load the contract code, run the interpreter loop,
  collect results.
- **Reference**: `execution-specs/.../vm/interpreter.py:process_message_call`

### 11.3 Block-Level State Transition
- **File**: `Evm/Block.lean` (new)
- **Approach**: Process a sequence of transactions against a state.
  This is the full state transition function.
- **Reference**: `execution-specs/.../fork.py:state_transition`

### 11.4 Conformance Testing
- **Approach**: Run against Ethereum test vectors (ethereum/tests).
  Compare RISC-V execution results to reference Python execution.
  Use `native_decide` or extraction for executable tests.

---

## Priority Order (What to do first)

**Immediate (unblocks most EVM programs):**
1. Phase 1: EQ (complete basic comparisons) — GT done
2. Phase 2.1-2.4: POP, PUSH0, DUP1, SWAP1 (stack manipulation)
3. Phase 2.5: Generalize DUP/SWAP to DUPn/SWAPn

**Short-term (enables simple contracts):**
4. Phase 3.2-3.3: SHL, SHR (used heavily in Solidity)
5. Phase 4.1: MUL (most common arithmetic after ADD/SUB)
6. Phase 5: MLOAD, MSTORE (EVM memory)
7. Phase 6: Interpreter loop + STOP + JUMP/JUMPI

**Medium-term (enables real contracts):**
8. Phase 4.2-4.3: DIV, MOD, SDIV, SMOD
9. Phase 7: Environment opcodes (CALLER, CALLVALUE, etc.)
10. Phase 9: KECCAK256 (via syscall)
11. Phase 8.1-8.2: SLOAD, SSTORE

**Long-term (full EVM):**
12. Phase 4.4-4.5: ADDMOD, MULMOD, EXP
13. Phase 8.3-8.6: LOG, CALL, CREATE, RETURN, REVERT
14. Phase 10: Gas metering
15. Phase 11: Integration and conformance testing

---

## Design Decisions

1. **Stack-in-memory**: EVM stack elements are 256-bit words stored in
   RISC-V memory (8 consecutive 32-bit words). SP register (x12) points
   to top of stack.

2. **Syscall bridge**: Complex operations (KECCAK, SLOAD/SSTORE, CALL)
   use ECALL to delegate to the host, following SP1 conventions.

3. **Per-limb modularity**: Each 256-bit operation is decomposed into
   8 per-limb operations with individual specs, then composed.

4. **Reference spec**: All opcodes must match the semantics in
   `execution-specs/src/ethereum/forks/shanghai/vm/`.

5. **Proof automation**: Use xperm/xsimp for all assertion permutation.
   Use cpsTriple_seq_with_perm for composing multi-limb specs.
