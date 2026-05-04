# Notable Specs Index

A curated index of notable proven specifications across the EvmAsm codebase, with
permalinks to the exact theorem statements at a pinned commit. Use this page to
find a spec without grepping; refresh the permalinks when files move.

> **Permalinks pinned to commit `7c5da808888e612c2d77be99afae07e3a7f90807` on
> 2026-05-04** (slice 2 add — links in the DivMod section still target the
> 2026-05-01 sha; both shas are immutable so the links remain valid).
> Refresh whenever a major surface lands (e.g. each closure of a #61-class
> umbrella issue) or quarterly, whichever comes first. To refresh, re-run
> `git rev-parse origin/main` and `grep -n` for each declaration name, then
> update the line numbers below.

This index is split by area. Slice 1 (this PR) lands the page skeleton plus the
DivMod stack-spec surface. Subsequent slices will populate the remaining
sections.

---

## DivMod stack-spec surface

The path-specific stack-level Hoare triples for `DIV` and `MOD` and their
dispatcher-surface aliases. These are the consumer-facing entry points for
downstream verifiers — when proving a higher-level property, prefer the alias
over the underlying `_word_uni` / `_dispatch_uni` theorem so a future bound
relaxation propagates automatically.

### Dispatcher aliases

Defined in
[`EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean).

| Alias | Underlying theorem | Meaning |
|---|---|---|
| [`evm_div_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L18) | `evm_div_bzero_stack_spec_within` | DIV with divisor = 0 returns 0 (within bound 13). |
| [`evm_div_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L19) | `evm_div_n1_stack_spec_within_word_uni` | DIV with 1-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L20) | `evm_div_n2_stack_spec_within_word_uni` | DIV with 2-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L21) | `evm_div_n3_stack_spec_within_word_uni` | DIV with 3-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L22) | `evm_div_n4_stack_spec_within_dispatch_uni` | DIV with 4-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_mod_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L24) | `evm_mod_bzero_stack_spec_within` | MOD with divisor = 0 returns 0 (within bound 13). |
| [`evm_mod_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L25) | `evm_mod_n1_stack_spec_within_word_uni` | MOD with 1-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L26) | `evm_mod_n2_stack_spec_within_word_uni` | MOD with 2-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L27) | `evm_mod_n3_stack_spec_within_word_uni` | MOD with 3-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L28) | `evm_mod_n4_stack_spec_within_dispatch_uni` | MOD with 4-limb divisor: stack-level result equals `EvmWord.mod`. |

### Underlying proof-bearing theorems

| Theorem | Defined at |
|---|---|
| `evm_div_bzero_stack_spec_within` | [`Spec/Base.lean:904`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Base.lean#L904) |
| `evm_div_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L46) |
| `evm_div_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:87`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L87) |
| `evm_div_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:127`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L127) |
| `evm_div_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:166`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L166) |
| `evm_mod_bzero_stack_spec_within` | [`Spec/Base.lean:961`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Base.lean#L961) |
| `evm_mod_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:195`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L195) |
| `evm_mod_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:236`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L236) |
| `evm_mod_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:276`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L276) |
| `evm_mod_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:315`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L315) |

### Dispatcher registries

The `evm_div_stack_spec_within` and `evm_mod_stack_spec_within` registries
([Dispatcher.lean#L65](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L65),
[#L73](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L73))
list every branch and the per-branch step bound. All non-`bzero` branches are
lifted to a single `unifiedDivBound`.

---

## Other Evm64 opcode stack specs

The following are the dispatcher-surface stack-level Hoare triples for the
remaining (non-`DivMod`) Evm64 opcodes. Each names a concrete program,
states the stack pre/post over `evmStackIs`, and bounds the step count.

### Arithmetic and bitwise

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_add_stack_spec_within` | [`Add/Spec.lean#L73`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Add/Spec.lean#L73) | ADD: top two stack words → low-256 sum. |
| `evm_sub_stack_spec_within` | [`Sub/Spec.lean#L73`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Sub/Spec.lean#L73) | SUB: a − b mod 2^256. |
| `evm_mul_stack_spec_within` | [`Multiply/Spec.lean#L90`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Multiply/Spec.lean#L90) | MUL: low-256 product. |
| `evm_and_stack_spec_within` | [`And/Spec.lean#L53`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/And/Spec.lean#L53) | AND: bitwise conjunction. |
| `evm_or_stack_spec_within`  | [`Or/Spec.lean#L41`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Or/Spec.lean#L41) | OR: bitwise disjunction. |
| `evm_xor_stack_spec_within` | [`Xor/Spec.lean#L41`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Xor/Spec.lean#L41) | XOR: bitwise xor. |
| `evm_not_stack_spec_within` | [`Not/Spec.lean#L62`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Not/Spec.lean#L62) | NOT: bitwise complement. |
| `evm_shl_stack_spec_within` | [`Shift/ShlSemantic.lean#L131`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/ShlSemantic.lean#L131) | SHL: shift-left, EVM saturation. |
| `evm_shr_stack_spec_within` | [`Shift/Semantic.lean#L131`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/Semantic.lean#L131) | SHR: logical shift-right. |
| `evm_sar_stack_spec_within` | [`Shift/SarSemantic.lean#L143`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/SarSemantic.lean#L143) | SAR: arithmetic shift-right (sign-fill). |
| `evm_byte_stack_spec_within` | [`Byte/Spec.lean#L848`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Byte/Spec.lean#L848) | BYTE: extract i-th byte (big-endian). |
| `evm_signextend_stack_spec_within` | [`SignExtend/Spec.lean#L64`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/SignExtend/Spec.lean#L64) | SIGNEXTEND: sign-extend low (k+1) bytes. |

### Comparators

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_lt_stack_spec_within`     | [`Lt/Spec.lean#L78`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Lt/Spec.lean#L78) | LT: unsigned less-than → 0/1. |
| `evm_gt_stack_spec_within`     | [`Gt/Spec.lean#L81`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Gt/Spec.lean#L81) | GT: unsigned greater-than → 0/1. |
| `evm_slt_stack_spec_within`    | [`Slt/Spec.lean#L117`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Slt/Spec.lean#L117) | SLT: signed less-than. |
| `evm_sgt_stack_spec_within`    | [`Sgt/Spec.lean#L119`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Sgt/Spec.lean#L119) | SGT: signed greater-than. |
| `evm_eq_stack_spec_within`     | [`Eq/Spec.lean#L78`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Eq/Spec.lean#L78) | EQ: equality → 0/1. |
| `evm_iszero_stack_spec_within` | [`IsZero/Spec.lean#L65`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/IsZero/Spec.lean#L65) | ISZERO: 1 iff top-of-stack is 0. |

### Stack/memory shuffling and constants

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_pop_stack_spec_within`  | [`Pop/Spec.lean#L30`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Pop/Spec.lean#L30) | POP: drop top of stack. |
| `evm_dup_stack_spec_within`  | [`Dup/Spec.lean#L143`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Dup/Spec.lean#L143) | DUP1..DUP16: duplicate the n-th stack slot. |
| `evm_swap_stack_spec_within` | [`Swap/Spec.lean#L149`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Swap/Spec.lean#L149) | SWAP1..SWAP16: swap top with the (n+1)-th. |
| `evm_push0_stack_spec_within` | [`Push0/Spec.lean#L40`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push0/Spec.lean#L40) | PUSH0: push the zero word. |
| `evm_push_zero_slot_stack_spec_within` | [`Push/Spec.lean#L171`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push/Spec.lean#L171) | PUSH1..32 to a zero stack slot (per-limb). |
| `evm_push_zero_slot_full_stack_spec_within` | [`Push/Spec.lean#L199`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push/Spec.lean#L199) | PUSH1..32 (full word, four-limb composition). |
| `evm_msize_stack_spec_within` | [`MSize/Spec.lean#L138`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MSize/Spec.lean#L138) | MSIZE: push current memory size in bytes. |
| `evm_mstore8_stack_spec_within` | [`MStore8/Spec.lean#L139`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MStore8/Spec.lean#L139) | MSTORE8: write the low byte at memory[offset]. |

> MLOAD / MSTORE stack specs are tracked under #102 / #99 and not yet
> landed; this section will be extended as those PRs merge.

## EvmWord arithmetic correctness

The pure-Lean correctness theorems that say each `EvmWord.<op>` matches the
expected mathematical semantics — these are what `evm_*_stack_spec_within`
ultimately reduces to in the post-condition.

| Theorem | Defined at | Meaning |
|---|---|---|
| `add_carry_chain_correct`  | [`EvmWordArith/Arithmetic.lean#L61`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L61)  | 4-limb carry-chain adder = `EvmWord` addition mod 2^256. |
| `sub_borrow_chain_correct` | [`EvmWordArith/Arithmetic.lean#L241`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L241) | 4-limb borrow-chain subtractor = `EvmWord` subtraction. |
| `mul_correct`              | [`EvmWordArith/MulCorrect.lean#L492`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L492) | 4×4 limb mul (low 256 bits) = `EvmWord` multiplication. |
| `div_correct`              | [`EvmWordArith/DivCorrect.lean#L15`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L15) | `EvmWord.div a b` matches integer division (with EVM b=0 → 0 convention). |
| `mod_correct`              | [`EvmWordArith/DivCorrect.lean#L26`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L26) | `EvmWord.mod a b` matches integer remainder (with b=0 → 0). |
| `exp_correct`              | [`EvmWordArith/Exp.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Exp.lean#L19) | `EvmWord.exp` matches `base ^ exponent` mod 2^256. |
| `lt_borrow_chain_correct`  | [`EvmWordArith/Comparison.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L19) | borrow-chain LT matches `EvmWord` unsigned `<`. |
| `slt_result_correct`       | [`EvmWordArith/Comparison.lean#L111`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L111) | sign-aware borrow-chain matches signed `<`. |
| `eq_xor_or_reduce_correct` | [`EvmWordArith/Eq.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Eq.lean#L19) | xor-then-or-reduce equals `BEq` on `EvmWord`. |
| `iszero_or_reduce_correct` | [`EvmWordArith/IsZero.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/IsZero.lean#L19) | or-reduce of all four limbs equals `iszero`. |
| `byte_correct`             | [`EvmWordArith/ByteOps.lean#L133`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L133) | per-byte select matches the EVM `BYTE` opcode semantics. |

## EL / RLP

The pure RLP encode/decode model lives under `EvmAsm/EL/RLP/`. `Basic.lean`
defines `encode`, `Decode.lean` defines `decode`, `Properties.lean` collects
round-trip and per-prefix-class equational lemmas, and `PrefixDecode.lean`
exposes the `classifyPrefix`-driven view used to bridge to the
RISC-V-decoder direction. `ProgramSpec.lean` houses the in-Rv64 Hoare
triples for the prefix-classification routines.

### Pure model (executable spec)

| Declaration | Defined at | Meaning |
|---|---|---|
| `encode` | [`EL/RLP/Basic.lean#L87`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L87) | RLP encoder for `RLPItem` (byte-string or list). |
| `encodeBytes` | [`EL/RLP/Basic.lean#L60`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L60) | RLP encoder for raw byte strings (the `.bytes` arm of `encode`). |
| `decode` | [`EL/RLP/Decode.lean#L97`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L97) | Top-level fuel-bounded decoder; returns `(item, leftover)`. |
| `decodeAux` | [`EL/RLP/Decode.lean#L36`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L36) | One step of decode; dispatches on prefix byte. |

### Round-trip and per-class properties (`Properties.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `encode_nonempty` | [`EL/RLP/Properties.lean#L1841`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1841) | `(encode item).length > 0`. |
| `encodeBytes_nonempty` | [`EL/RLP/Properties.lean#L1834`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1834) | `(encodeBytes data).length > 0`. |
| `decode_encode_bytes_empty` | [`EL/RLP/Properties.lean#L1865`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1865) | Round-trip on the empty byte string. |
| `decode_encode_bytes_single_small` | [`EL/RLP/Properties.lean#L1858`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1858) | Round-trip on a single byte `< 0x80` (encoded as itself). |
| `decode_encode_bytes_single_large` | [`EL/RLP/Properties.lean#L1874`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1874) | Round-trip on a single byte `≥ 0x80` (encoded as `0x81 b`). |
| `decodeAux_zero_fuel` | [`EL/RLP/Properties.lean#L52`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L52) | `decodeAux 0 _ = none` (fuel exhausted). |
| `decodeAux_nil` | [`EL/RLP/Properties.lean#L57`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L57) | `decodeAux _ [] = none`. |
| `encodeBytes_short_of_length_ne_one` | [`EL/RLP/Basic.lean#L74`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L74) | When `data.length ≠ 1`, `encodeBytes data = 0x80+len :: data` (short-form). |

> The bulk of `Properties.lean` is a long sequence of length-indexed
> `decodeAux_<n>_byte_string` and `encodeBytes_<n>uple` equational lemmas
> (n = 0..47). They are used by the Rv64 decoder proofs but are too
> mechanical to enumerate here; see the file for the full list.

### `classifyPrefix` view (`PrefixDecode.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `decode_cons_eq_classifyPrefix_match` | [`EL/RLP/PrefixDecode.lean#L136`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L136) | `decode (pfx :: rest)` matches the case-split implied by `classifyPrefix pfx`. |
| `decodeAux_cons_eq_classifyPrefix_match` | [`EL/RLP/PrefixDecode.lean#L93`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L93) | Same shape, expressed against `decodeAux fuel`. |
| `decodeAux_cons_singleByte_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L13`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L13) | Single-byte branch of the case split. |
| `decodeAux_cons_shortBytes_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L21`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L21) | Short-string branch (`0x81..0xb7`). |
| `decodeAux_cons_longBytes_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L36`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L36) | Long-string branch (`0xb8..0xbf`). |
| `decodeAux_cons_shortList_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L53`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L53) | Short-list branch (`0xc0..0xf7`). |
| `decodeAux_cons_longList_of_classifyPrefix` | [`EL/RLP/PrefixDecode.lean#L69`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/PrefixDecode.lean#L69) | Long-list branch (`0xf8..0xff`). |

### Rv64 prefix-classifier triples (`ProgramSpec.lean`)

| Theorem | Defined at | Meaning |
|---|---|---|
| `rlp_prefix_classify_singleByte_spec_within` | [`EL/RLP/ProgramSpec.lean#L29`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/ProgramSpec.lean#L29) | Classifier returns `singleByte` when prefix `< 0x80`. |
| `rlp_prefix_classify_singleByte_of_classifyPrefix_spec_within` | [`EL/RLP/ProgramSpec.lean#L180`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/ProgramSpec.lean#L180) | Classifier output matches `classifyPrefix pfx`. |
| `rlp_prefix_short_payload_len_spec_within` | [`EL/RLP/ProgramSpec.lean#L203`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/ProgramSpec.lean#L203) | Decode the payload length of a short-form RLP item. |
| `rlp_prefix_long_header_bytes_spec_within` | [`EL/RLP/ProgramSpec.lean#L404`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/ProgramSpec.lean#L404) | Number of header-byte slots consumed for a long-form RLP item. |

## Rv64 infrastructure

### `ByteOps` (byte-level memory operations)

Defined in
[`EvmAsm/Rv64/ByteOps.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean).

| Theorem | Defined at | Meaning |
|---|---|---|
| `generic_lbu_spec_within` | [`Rv64/ByteOps.lean#L96`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L96) | LBU loads the byte at `v_addr` into `rd`, zero-extended. |
| `generic_lb_spec_within`  | [`Rv64/ByteOps.lean#L141`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L141) | LB loads the byte at `v_addr` into `rd`, sign-extended. |
| `generic_sb_spec_within`  | [`Rv64/ByteOps.lean#L185`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L185) | SB stores the low byte of `v_data` at `v_addr`, leaving other bytes of the dword intact. |
| `alignToDword_byteOffset_zero` | [`Rv64/ByteOps.lean#L24`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L24) | If `byteOffset addr = 0` then `alignToDword addr = addr`. |
| `alignToDword_idempotent` | [`Rv64/ByteOps.lean#L30`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L30) | `alignToDword (alignToDword a) = alignToDword a`. |
| `alignToDword_add_byteOffset` | [`Rv64/ByteOps.lean#L36`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L36) | `alignToDword addr + byteOffset addr = addr`. |
| `extractByte_replaceByte_same` | [`Rv64/ByteOps.lean#L76`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L76) | `extractByte (replaceByte w pos b) pos = b`. |

### LP64 calling convention (`Evm64/CallingConvention.lean`)

The reusable building blocks for non-leaf functions: prologue / epilogue
snippets and the call/return primitive specs. Use these instead of
re-deriving call semantics in opcode handlers — see also `AGENTS.md` →
"Calling Convention (LP64)".

| Declaration | Defined at | Meaning |
|---|---|---|
| `cc_ret` (program) | [`Evm64/CallingConvention.lean#L42`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L42) | `JALR x0 x1 0` — the leaf-return one-liner. |
| `cc_prologue` (program) | [`Evm64/CallingConvention.lean#L46`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L46) | Non-leaf prologue: bump sp by −16, save ra at `sp+8`. |
| `cc_epilogue` (program) | [`Evm64/CallingConvention.lean#L51`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L51) | Non-leaf epilogue: restore ra from `sp+8`, unbump sp, JALR x0 ra. |
| `callNear_spec_within` | [`Evm64/CallingConvention.lean#L65`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L65) | JAL (near call) saves return address into `x1` and jumps. |
| `callFar_spec_within`  | [`Evm64/CallingConvention.lean#L75`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L75) | JALR (far call) saves return address into `x1` and jumps via target reg. |
| `ret_spec_within`  | [`Evm64/CallingConvention.lean#L84`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L84) | `cc_ret` jumps to `x1`. |
| `ret_spec_within'` | [`Evm64/CallingConvention.lean#L92`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L92) | Variant of `ret_spec_within` with a different framing of `x1`. |
| `cc_prologue_spec_within` | [`Evm64/CallingConvention.lean#L109`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L109) | Block spec for `cc_prologue`. |
| `cc_epilogue_spec_within` | [`Evm64/CallingConvention.lean#L129`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L129) | Block spec for `cc_epilogue`. |

> Spec database / `@[spec_gen_rv64]` registry: see
> [`EvmAsm/Rv64/SyscallSpecs.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/SyscallSpecs.lean).
> Each `@[spec_gen_rv64]`-tagged theorem (`ld_spec_gen_within`,
> `sd_spec_gen_within`, `addi_spec_gen_within`, …) is auto-detected by
> instruction constructor and used by the `runBlock` automation.

## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Refresh procedure: `git rev-parse origin/main` for the new sha, then for each
  entry re-confirm the line number with `grep -n '<theorem name>'` against the
  named file. Replace the pinned sha and line numbers and the date in the
  top-of-page note.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly.
