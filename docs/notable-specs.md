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

_TODO (slice 3): index RLP encode/decode round-trip and per-phase decode specs._

## Rv64 infrastructure

_TODO (slice 3): index `ByteOps` LBU/SB specs, calling-convention helpers
(`callNear_spec`, `cc_prologue_spec`, `nonleaf_function_spec`, etc.)._

## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Refresh procedure: `git rev-parse origin/main` for the new sha, then for each
  entry re-confirm the line number with `grep -n '<theorem name>'` against the
  named file. Replace the pinned sha and line numbers and the date in the
  top-of-page note.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly.
