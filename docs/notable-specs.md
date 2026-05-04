# Notable Specs Index

A curated index of notable proven specifications across the EvmAsm codebase, with
permalinks to the exact theorem statements at a pinned commit. Use this page to
find a spec without grepping; refresh the permalinks when files move.

> **Permalinks pinned to commit `7c5da808888e612c2d77be99afae07e3a7f90807` on
> 2026-05-04.** Refresh whenever a major surface lands (e.g. each closure of a
> #61-class umbrella issue) or quarterly, whichever comes first. To refresh,
> re-run `git rev-parse origin/main` and `grep -n` for each declaration name,
> then update the line numbers below.

This index is split by area. Slice 1 landed the page skeleton plus the DivMod
stack-spec surface. Slice 2 (this update) adds the non-DivMod Evm64 opcode
stack specs and the `EvmWord` arithmetic correctness theorems, alongside the
already-populated EL/RLP and Rv64 infrastructure sections.

---

## DivMod stack-spec surface

The path-specific stack-level Hoare triples for `DIV` and `MOD` and their
dispatcher-surface aliases. These are the consumer-facing entry points for
downstream verifiers — when proving a higher-level property, prefer the alias
over the underlying `_word_uni` / `_dispatch_uni` theorem so a future bound
relaxation propagates automatically.

### Unified case-split specs (single theorem per opcode)

The monolithic stack specs that case-split internally on the dispatcher
branch certificate (`DivStackSpecCase` / `ModStackSpecCase`). Prefer these
when proving a higher-level property that does not need to mention the
specific path — the dispatcher branch is hidden behind the certificate.

| Theorem | Defined at | Pre / Post (plain English) |
|---|---|---|
| [`evm_div_stack_spec`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L482) | `Spec/Unified.lean:482` | Pre: stack at `sp` holds two `EvmWord`s `a, b` (top = `b`), the DivMod scratch buffer at `base + ...` is in a recognized branch state given by `branch : DivStackSpecCase base a b`. Post: stack-level `cpsTripleWithin unifiedDivBound` lands at `base + nopOff` with the top of stack equal to `EvmWord.div a b` under `evmWordIs`, all framed memory and registers preserved per `divStackDispatchPost`. |
| [`evm_mod_stack_spec`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L813) | `Spec/Unified.lean:813` | Pre: stack at `sp` holds two `EvmWord`s `a, b` (top = `b`), the DivMod scratch buffer at `base + ...` is in a recognized branch state given by `branch : ModStackSpecCase base a b`. Post: stack-level `cpsTripleWithin unifiedDivBound` lands at `base + nopOff` with the top of stack equal to `EvmWord.mod a b` under `evmWordIs`, all framed memory and registers preserved per `modStackDispatchPost`. |

### Dispatcher aliases

Defined in
[`EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean).

| Alias | Underlying theorem | Meaning |
|---|---|---|
| [`evm_div_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L18) | `evm_div_bzero_stack_spec_within` | DIV with divisor = 0 returns 0 (within bound 13). |
| [`evm_div_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L19) | `evm_div_n1_stack_spec_within_word_uni` | DIV with 1-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L20) | `evm_div_n2_stack_spec_within_word_uni` | DIV with 2-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L21) | `evm_div_n3_stack_spec_within_word_uni` | DIV with 3-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L22) | `evm_div_n4_stack_spec_within_dispatch_uni` | DIV with 4-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_mod_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L24) | `evm_mod_bzero_stack_spec_within` | MOD with divisor = 0 returns 0 (within bound 13). |
| [`evm_mod_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L25) | `evm_mod_n1_stack_spec_within_word_uni` | MOD with 1-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L26) | `evm_mod_n2_stack_spec_within_word_uni` | MOD with 2-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L27) | `evm_mod_n3_stack_spec_within_word_uni` | MOD with 3-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L28) | `evm_mod_n4_stack_spec_within_dispatch_uni` | MOD with 4-limb divisor: stack-level result equals `EvmWord.mod`. |

### Underlying proof-bearing theorems

| Theorem | Defined at |
|---|---|
| `evm_div_bzero_stack_spec_within` | [`Spec/Base.lean:904`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Base.lean#L904) |
| `evm_div_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:210`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L210) |
| `evm_div_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:251`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L251) |
| `evm_div_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:291`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L291) |
| `evm_div_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:330`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L330) |
| `evm_mod_bzero_stack_spec_within` | [`Spec/Base.lean:961`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Base.lean#L961) |
| `evm_mod_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:541`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L541) |
| `evm_mod_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:582`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L582) |
| `evm_mod_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:622`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L622) |
| `evm_mod_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:661`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L661) |

### Dispatcher registries

The `evm_div_stack_spec_within` and `evm_mod_stack_spec_within` registries
([Dispatcher.lean#L65](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L65),
[#L73](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L73))
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
| `evm_mul_stack_spec_within_layout` | [`Multiply/Layout.lean#L86`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Multiply/Layout.lean#L86) | MUL with explicit scratch layout exposed to callers. |
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
| `evm_mstore8_stack_spec_clean_sp_within` | [`MStore8/Spec.lean#L219`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MStore8/Spec.lean#L219) | MSTORE8 variant that exposes the post-stack-pointer cleanup explicitly. |

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
| `mul_correct_limb0` / `_limb1` / `_limb2` / `_limb3` | [`EvmWordArith/MulCorrect.lean#L84`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L84) | Per-output-limb correctness lemmas feeding `mul_correct`. |
| `div_correct`              | [`EvmWordArith/DivCorrect.lean#L15`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L15) | `EvmWord.div a b` matches integer division (with EVM b=0 → 0 convention). |
| `mod_correct`              | [`EvmWordArith/DivCorrect.lean#L26`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L26) | `EvmWord.mod a b` matches integer remainder (with b=0 → 0). |
| `exp_correct`              | [`EvmWordArith/Exp.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Exp.lean#L19) | `EvmWord.exp` matches `base ^ exponent` mod 2^256. |
| `lt_borrow_chain_correct`  | [`EvmWordArith/Comparison.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L19) | borrow-chain LT matches `EvmWord` unsigned `<`. |
| `slt_result_correct`       | [`EvmWordArith/Comparison.lean#L111`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L111) | sign-aware borrow-chain matches signed `<`. |
| `eq_xor_or_reduce_correct` | [`EvmWordArith/Eq.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Eq.lean#L19) | xor-then-or-reduce equals `BEq` on `EvmWord`. |
| `iszero_or_reduce_correct` | [`EvmWordArith/IsZero.lean#L19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/IsZero.lean#L19) | or-reduce of all four limbs equals `iszero`. |
| `byte_correct`             | [`EvmWordArith/ByteOps.lean#L133`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L133) | per-byte select matches the EVM `BYTE` opcode semantics. |
| `byte_extract_correct`     | [`EvmWordArith/ByteOps.lean#L68`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L68) | Selecting byte index `i < 32` from `x` returns the spec-level byte. |

> _DivMod internal correctness._ The intermediate `div_correct_n{1,2,3,4}_no_shift`,
> `div_correct_normalized` / `mod_correct_normalized`, and `n4_max_*` /
> `mulsub_*_correct` lemmas in
> [`DivAccumulate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivAccumulate.lean),
> [`DivN4DoubleAddback.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivN4DoubleAddback.lean),
> [`DivN4Overestimate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivN4Overestimate.lean),
> and [`DivRemainderBound.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivRemainderBound.lean)
> are not indexed individually — they are private to the DivMod proof tree
> and consumers should use `div_correct` / `mod_correct` instead.

## EL / RLP

Pure (no RISC-V dependency) RLP encoder, decoder, and round-trip lemmas.
These are the executable-spec direction: `encode` is the canonical RLP
encoder, `decode` enforces canonical decoding, and `Properties.lean`
discharges round-trip facts via `native_decide` for byte-string lengths
covered so far.

### Encoder ([`EvmAsm/EL/RLP/Basic.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean))

| Declaration | Defined at | Meaning |
|---|---|---|
| `Nat.toBytesBE` | [`Basic.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L46) | Big-endian byte representation of a `Nat`. |
| `Nat.fromBytesBE` | [`Basic.lean:53`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L53) | Inverse of `toBytesBE` on lists of bytes. |
| `encodeBytes` | [`Basic.lean:60`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L60) | Canonical RLP encoding of a single byte string. |
| `encode` | [`Basic.lean:87`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L87) | Canonical RLP encoding of an `RLPItem` (string or list). |
| `encodeBytes_short_of_length_ne_one` | [`Basic.lean:74`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Basic.lean#L74) | Single-byte fast path doesn't apply when length ≠ 1. |

### Decoder ([`EvmAsm/EL/RLP/Decode.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean))

| Declaration | Defined at | Meaning |
|---|---|---|
| `takeBytes` | [`Decode.lean:14`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L14) | Splits a byte list at index `n`, returning `none` if too short. |
| `readLength` | [`Decode.lean:20`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L20) | Reads a big-endian `n`-byte length prefix, enforcing canonical form. |
| `decodeAux` | [`Decode.lean:36`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L36) | Fuel-driven canonical RLP decoder for a single item. |
| `decode` | [`Decode.lean:97`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Decode.lean#L97) | Top-level canonical RLP decode (calls `decodeAux` with `bs.length` fuel). |

### Round-trip and length lemmas ([`EvmAsm/EL/RLP/Properties.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean))

| Theorem | Defined at | Meaning |
|---|---|---|
| `encode_nonempty` | [`Properties.lean:1841`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1841) | `encode` always produces a non-empty byte list. |
| `decode_encode_bytes_empty` | [`Properties.lean:1865`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1865) | `decode (encodeBytes [])` returns the empty string. |
| `decode_encode_bytes_single_small` | [`Properties.lean:1858`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1858) | Round trip for one byte `< 0x80` (single-byte fast path). |
| `decode_encode_bytes_single_large` | [`Properties.lean:1874`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/EL/RLP/Properties.lean#L1874) | Round trip for one byte `≥ 0x80` (uses 0x81 prefix). |

`Properties.lean` also contains a long ladder of per-length
`encodeBytes_<n>tuple` and `decodeAux_<n>_byte_string` lemmas
(`native_decide`-backed) covering byte-string lengths 0..~75 used by
downstream RLP proofs.


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

Generic RISC-V instruction specs and the LP64-aligned calling convention
that EVM opcode handlers and EL routines call into.

### Byte / halfword / word memory specs

Memory-access specs at byte (8-bit), halfword (16-bit), and word (32-bit)
granularity, used by the byte-addressed EVM memory model and the RLP
byte writers. All triples are CPS-style and step-bounded.

| Theorem | Defined at | Meaning |
|---|---|---|
| `byteOffset_lt_8` | [`ByteOps.lean:18`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L18) | The byte index inside a dword is always `< 8`. |
| `alignToDword_byteOffset_zero` | [`ByteOps.lean:24`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L24) | `byteOffset (alignToDword addr) = 0`. |
| `alignToDword_idempotent` | [`ByteOps.lean:30`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L30) | `alignToDword` is idempotent. |
| `alignToDword_add_byteOffset` | [`ByteOps.lean:36`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L36) | `alignToDword addr + byteOffset addr = addr`. |
| `generic_lbu_spec_within` | [`ByteOps.lean:96`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L96) | LBU loads one byte zero-extended; the dword at `alignToDword addr` is unchanged. |
| `generic_lb_spec_within` | [`ByteOps.lean:141`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L141) | LB loads one byte sign-extended. |
| `generic_sb_spec_within` | [`ByteOps.lean:185`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/ByteOps.lean#L185) | SB stores one byte; only the targeted byte slot of the underlying dword is modified. |
| `generic_lhu_spec_within` | [`HalfwordOps.lean:62`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/HalfwordOps.lean#L62) | LHU loads a 16-bit halfword zero-extended. |
| `generic_lh_spec_within` | [`HalfwordOps.lean:106`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/HalfwordOps.lean#L106) | LH loads a 16-bit halfword sign-extended. |
| `generic_sh_spec_within` | [`HalfwordOps.lean:150`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/HalfwordOps.lean#L150) | SH stores a 16-bit halfword. |
| `generic_lwu_spec_within` | [`WordOps.lean:47`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/WordOps.lean#L47) | LWU loads a 32-bit word zero-extended. |
| `generic_lw_spec_within` | [`WordOps.lean:91`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/WordOps.lean#L91) | LW loads a 32-bit word sign-extended. |
| `generic_sw_spec_within` | [`WordOps.lean:135`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/WordOps.lean#L135) | SW stores a 32-bit word. |

### `runBlock` registry highlights ([`EvmAsm/Rv64/SyscallSpecs.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/SyscallSpecs.lean))

The `@[spec_gen_rv64]` registry registers per-instruction specs that
`runBlock` consumes during auto-mode block elaboration. A representative
sample of the LD/SD entry points (the rest follow the same pattern;
the file lists ~50 ALU, branch, and memory specs):

| Theorem | Defined at | Meaning |
|---|---|---|
| `ld_spec_gen_within` | [`SyscallSpecs.lean:28`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/SyscallSpecs.lean#L28) | LD loads a 64-bit doubleword from `[rs1+offset]`. |
| `sd_spec_gen_within` | [`SyscallSpecs.lean:35`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/SyscallSpecs.lean#L35) | SD stores a 64-bit doubleword to `[rs1+offset]`. |
| `sd_spec_gen_own_within` | [`SyscallSpecs.lean:41`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Rv64/SyscallSpecs.lean#L41) | SD-own variant for `rs1 = rs2`. |

### Calling convention ([`EvmAsm/Evm64/CallingConvention.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean))

LP64-aligned register roles (`x1` ra, `x2` sp, `x5–x7` t0–t2, `x10–x11`
a0–a1, `x12` a2/EVM-sp). Reusable program snippets and their proved
specs.

| Snippet / Theorem | Defined at | Meaning |
|---|---|---|
| `cc_ret` | [`CallingConvention.lean:42`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L42) | Return: `JALR x0 x1 0`. |
| `cc_prologue` | [`CallingConvention.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L46) | Non-leaf prologue: allocate 16-byte frame, save `ra`. |
| `cc_epilogue` | [`CallingConvention.lean:51`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L51) | Non-leaf epilogue: restore `ra`, deallocate, return. |
| `callNear_spec_within` | [`CallingConvention.lean:65`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L65) | `JAL x1 offset` jumps to `base + offset` and saves the return address in `x1`. |
| `callFar_spec_within` | [`CallingConvention.lean:75`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L75) | `JALR x1 target 0` indirect call: jumps to `target` and saves the return address. |
| `ret_spec_within` | [`CallingConvention.lean:84`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L84) | `JALR x0 x1 0` returns to the caller (jumps to `ra`). |
| `ret_spec_within'` | [`CallingConvention.lean:92`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L92) | Variant of `ret_spec_within` with a different post-shape. |
| `cc_prologue_spec_within` | [`CallingConvention.lean:109`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L109) | Block spec for the 2-instruction prologue: `sp` decremented by 16, `ra` saved at `sp+8`. |
| `cc_epilogue_spec_within` | [`CallingConvention.lean:129`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/CallingConvention.lean#L129) | Block spec for the 3-instruction epilogue: `ra` restored, `sp` incremented by 16, jumps to saved `ra`. |


## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly,
  whichever comes first.

### Refresh procedure (5 steps)

1. **Survey the spec surface.** Grep for the canonical entry-point names so
   nothing has been added or renamed since the last refresh:

   ```bash
   rg -n '@\[stack_spec_' EvmAsm/
   rg -n 'theorem evm_[a-z_]*_stack_spec' EvmAsm/
   rg -n 'theorem EvmWord\.[a-z_]*_correct' EvmAsm/
   ```

   Add an entry to the appropriate section for any name not already listed;
   delete entries whose underlying theorem is gone.

2. **Capture `file:line` for every entry.** For each theorem name, locate
   its current declaration site:

   ```bash
   grep -n '<theorem-name>' EvmAsm/<path>.lean
   ```

   Record the `path:line` pair — both the alias line and (if separate) the
   underlying proof-bearing theorem line.

3. **Mint commit-pinned permalinks.** Capture the current upstream sha and
   build URLs against it:

   ```bash
   SHA=$(git rev-parse origin/main)
   gh browse <path>:<line> --commit "$SHA" --no-browser
   # or directly:
   echo "https://github.com/Verified-zkEVM/evm-asm/blob/$SHA/<path>#L<line>"
   ```

   Replace each existing permalink in the table cells with the freshly
   minted one.

4. **Update the top-of-page pin.** Replace the `Permalinks pinned to commit
   <sha> on <date>` blockquote near the top with the new sha and today's
   date.

5. **Verify with `lake build`.** Run `lake build` from the repo root to
   confirm every referenced declaration still elaborates under the pinned
   sha. Any rename or relocation discovered here loops back to step 1.
