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
stack specs and the `EvmWord` arithmetic correctness theorems. Subsequent
slices populate the EL/RLP and Rv64 infrastructure sections.

---

## DivMod stack-spec surface

The path-specific stack-level Hoare triples for `DIV` and `MOD` and their
dispatcher-surface aliases. These are the consumer-facing entry points for
downstream verifiers — when proving a higher-level property, prefer the alias
over the underlying `_word_uni` / `_dispatch_uni` theorem so a future bound
relaxation propagates automatically.

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

Stack-level Hoare triples for the remaining Evm64 opcodes. Each `_within`
theorem has the standard shape: the `evmStackIs` precondition holds at `sp`
with two (or appropriate-arity) input words on top, and after running the
opcode body the postcondition asserts the stack now holds the result word at
the same or adjusted slot, with all framed state preserved.

| Theorem | Defined at | Meaning |
|---|---|---|
| `evm_add_stack_spec_within` | [`Add/Spec.lean:73`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Add/Spec.lean#L73) | ADD: top two words `a`, `b` → `a + b` (mod 2^256). |
| `evm_sub_stack_spec_within` | [`Sub/Spec.lean:73`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Sub/Spec.lean#L73) | SUB: top two words `a`, `b` → `a - b` (mod 2^256). |
| `evm_mul_stack_spec_within` | [`Multiply/Spec.lean:90`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Multiply/Spec.lean#L90) | MUL: top two words `a`, `b` → `a * b` (mod 2^256). |
| `evm_mul_stack_spec_within_layout` | [`Multiply/Layout.lean:86`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Multiply/Layout.lean#L86) | MUL with explicit scratch layout exposed to callers. |
| `evm_lt_stack_spec_within` | [`Lt/Spec.lean:78`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Lt/Spec.lean#L78) | LT: top two words `a`, `b` → `1` if unsigned `a < b` else `0`. |
| `evm_gt_stack_spec_within` | [`Gt/Spec.lean:81`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Gt/Spec.lean#L81) | GT: top two words `a`, `b` → `1` if unsigned `a > b` else `0`. |
| `evm_slt_stack_spec_within` | [`Slt/Spec.lean:117`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Slt/Spec.lean#L117) | SLT: signed less-than on top two words → `1` or `0`. |
| `evm_sgt_stack_spec_within` | [`Sgt/Spec.lean:119`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Sgt/Spec.lean#L119) | SGT: signed greater-than on top two words → `1` or `0`. |
| `evm_eq_stack_spec_within` | [`Eq/Spec.lean:78`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Eq/Spec.lean#L78) | EQ: top two words `a`, `b` → `1` if `a == b` else `0`. |
| `evm_iszero_stack_spec_within` | [`IsZero/Spec.lean:65`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/IsZero/Spec.lean#L65) | ISZERO: top word `a` → `1` if `a == 0` else `0`. |
| `evm_and_stack_spec_within` | [`And/Spec.lean:53`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/And/Spec.lean#L53) | AND: bitwise AND of top two words. |
| `evm_or_stack_spec_within` | [`Or/Spec.lean:41`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Or/Spec.lean#L41) | OR: bitwise OR of top two words. |
| `evm_xor_stack_spec_within` | [`Xor/Spec.lean:41`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Xor/Spec.lean#L41) | XOR: bitwise XOR of top two words. |
| `evm_not_stack_spec_within` | [`Not/Spec.lean:62`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Not/Spec.lean#L62) | NOT: bitwise complement of top word. |
| `evm_byte_stack_spec_within` | [`Byte/Spec.lean:848`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Byte/Spec.lean#L848) | BYTE: extract `idx`-th byte of `x` (zero if `idx >= 32`). |
| `evm_signextend_stack_spec_within` | [`SignExtend/Spec.lean:64`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/SignExtend/Spec.lean#L64) | SIGNEXTEND: sign-extend `x` from byte position `b`. |
| `evm_shl_stack_spec_within` | [`Shift/ShlSemantic.lean:131`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/ShlSemantic.lean#L131) | SHL: shift left by top word amount (0 if shift ≥ 256). |
| `evm_shr_stack_spec_within` | [`Shift/Semantic.lean:131`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/Semantic.lean#L131) | SHR: logical shift right by top word amount. |
| `evm_sar_stack_spec_within` | [`Shift/SarSemantic.lean:143`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Shift/SarSemantic.lean#L143) | SAR: arithmetic shift right with sign fill. |
| `evm_pop_stack_spec_within` | [`Pop/Spec.lean:30`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Pop/Spec.lean#L30) | POP: drop top word; stack pointer adjusts. |
| `evm_dup_stack_spec_within` | [`Dup/Spec.lean:143`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Dup/Spec.lean#L143) | DUP-n: duplicate the n-th stack word onto the top. |
| `evm_swap_stack_spec_within` | [`Swap/Spec.lean:149`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Swap/Spec.lean#L149) | SWAP-n: swap top word with the n-th-below word. |
| `evm_push0_stack_spec_within` | [`Push0/Spec.lean:40`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push0/Spec.lean#L40) | PUSH0: push the zero word onto the stack. |
| `evm_push_zero_slot_stack_spec_within` | [`Push/Spec.lean:171`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push/Spec.lean#L171) | PUSH-n (zero-slot variant): push zero into the freshly opened top slot. |
| `evm_push_zero_slot_full_stack_spec_within` | [`Push/Spec.lean:199`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/Push/Spec.lean#L199) | PUSH-n (full-slot composition): combine zero-slot with the constant payload. |
| `evm_msize_stack_spec_within` | [`MSize/Spec.lean:138`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MSize/Spec.lean#L138) | MSIZE: push current memory size in bytes. |
| `evm_mstore8_stack_spec_within` | [`MStore8/Spec.lean:139`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MStore8/Spec.lean#L139) | MSTORE8: write low byte of `value` at address `addr`. |
| `evm_mstore8_stack_spec_clean_sp_within` | [`MStore8/Spec.lean:219`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/MStore8/Spec.lean#L219) | MSTORE8 variant that exposes the post-stack-pointer cleanup explicitly. |

> _Not yet indexed:_ MLOAD/MSTORE bulk specs (#102, in flight under
> `evm-asm-yrz5` MSTORE-window refactor), and the calldata opcodes (#104).
> Add their stack specs here when they land.

---

## EvmWord arithmetic correctness

Pure-Lean theorems relating the limb-level decomposition of a 256-bit
`EvmWord` to its semantic operation. These are proof tools used by the
opcode-level Hoare triples; downstream consumers usually want the opcode
stack spec, not these.

Defined under
[`EvmAsm/Evm64/EvmWordArith/`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/).

| Theorem | Defined at | Meaning |
|---|---|---|
| `add_carry_chain_correct` | [`Arithmetic.lean:61`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L61) | The 4-limb carry-chain addition equals `EvmWord.add`. |
| `sub_borrow_chain_correct` | [`Arithmetic.lean:241`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Arithmetic.lean#L241) | The 4-limb borrow-chain subtraction equals `EvmWord.sub`. |
| `lt_borrow_chain_correct` | [`Comparison.lean:19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L19) | Final borrow flag from the 4-limb subtractor equals unsigned `<`. |
| `slt_result_correct` | [`Comparison.lean:111`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Comparison.lean#L111) | The signed-LT recipe on top-limb sign bits + unsigned LT equals signed `<`. |
| `eq_xor_or_reduce_correct` | [`Eq.lean:19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Eq.lean#L19) | `(a XOR b) reduced via OR == 0` iff `a == b`. |
| `iszero_or_reduce_correct` | [`IsZero.lean:19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/IsZero.lean#L19) | OR-reduction of the four limbs is zero iff the word is zero. |
| `byte_extract_correct` | [`ByteOps.lean:68`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L68) | Selecting byte index `i < 32` from `x` returns the spec-level byte. |
| `byte_correct` | [`ByteOps.lean:133`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/ByteOps.lean#L133) | The full BYTE-opcode definition equals `EvmWord.byte`. |
| `mul_correct` | [`MulCorrect.lean:492`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L492) | The 4×4 limb-product reduction equals `EvmWord.mul` (mod 2^256). |
| `mul_correct_limb0` / `_limb1` / `_limb2` / `_limb3` | [`MulCorrect.lean:84`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/MulCorrect.lean#L84) | Per-output-limb correctness lemmas feeding `mul_correct`. |
| `div_correct` | [`DivCorrect.lean:15`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L15) | The DivMod algorithm result equals `EvmWord.div` for any `a`, `b`. |
| `mod_correct` | [`DivCorrect.lean:26`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivCorrect.lean#L26) | The DivMod algorithm remainder equals `EvmWord.mod` for any `a`, `b`. |
| `exp_correct` | [`Exp.lean:19`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/Exp.lean#L19) | The square-and-multiply EXP algorithm equals `EvmWord.exp`. |

> _DivMod internal correctness._ The intermediate `div_correct_n{1,2,3,4}_no_shift`,
> `div_correct_normalized` / `mod_correct_normalized`, and `n4_max_*` /
> `mulsub_*_correct` lemmas in
> [`DivAccumulate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivAccumulate.lean),
> [`DivN4DoubleAddback.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivN4DoubleAddback.lean),
> [`DivN4Overestimate.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivN4Overestimate.lean),
> and [`DivRemainderBound.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/7c5da808888e612c2d77be99afae07e3a7f90807/EvmAsm/Evm64/EvmWordArith/DivRemainderBound.lean)
> are not indexed individually — they are private to the DivMod proof tree
> and consumers should use `div_correct` / `mod_correct` instead.

---

## EL / RLP

_TODO (slice 3 — `evm-asm-u68x`): index RLP encode/decode round-trip and
per-phase decode specs._

## Rv64 infrastructure

_TODO (slice 3 — `evm-asm-u68x`): index `ByteOps` LBU/SB specs and
calling-convention helpers (`callNear_spec`, `cc_prologue_spec`,
`nonleaf_function_spec`, etc.)._

## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Refresh procedure: `git rev-parse origin/main` for the new sha, then for each
  entry re-confirm the line number with `grep -n '<theorem name>'` against the
  named file. Replace the pinned sha and line numbers and the date in the
  top-of-page note.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly.
