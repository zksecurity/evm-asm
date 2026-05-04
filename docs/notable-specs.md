# Notable Specs Index

A curated index of notable proven specifications across the EvmAsm codebase, with
permalinks to the exact theorem statements at a pinned commit. Use this page to
find a spec without grepping; refresh the permalinks when files move.

> **Permalinks pinned to commit `7c5da808888e612c2d77be99afae07e3a7f90807` on
> 2026-05-04.** Refresh whenever a major surface lands (e.g. each closure of a
> #61-class umbrella issue) or quarterly, whichever comes first. To refresh,
> re-run `git rev-parse origin/main` and `grep -n` for each declaration name,
> then update the line numbers below.

This index is split by area. The DivMod stack-spec surface, EL/RLP, and
Rv64 infrastructure sections are populated; the remaining `## Other Evm64
opcode stack specs` and `## EvmWord arithmetic correctness` sections are
landed by a separate slice (PR #2242).

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

_TODO (slice 2): index `evm_add` / `evm_sub` / `evm_mul` / `evm_shl` / `evm_shr`
/ `evm_sar` / comparator / `evm_push_n` stack specs._

## EvmWord arithmetic correctness

_TODO (slice 2): index `EvmWord.div_correct`, `EvmWord.mod_correct`, etc._

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
- Refresh procedure: `git rev-parse origin/main` for the new sha, then for each
  entry re-confirm the line number with `grep -n '<theorem name>'` against the
  named file. Replace the pinned sha and line numbers and the date in the
  top-of-page note.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly.
