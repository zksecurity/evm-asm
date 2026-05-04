# SDIV / SMOD design note (#90, beads parent `evm-asm-34sg`)

This is the slice-1 design survey for the SDIV and SMOD opcode subtrees. It
chooses the strategy used by subsequent slices (skeleton, `EvmWord.sdiv_correct`
/ `smod_correct`, `evm_sdiv` / `evm_smod` programs and stack specs, dispatcher
wiring). No production Lean code is introduced by this slice.

The corresponding Python execution-spec sources are
`execution-specs/src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py`
functions `sdiv` (lines 145–175) and `smod` (lines 208–235).

## 1. Spec semantics (EvmWord level)

Following the executable spec, both opcodes interpret their two stack
operands as **two's-complement signed 256-bit integers** (`U256.to_signed`):
the value `v ∈ {0, …, 2^256 − 1}` represents `v` if `v < 2^255` and
`v − 2^256` otherwise. The result is reinterpreted by `U256.from_signed`
(equivalently: take `result mod 2^256`).

### SDIV(dividend, divisor)

```
if divisor == 0:                            quotient = 0
elif dividend == −2^255 and divisor == −1:  quotient = −2^255      -- overflow trap
else:                                       quotient = sign(d*v) * (|d| // |v|)
```

The `−2^255 / −1` case is the only signed-integer overflow point and is
short-circuited to return `−2^255` (the dividend) rather than `+2^255`
(which is unrepresentable in signed 256). Truncating-toward-zero division
(`abs/abs` then sign-correction) is what the spec computes; this matches
EVM Yellow Paper §3 and Lean's `Int.tdiv` / `BitVec.sdiv`.

### SMOD(x, y)

```
if y == 0:  remainder = 0
else:       remainder = sign(x) * (|x| % |y|)        -- divisor sign ignored
```

Sign of result follows the dividend (truncating modulo, matches `Int.tmod`
/ `BitVec.smod`).

## 2. Lean spec layer (`EvmAsm/Evm64/EvmWordArith/`)

Two new pure-`BitVec 256` correctness theorems will live alongside the
existing `EvmWord.div` / `EvmWord.mod` machinery:

| Theorem | File | Statement (informal) |
| --- | --- | --- |
| `EvmWord.sdiv` (def) | `EvmWordArith/SDiv.lean` | `BitVec.sdiv` lifted to `EvmWord` with the EVM `divisor=0 → 0` and `−2^255/−1 → −2^255` short-circuits baked in. |
| `EvmWord.sdiv_correct` | `EvmWordArith/SDiv.lean` | `EvmWord.sdiv a b` equals the spec formula stated in terms of `a.toInt`, `b.toInt`, `Int.tdiv`. |
| `EvmWord.smod` (def) | `EvmWordArith/SDiv.lean` (or sibling `SMod.lean`) | `BitVec.smod` lifted to `EvmWord` with `y=0 → 0`. |
| `EvmWord.smod_correct` | same | spec formula in terms of `a.toInt`, `b.toInt`, `Int.tmod`. |

Reference shape: `EvmAsm/Evm64/EvmWordArith/Div.lean` already gives
`EvmWord.div` / `mod` with `if hbnz then bv_udiv else 0` and proves a
uniqueness bridge `div_eq_of_euclidean`. The signed variants follow the
same pattern, plus a single extra `if` for the SDIV overflow case. Lean
already has `BitVec.sdiv` (used in `Rv64/Instructions.lean:115`) and the
SAIL bridge `sdiv_eq_to_bits_truncate` in
`Rv64/SailEquiv/MExtProofs.lean:74`, so the underlying primitives are
in place.

Slice 3 (`evm-asm-kvs4`) covers SDIV; slice 5 (`evm-asm-bjnb`) covers
SMOD. Both are pure 256-bit proofs with no RISC-V code.

## 3. Reuse strategy: callable shim around `evm_div` / `evm_mod`

The existing unsigned divider (`EvmAsm/Evm64/DivMod/Program.lean :: evm_div`)
already takes a long path through Knuth Algorithm D and is the most
expensive opcode body in the project. We **must** reuse it rather than
reimplement. The pattern is the same one used by EXP for multiplication
(`EvmAsm/Evm64/Multiply/Callable.lean`), which @pirapira called out as
the model in the slice 1 description.

### `evm_div_callable` / `evm_mod_callable` shim layout

```
def evm_div_callable : Program := evm_div ;; cc_ret    -- returns via JALR x0 x1 0
def evm_mod_callable : Program := evm_mod ;; cc_ret
```

Both shims live under `EvmAsm/Evm64/DivMod/Callable.lean`. They mirror
the `mul_callable` shim 1:1:

* Length lemma: `evm_div_callable.length = evm_div.length + 1`.
* `byte_length` lemma scaling by 4.
* `_code` abbreviation `CodeReq.ofProg base evm_div_callable`.
* Sub-code lemmas isolating the body and the `JALR` so that the existing
  `evm_div_stack_spec` and the LP64 calling-convention `ret_spec` can be
  composed at the byte-disjoint regions.
* Round-trip `_function_spec` derived via `callNear_function_spec` (the
  proven helper at `EvmAsm/Rv64/CallingConvention.lean`).

The shim is non-leaf-aware via `cc_prologue` / `cc_epilogue` only if the
caller (SDIV / SMOD wrapper) needs to spill `ra`. The simplest routing is
to make SDIV / SMOD the non-leaf and keep the divisor body as a leaf
(no inner `JAL`s).

### evm_sdiv / evm_smod (caller) outline

```
def evm_sdiv : Program :=
  -- prologue: save ra
  cc_prologue ;;
  -- read top two stack words into the (sp+32, sp+40, ..., sp+56) and
  -- (sp+64, ..., sp+88) input slots used by evm_div
  read_top_two_stack_words_into_evm_div_inputs ;;
  -- absolute-value normalization on both operands, capturing sign bits
  -- in saved registers (s1=sign(a), s2=sign(b))
  abs_in_place_at sp+32 ;;             -- sets s1 = sign(a) before negation
  abs_in_place_at sp+64 ;;             -- sets s2 = sign(b) before negation
  -- early-out: if (a, b) == (-2^255, -1), short-circuit result = -2^255
  -- early-out: if b == 0, result = 0  -- inherited from evm_div semantics
  --                                     (evm_div already returns 0 on b=0)
  JAL x1, evm_div_callable ;;           -- 64-bit absolute quotient lands at sp+96..
  -- sign correction: negate the 256-bit quotient if (s1 XOR s2) == 1
  conditional_negate_256_bit_at sp+96 ;;
  -- push result onto the EVM stack
  push_to_stack ;;
  cc_epilogue
```

`evm_smod` is identical except:

* sign correction uses `s1` only (sign(dividend)),
* no `−2^255 / −1` overflow case (the spec returns 0 for `y==0`,
  `sign(x) * (|x| % |y|)` otherwise — even SMOD(−2^255, −1) gives 0
  because `2^255 % 1 = 0`),
* it copies the absolute remainder out of `sp + 4056..4032` instead of
  the quotient.

### Sign extraction — single-instruction primitive

`sign(v)` for a 256-bit two's-complement word is the **top bit of limb 3**.
On RV64 with our 4×64 layout, we already store limbs at offsets 8 / 16 /
24 / 32 from a base; the top limb is at the highest offset (e.g.
`sp + 32 + 24` for the dividend). One `LD t0, sp+56` followed by
`SRLI t0, t0, 63` gives 0 / 1 in `t0`. No 256-bit branching: just XOR the
two sign bits and feed to the conditional-negate block.

### Conditional 256-bit negate

For absolute-value pre-pass, given a sign bit `s ∈ {0, 1}`, we want
`v` if `s = 0` and `−v` (two's complement) otherwise. Two-instruction-per-limb:

```
  XOR  l_i, l_i, mask          -- mask = (s == 1) ? all-ones : 0
  ADD  l_0, l_0, s             -- +1 only on the lowest limb (with carry)
  -- propagate carry across 4 limbs via SLTU / ADD
```

Total ~16 instructions for the 256-bit conditional negate (mask, four
XORs, +1 on limb 0, three carry propagations using SLTU+ADD). Same
sequence is reused for the post-divide sign correction, so factor it as
`negate_256_at` taking a base address + sign register.

The `mask = −s` trick: `s ∈ {0,1}`, so `mask = 0 − s = (s == 1 ? all-ones :
0)`. One `SUB` produces the mask.

### Edge cases and the −2^255 / −1 overflow

Detect with two equality tests on raw limbs **before** the abs-pre-pass:

* `a == −2^255` ⇔ limb3 == 0x8000_0000_0000_0000 ∧ limb2 = limb1 = limb0 = 0.
* `b == −1` ⇔ all four limbs == 0xFFFF_FFFF_FFFF_FFFF.

If both hold, jump past the divide and write the dividend back as the
quotient; sign-correction is skipped (the result is exactly `−2^255`).

This avoids the `abs(−2^255)` overflow inside the absolute-value step
(`−(−2^255) = 2^255` doesn't fit signed 256). Without this short-circuit
we would need a 257-bit absolute value, which we don't want.

For SMOD, the spec result for `(−2^255, −1)` is `0` (since `2^255 % 1 = 0`),
which is what the abs/divide/sign-correct path **already** returns
correctly. So **SMOD does not need the overflow short-circuit at all**.

## 4. Register and scratchpad plan

LP64 calling convention (`EvmAsm/Evm64/CallingConvention.lean`):

| Reg | Role in evm_sdiv / evm_smod |
| --- | --- |
| x1 (ra) | saved by `cc_prologue` at `sp+8` |
| x2 (sp) | EVM-frame pointer, unchanged across body |
| x12 (a2) | EVM stack pointer (per zkvm-standards) |
| x10 (a0) | scratch / first arg / used by `evm_div` |
| x11 (a1) | scratch |
| x5..x7 (t0..t2) | temporaries in abs-pre-pass and sign-correction |
| x8 (s0) | sign(a) bit, saved across the call |
| x9 (s1) | sign(b) bit (SDIV) or unused (SMOD) |

`evm_div` already uses scratchpad cells at `sp + 32..56` (operand b),
`sp + 64..88` (operand a), `sp + 4056..4032` (denormalized remainder),
`sp + 4088..4064` (quotient) — see
`EvmAsm/Evm64/DivMod/Compose/SharedLoopPost.lean` for the post-state
naming. SDIV / SMOD reuse this layout unchanged: the abs-pre-pass writes
into the same `b`/`a` slots that `evm_div` already expects, and the
post-divide sign correction reads from the quotient slot for SDIV or the
remainder slot for SMOD before pushing onto the EVM stack.

No new scratchpad cells are introduced. `s0` / `s1` are *registers* saved
across the call, not memory cells, because the divider body does not
touch saved-set registers per LP64.

## 5. Lemma surface (forward look — slices 3, 4, 5)

| Slice | Lemma | Shape |
| --- | --- | --- |
| 3 | `EvmWord.sdiv_correct` | pure BitVec |
| 5 | `EvmWord.smod_correct` | pure BitVec |
| 4 | `evm_div_callable_function_spec` | `cpsTriple` round-trip via `callNear_function_spec` |
| 4 | `abs_negate_256_at_spec` | `cpsTriple` block spec for abs-pre-pass / sign correction |
| 4 | `evm_sdiv_stack_spec` | top-level `evmStackIs` → `evmStackIs` |
| 5 | `evm_mod_callable_function_spec` | analogous |
| 5 | `evm_smod_stack_spec` | analogous |
| 6 | dispatcher row + `gh issue` close-proposal comment | wiring only |

Skeleton slice 2 (`evm-asm-kyp6`) creates the empty
`EvmAsm/Evm64/SDiv/{Program,LimbSpec,Compose,Spec}.lean` and
`EvmAsm/Evm64/SMod/{...}.lean` per `Evm64/OPCODE_TEMPLATE.md`, plus the
two umbrella files `EvmAsm/Evm64/SDiv.lean` and `EvmAsm/Evm64/SMod.lean`
imported from `EvmAsm/Evm64.lean`. The callable shim lives under
`EvmAsm/Evm64/DivMod/Callable.lean` (sibling to the existing DivMod
content), so neither SDIV nor SMOD imports the other.

## 6. Out of scope for this design slice

* Performance (gas cost is `GAS_LOW` static, same as DIV/MOD; covered by
  parent #117 / `evm-asm-y6gx`, not here).
* Specs of the abs / sign-correction blocks; only their *interface* is
  fixed here.
* Any change to the unsigned `evm_div` / `evm_mod` body. The shim is
  purely additive.
* The non-DivMod variant of the −2^255 overflow case (e.g. EXP at
  −2^255). That belongs to its own opcode subtree.

## 7. Open questions deferred to slice 4

* Whether the abs-pre-pass overwrites the original operand cells in-place
  (cheaper, current sketch) or writes to a fresh scratchpad pair
  (cleaner separation, requires extra cells). Recommended: in-place,
  matching how `evm_mul` writes back to its argument cells.
* Whether to expose a single `evm_div_callable` shim and call it twice
  (once for SDIV, once for SMOD) or to expose two distinct shims. A
  single shim is fine; SDIV reads the quotient slot and SMOD reads the
  remainder slot, both already populated by the divider body.
* Heartbeat budget for the composed `evm_sdiv_stack_spec` proof — likely
  fine without bumps because the divider body is already factored into
  `evm_div_stack_spec` and the abs / sign-correction blocks are short
  (~16 instructions each). Defer measurement to slice 4.

---

Authored by @pirapira; implemented by Hermes-bot (evm-hermes). Refs
GH #90, beads parent `evm-asm-34sg`, slice `evm-asm-rtt5`.
