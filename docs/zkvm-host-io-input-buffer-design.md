# Design: `read_input` on-machine layout

Status: Accepted (2026-05-08)
Authors: @pirapira (decision); Hermes-bot (drafting)
Refs: parent bead `evm-asm-96ysd`; slice 1 bead `evm-asm-zyy97`;
sibling ADR [`docs/zkvm-host-io-interface.md`](zkvm-host-io-interface.md);
upstream spec
[`EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`](../EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md);
GH #114, #116.

This is the design-only deliverable for slice 1 of the host-I/O migration.
It picks the on-machine representation for the zkvm-standards `read_input`
buffer, the C ABI mapping onto RISC-V state, the idempotency model, and
the mutability convention. Slices 2–5 (handler implementation, RLP
wrapper rewrite, `write_output`, retire `HINT_*`) will refer back to this
document.

## TL;DR

| Question | Decision |
|----------|----------|
| Where does the input buffer live in `MachineState`? | **Reuse the existing `privateInput : List (BitVec 8)` field**, plus one new `inputBufBase : Word` field giving the guest-visible base address of an *abstract* read-only image of `privateInput`. (Option (a) augmented with an explicit base.) |
| C ABI mapping (`read_input(&buf_ptr, &buf_size)`) | `a0` = pointer to an 8-byte cell that receives `buf_ptr`; `a1` = pointer to an 8-byte cell that receives `buf_size`. The handler stores `s.inputBufBase` at `[a0]` and `s.privateInput.length` at `[a1]`. |
| Syscall ID | Reuse `t0 = 0xF0` (the slot currently used by `HINT_LEN`). After the migration `0xF1` (HINT_READ) is unused; slice 4 deletes it. |
| Idempotency | Enforced by the *handler being a pure function of `s`* — `read_input` does not mutate `privateInput`, `inputBufBase`, or any other ABI-visible field. Calling it twice yields identical out-parameters. No set-once flag is needed. |
| Mutability of input bytes | Conventionally read-only. Callers must not write to `[inputBufBase, inputBufBase + privateInput.length)`. The handler does **not** install the bytes into `s.mem`; instead `Phase4` wrappers (slice 3) consume `privateInput` directly via the byte-list, mirroring how `HINT_READ` does it today, but indexed by offset rather than streamed. |

The rest of this document explains the trade-offs and pins down the
shape that slices 2–5 will implement.

## Options considered

The bead enumerates three layouts. We assessed each against four
criteria: minimum diff to today's code; faithfulness to the
zkvm-standards C contract; ease of re-proving the affected RLP Hoare
triples; and friendliness to a future "input bytes are addressable
memory" refinement.

### (a) Reuse `privateInput`, return a constant pointer plus the array length

* **Minimum diff:** highest. `privateInput` already exists, is invariant
  under every non-`HINT_READ` instruction (see
  `Rv64/Execution.lean:222-228`), and is the source of truth that
  `Phase4HintLen.lean` / `Phase4HintRead.lean` already reason about.
* **Faithfulness to spec:** good. The spec admits a "may be read-only"
  buffer; an abstract `List (BitVec 8)` plus a base address satisfies
  that.
* **Re-proof effort:** moderate. The current Phase4 specs are stated in
  terms of `privateInput.length` and `privateInput.take/drop`. After
  migration they will be stated in terms of `privateInput[offset..]`,
  same data, slightly different access pattern. No new field types.
* **Refinement story:** good. A future slice can replace
  `inputBufBase` with a real read-only memory region and add a lemma
  `s.getByte (inputBufBase + i) = privateInput[i.toNat]` without
  disturbing slice 2–5 callers.

### (b) Add a fresh dedicated read-only memory region

* **Minimum diff:** lowest. Requires a new `MachineState` field plus
  per-region get/set lemmas, plus updates to every existing `setReg`
  / `setMem` / `setPC` framing simp lemma (the analogue of the existing
  `privateInput_setReg`, `privateInput_setMem`, … lemma family).
* **Faithfulness:** highest in the limit. Cleanly separates ABI input
  bytes from regular memory.
* **Re-proof effort:** highest. Phase4 specs would have to switch from
  `privateInput`-shaped reasoning to a new region. The migration would
  have to land both the new region and the read API in one slice.
* **Refinement story:** trivial — that *is* the refinement.

### (c) Place input at a fixed virtual address inside regular memory at startup

* **Minimum diff:** medium. `MachineState` gains no new field, but the
  initialization story changes ("the genesis machine has bytes laid out
  in `mem` starting at some fixed address"). All Phase4 reasoning must
  be reframed in terms of `getByte` against `mem`.
* **Faithfulness:** medium. The bytes are read-only only by convention.
  Nothing in the type system forbids a buggy program from
  `setByte`-ing them.
* **Re-proof effort:** highest. Phase4 specs become byte-level memory
  specs from the start.
* **Refinement story:** none — this *is* the concrete model, with no
  abstraction to refine.

### Decision: option (a), augmented with an explicit base address

We pick (a) because it minimizes the diff to the current model and
preserves the existing `privateInput` framing infrastructure (the
`privateInput_setReg` / `privateInput_setMem` / `privateInput_setByte`
/ `privateInput_setHalfword` family of `@[simp]` lemmas in
`Rv64/Basic.lean` and the `privateInput_execInstrBr` lemma in
`Rv64/Execution.lean`). The cost of (a) is that input bytes do not
appear in `s.mem`; this is acceptable because zkvm-standards
explicitly says the buffer "may be read-only", and the only
verification consumers we have today (Phase4 wrappers) are happy to
reason against `privateInput` directly.

We do add **one new field**, `inputBufBase : Word`, defaulting to a
sentinel chosen far from any address space the verified code uses
(see "Concrete sentinel" below). This is the C-level pointer
`read_input` returns through its first out-parameter. Keeping it as a
distinct field — rather than hard-coding a constant in the handler —
lets the eventual refinement to option (b) just rename the field
`inputBufBase` to "the base of the new read-only region" without
touching call sites.

## Concrete `MachineState` shape

After slice 2 (handler implementation), the relevant fields will be:

```lean
structure MachineState where
  ...
  /-- Private input bytes (the zkvm-standards `read_input` buffer). -/
  privateInput : List (BitVec 8) := []
  /-- Guest-visible base address of `privateInput` returned by `read_input`. -/
  inputBufBase : Word := 0x0000_0000_8000_0000#64
  ...
```

The default `0x8000_0000` is well above any address the verified code
currently writes to (Stack / scratchpad / EL.RLP regions live below
`0x4000_0000` in current uses) and well below `2^64 - 2^21` so that
`signExtend21` offsets from caller-provided `inputBufBase` do not wrap.
The exact constant is not part of the C ABI — it is a
machine-initialization choice. Slice 2 is free to refine the default
once the read-only region (option (b)) lands.

`privateInput` retains its existing default `[]`. No other field is
touched. Crucially, `inputBufBase` is *immutable* under every
instruction in `execInstrBr` and under the `read_input` /
`write_output` handlers, so it inherits framing for free under the
existing `<field>_setX` lemma pattern (slice 2 will add the four lemmas
`inputBufBase_setReg`, `inputBufBase_setMem`, `inputBufBase_setPC`,
`inputBufBase_setByte` plus their halfword/word32 counterparts and the
`inputBufBase_execInstrBr` framing lemma, mirroring the existing
`privateInput_*` family).

## C ABI mapping onto RISC-V

The zkvm-standards prototype is

```c
void read_input(const uint8_t** buf_ptr, size_t* buf_size);
```

Argument-passing convention (LP64, matching everywhere else in this
repo: see `EvmAsm/Evm64/CallingConvention.lean`):

* `a0` (`x10`) carries `buf_ptr` — a pointer to an 8-byte cell into
  which the handler writes the buffer base address.
* `a1` (`x11`) carries `buf_size` — a pointer to an 8-byte cell into
  which the handler writes the buffer length.

After `read_input` returns, the guest reads its own `a0`/`a1`-pointed
cells to recover the buffer's `(ptr, len)` pair — exactly as the C
prototype prescribes.

### Effect on `MachineState`

The handler is a pure function of `s`:

```
read_input(s) :=
  let s1 := s.setMem s.x10 s.inputBufBase
  let s2 := s1.setMem s1.x11 (BitVec.ofNat 64 s.privateInput.length)
  some (s2.setPC (s.pc + 4))
```

(Concrete Lean shape is slice 2's job; this pseudocode pins the
intent.)

Notes on the shape:

* `setMem` writes a doubleword at the caller-supplied 8-byte-aligned
  pointer; alignment of `a0`/`a1` is the caller's obligation and is
  expressed as a precondition in the gen-spec.
* The handler does **not** mutate `privateInput`, `inputBufBase`,
  `regs` (other than via `setMem`-induced framing — `setMem` does
  not touch `regs`), `committed`, `publicValues`, or `code`.
* `setPC (s.pc + 4)` advances over the `ECALL` instruction, matching
  every other ECALL handler in this file.

### No streaming, no two-phase length call

The current `HINT_LEN` returns `privateInput.length` in `a0` (a
register, not a memory cell). The zkvm-standards `read_input` writes
to a *memory cell* pointed to by `a1`. The change is shape-visible to
callers and is the reason this migration cannot be done as a thin
rename.

The current `HINT_READ` *streams* bytes from `privateInput` into guest
memory and *consumes* them (`privateInput := privateInput.drop n`).
zkvm-standards' `read_input` does no such thing — the buffer remains
addressable indefinitely. This is the central simplification of the
migration: Phase4 wrappers (slice 3) stop being a stream consumer and
become a fixed-buffer reader indexed by offset.

## Idempotency

The C spec says `read_input` is idempotent — successive calls return
the same `(ptr, size)` pair. Our handler enforces idempotency
*structurally*, not via a flag:

* `read_input` writes `s.inputBufBase` (an immutable field) and
  `BitVec.ofNat 64 s.privateInput.length`.
* `privateInput` is invariant under every non-`HINT_READ` instruction
  (slice 4 deletes the only mutation site, `HINT_READ`).

After slice 4 lands, `privateInput.length` is invariant under every
instruction, so two `read_input` calls trivially produce the same
out-parameters regardless of program counter or intervening
non-input-mutating instructions. We do **not** introduce a
`readInputDone : Bool` flag — the spec asks for idempotency, not for
"first call is special".

## Mutability of input bytes

zkvm-standards: `const uint8_t* buf_ptr` — the bytes are readable, may
be read-only, must not be written by the application.

In our model, the bytes are not installed into `s.mem`, so the
question of write-protection is moot at the RISC-V level: a buggy
program that does `setByte (inputBufBase + i) v` modifies regular
memory at that virtual address but does **not** modify
`privateInput`. The Phase4 spec consumes `privateInput` directly, so
input correctness is preserved by construction.

This is a strictly *stronger* read-only guarantee than option (c)
provides, at the cost of decoupling the abstract input from
addressable memory. If a future verification consumer needs
`getByte (inputBufBase + i) = privateInput[i.toNat]`, slice 4+ can
add it as an axiom that the eventual concrete machine satisfies.

## Phase4 wrapper shape (preview, not slice 1)

Slice 3 will rewrite `Rv64/RLP/Phase4HintLen.lean` and
`Phase4HintRead.lean` against this design. The preview shape:

```lean
-- old (HINT_LEN streaming):
--   read length into a0, decrement privateInput head
-- new (read_input one-shot):
--   call read_input once at Phase 4 entry; cache (base, len)
--   in two scratch dwords; subsequent reads do `getByte (base + off)`
--   resolved against the same cached `privateInput`.
```

Re-proof cost: the `Phase4HintLen_spec` Hoare triple changes from
"after the call, `a0 = privateInput.length`" to "after the call,
`[buf_size_ptr] = privateInput.length` and `[buf_ptr_ptr] =
inputBufBase`". `Phase4HintRead_spec` becomes a memory-read at
`inputBufBase + off` instead of a streaming consumption.

These changes are deferred to slice 3; slice 1 only locks the field
shape and the handler signature.

## What slice 1 does *not* decide

* **HALT convention** — open question, deferred to follow-up bead
  `evm-asm-22tbc`.
* **Concrete syscall ID for `read_input`** — slice 2 may keep
  `t0 = 0xF0` (currently HINT_LEN) for minimum churn or pick a fresh
  ID. This document only requires that the ID be *some* fixed
  constant; the C ABI doesn't see it.
* **`write_output` implementation** — sibling slice `evm-asm-rv8pv`.
* **`inputBufBase` default constant** — slice 2 may pick a different
  address if it interferes with concrete tests; the contract is just
  "fixed and far from current address space usage".

## Acceptance for this slice

* Doc lands at `docs/zkvm-host-io-input-buffer-design.md`.
* No Lean changes in this slice (an empty `inputBufBase` field stub
  is *not* added here — slice 2 introduces it together with the
  handler that uses it).
* `lake build` is unaffected.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
