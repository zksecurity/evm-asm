# ADR: zkvm-standards I/O interface as the canonical host-I/O C ABI

Status: Accepted (2026-05-06)
Authors: @pirapira (decision); Hermes-bot (drafting)
Refs: beads `evm-asm-96ysd`; sibling ADR
[`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md);
GH #114, #116

## Decision

The canonical C interface for *host-side I/O* — the channel by which the
verified guest receives its private input and emits its public output —
is the eth-act zkvm-standards I/O interface vendored at

  `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`

It declares two C functions:

```c
void read_input(const uint8_t** buf_ptr, size_t* buf_size);
void write_output(const uint8_t* output, size_t size);
```

The README — not any particular zkVM's syscall list — is the source of
truth for argument layout, idempotency, and concatenation semantics. EVM-
asm's RISC-V ECALL handlers and Lean Hoare triples lower onto these two
functions; concrete syscall IDs and the on-machine input buffer
representation are implementation details of the dispatch layer, not
part of the C ABI.

This ADR mirrors the accelerator-side decision recorded in
[`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md):
function set + argument layout come from zkvm-standards; ECALL framing
follows the RISC-V convention SP1 also uses; concrete syscall IDs are
handler-side and tracked separately.

## Why this is non-obvious from the code today

`README.md` historically said "the ECALL-based syscall mechanism follows
SP1's conventions." That is a statement about the *mechanism* (RISC-V
`ECALL` with syscall ID in `t0`/`a7`, args in `a0`–`a2`), not about the
*function set* or the I/O semantics. SP1 ships its own host-I/O surface
(streaming `HINT_LEN` + `HINT_READ` for input, `COMMIT` for committed
public values); zkvm-standards specifies a different shape.

The two surfaces are not interchangeable:

- `read_input` is *single-call*, *idempotent*, and returns a pointer +
  length into a (possibly read-only) zkVM-managed buffer. There is no
  two-phase "ask for length, then stream bytes" call. zkVMs that don't
  preload input must materialize the entire input into an internal
  buffer during machine initialization so that `read_input` can be
  safely called from `main`.
- `write_output` is *concatenating*, takes `(ptr, size)`, returns no
  error code, and may be called multiple times — successive buffers are
  concatenated to form the public output. It does not framepack
  word-pair commits the way SP1's `COMMIT` does.

The verified RISC-V code today still implements the SP1-shaped surface;
the Lean specs in `EvmAsm/Rv64/HintSpecs.lean`,
`EvmAsm/Rv64/RLP/Phase4HintLen.lean`, and `EvmAsm/Rv64/RLP/Phase4HintRead.lean`
encode the streaming hint contract. Migration to the zkvm-standards C
ABI is tracked under parent bead `evm-asm-96ysd`.

## Mapping: current SP1 ECALL handlers ↔ zkvm-standards C ABI

The current `EvmAsm/Rv64/Execution.lean` `step` function dispatches the
following ECALL syscalls (all selected by `t0 = x5`):

| t0 (hex) | SP1 syscall | Current Lean handler | zkvm-standards counterpart |
|----------|-------------|----------------------|----------------------------|
| `0x00`   | HALT        | `step_ecall_halt` (returns `none`)        | (no zkvm-standards counterpart — see §HALT below for the local convention) |
| `0x02`   | WRITE fd=13 | append a1..a1+a2 bytes from memory to public values | `write_output(output, size)` (shape-compatible: ptr+size, concatenating) |
| `0x10`   | COMMIT selector, reshaped | `s.writeOutput a0 a1` appends bytes from memory to public values | `write_output(output, size)` |
| `0xF0`   | HINT_LEN    | returns `privateInput.length` in a0       | replaced by `read_input` (length is `*buf_size` out-parameter; no separate length call) |
| `0xF1`   | HINT_READ   | streams `(a1)` bytes from `privateInput` into guest memory at `a0` as LE dwords | replaced by `read_input` (no streaming — input lives in a single buffer the guest indexes into) |

*ECALL framing* (instruction encoding, register convention,
return-via-`a0`) is unchanged by this ADR — it is the same RISC-V
convention every zkVM uses and is orthogonal to the host-I/O ABI.

## Migration plan (high level)

Concrete Lean changes are tracked under parent bead `evm-asm-96ysd`; the
shape changes are:

1. **Lean machine state.** Decide where the input buffer lives. The
   current `MachineState.privateInput : List UInt8` matches the
   *streaming* model (consumer pulls bytes); for `read_input`, the
   buffer must be addressable in guest memory (or in an abstract
   read-only region the spec exposes) so that `read_input` can return a
   pointer into it. **Decided** in
   [`docs/zkvm-host-io-input-buffer-design.md`](zkvm-host-io-input-buffer-design.md):
   reuse `privateInput` plus a new immutable `inputBufBase : Word`
   field carrying the guest-visible base address. Refinement to a
   dedicated read-only memory region is deferred.
2. **ECALL handlers.** Replace the `HINT_LEN`/`HINT_READ` cases of
   `step` with a single `read_input` handler (ptr+len-out semantics).
   Reshape `COMMIT` (and/or `WRITE fd=13`) into a `write_output`
   handler. The `0x10` branch now has the `write_output(ptr, size)`
   shape; `WRITE fd=13` remains as a compatibility spelling. Keep SP1 syscall IDs as the dispatch numbers for now;
   document that the IDs are handler-side, not ABI.
3. **RLP wrappers.** Rewrite `Phase4HintLen.lean` and `Phase4HintRead.lean`
   to consume the `read_input` ptr+len once and index into the buffer,
   then re-prove the affected Hoare triples.
4. **Doc surface.** Update `README.md`, `PLAN.md`, and `AGENTS.md` to
   replace the "follows SP1 hint/commit conventions" wording with a
   pointer to this ADR.

## HALT

zkvm-standards' I/O interface README is silent on halt/termination, so
HALT is not part of the canonical C ABI this ADR adopts. EVM-asm's
local convention is to **keep SP1's `t0 = 0x00` HALT semantics** as the
guest's termination signal:

- Encoding: `ECALL` with `x5` (alias `t0`) set to `0x00`.
- Effect: `EvmAsm/Rv64/Execution.lean :: step` returns `none`, ending
  the verified execution. No further state transition is defined.
- Status code: today the handler ignores any register payload. If a
  future revision wants to surface a `zkvm_status`-style exit code, the
  natural choice is `a0` (matching the accelerator return-code
  convention in
  [`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md)).

This is a **local** convention, not a zkvm-standards one — the same
caveat that applies to syscall ID numbering in §"Mapping" above. We
choose option (a) from the design follow-up (beads `evm-asm-zgd4y`):

- (a) Keep SP1 `t0=0` as the local halt convention and document it
  here. **Adopted.** Cheapest; no upstream coordination; preserves the
  existing `step_ecall_halt` Hoare triple surface.
- (b) Propose a `halt(zkvm_status)` addition to zkvm-standards
  upstream. Filed as a longer-running follow-up; not blocking the
  read_input / write_output migration under `evm-asm-96ysd`.
- (c) Treat exhaustion of the `read_input` buffer as implicit halt.
  Rejected — guests need to signal failure status, not just "input
  drained."

A guest that wants to return a non-zero exit status today can write a
status word via `write_output` immediately before HALT; the verifier
inspects committed output, not register state at halt. If/when (b) is
adopted upstream, this section is updated and the dispatch table in
§"Mapping" gains a `halt(zkvm_status)` row.

## Maintenance

Update this ADR when:

- The vendored zkvm-standards I/O interface README is bumped (record
  the source commit).
- A migration slice under `evm-asm-96ysd` lands a shape change visible
  to the C ABI surface (the mapping table above needs ticking).
- The decision itself is revisited (e.g. eth-act zkvm-standards is
  superseded, or the project decides to keep the SP1 surface).

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
