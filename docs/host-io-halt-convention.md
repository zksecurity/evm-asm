# Design: host-I/O HALT convention

Status: Open (2026-05-08)
Authors: @pirapira (decision); Hermes-bot (drafting)
Refs: beads `evm-asm-zgd4y`; parent `evm-asm-96ysd`; ADR
[`docs/zkvm-host-io-interface.md`](zkvm-host-io-interface.md);
zkvm-standards I/O interface README at
`EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`

## Context

The host-I/O ADR (`docs/zkvm-host-io-interface.md`) commits us to the
eth-act zkvm-standards C ABI for *input* (`read_input`) and *output*
(`write_output`). The vendored README, however, is silent on
**termination** — there is no `halt()` / `exit()` / `done()` function in
the zkvm-standards I/O interface. The verified guest still needs *some*
way to signal that it has finished producing public output and the
zkVM should stop stepping the machine.

Today the verified RISC-V code uses SP1's HALT convention:

- `EvmAsm/Rv64/Execution.lean` line 394: `step` returns `none` when the
  current instruction is `ECALL` with `t0 = 0`.
- `step_ecall_halt` (line 614) is the corresponding Hoare-triple-style
  lemma consumed by termination proofs.
- The host-I/O ADR's mapping table reflects this with a `(no
  counterpart — see Open question)` entry for `t0 = 0x00`.

That convention is shape-compatible with SP1 (`ecall` + `t0 = 0`), but
it is *not* part of the zkvm-standards C ABI we now claim to target. We
need to either keep it as a documented local extension, propose an
upstream addition, or change the verified semantics so termination is
implicit. This document records the options and recommends one for
@pirapira's decision.

## Constraints

- The verified `step` function is total in the sense of returning
  `Option MachineState`; *some* observable signal must drive the
  `none` result, so termination cannot be made invisible to the spec.
- Whatever we pick must be expressible as a one-line bead in the
  ECALL-handler dispatch (`Execution.lean` line 394 region) so the
  migration cost is bounded.
- Whatever we pick must compose with the verified Hoare triples that
  consume `step_ecall_halt` today (e.g. `EvmAsm/Rv64/HintSpecs.lean`,
  the `run_stateless_guest` driver under construction).
- The chosen mechanism should not silently re-introduce the streaming
  shape `read_input` was meant to retire (i.e. "termination = end of
  input buffer" is suspect because it conflates input exhaustion with
  intentional exit).

## Options

### A. Keep SP1 `t0 = 0` HALT as a local convention (status quo)

Document in the host-I/O ADR (§HALT) and in the zkvm-standards
vendored README a delta note: "evm-asm uses SP1's `t0 = 0` HALT
convention pending an upstream zkvm-standards halt() addition." No
code or proof changes; only docs.

**Pros.**
- Zero code churn. Existing `step_ecall_halt`, every termination
  Hoare triple, and every `native_decide` ECALL/halt example keep
  working unmodified.
- HALT is structurally similar across zkVMs (SP1, RISC0, etc.) — we
  are not picking an exotic encoding.
- The host-I/O ADR already tags this as the default fallback; the
  follow-up only needs to lift the "Open" tag.

**Cons.**
- Adds a documented but real divergence between the verified surface
  and the zkvm-standards C ABI we claim to target. Future readers of
  the ADR will see a mismatch unless they read the §HALT note
  carefully.
- If zkvm-standards later picks a *different* halt mechanism (option
  B), we pay the migration cost twice: once to land it locally, once
  to retire the SP1 entry.

### B. Propose a `halt()` (or `exit(int code)`) addition to zkvm-standards upstream

File an issue / PR against the eth-act zkvm-standards repo proposing a
new C function in `standards/io-interface/README.md`:

```c
void halt(void);                  // simplest variant
// or:
void exit(uint32_t exit_code);    // SP1-compatible (a0 carries code)
```

Then mirror the chosen shape in evm-asm: keep `t0 = 0` as the
*handler-side* dispatch ID (consistent with the "syscall IDs are
handler-side, not ABI" stance), but rename the ADR mapping row to
point at the new upstream symbol once it lands.

**Pros.**
- Fully closes the ADR gap. The host-I/O surface ends up with a clean
  three-function ABI (`read_input`, `write_output`, `halt`).
- Aligns evm-asm with whatever convention other zkvm-standards
  consumers settle on; reduces drift.

**Cons.**
- Requires an upstream conversation with unbounded latency (we don't
  control the zkvm-standards merge cadence). Until that lands the
  ADR still has an open hole.
- Bikeshed risk on the signature (`halt` vs `exit(code)` vs returning
  status to the host runner). evm-asm currently emits no exit code,
  so adopting `exit(uint32_t)` retroactively would force a spec
  decision on what code the verified guest emits.

### C. End-of-input as implicit HALT (rejected)

Treat exhaustion of the `read_input` buffer (`*buf_size == 0` after
all bytes have been consumed by the guest) as the termination signal.
The handler-side `step` returns `none` once a `read_input` call would
return an empty buffer.

**Pros.**
- Removes the need for *any* explicit halt syscall.

**Cons (decisive).**
- Conflates "input is empty" with "guest is done." A guest that
  legitimately processes a zero-byte input (e.g. a no-op stateless
  block) cannot terminate.
- Forces every guest to consume input it doesn't need just to drive
  termination, which inverts the `read_input` shape (single-call,
  idempotent, ptr+len out).
- Re-introduces the streaming-style coupling the zkvm-standards
  read_input shape was specifically designed to avoid.

This option is mentioned for completeness; it is not a viable choice.

## Recommendation

**Adopt Option A (keep SP1 `t0 = 0` HALT) as the immediate decision,
and file Option B (upstream `halt()` addition) as a non-blocking
follow-up beads task.** Rationale:

1. Option A has zero code/proof cost and is consistent with the
   "syscall IDs are handler-side, not ABI" stance the host-I/O ADR
   already takes for `read_input` / `write_output` dispatch numbers.
2. The host-I/O migration parent (`evm-asm-96ysd`) is gated on
   substantive Lean refactors (PartialState plumbing, ECALL handler
   reshape, RLP wrapper rewrite). Blocking that parent on an upstream
   spec PR would be the wrong dependency direction.
3. Option B is genuinely useful but is conversation-bound, not
   verification-bound. It belongs in its own beads task with a clear
   "track the upstream PR" lifecycle, not on the critical path to
   `run_stateless_guest`.

## Action items

If @pirapira approves the recommendation:

1. **Lift the "Open question" tag in
   `docs/zkvm-host-io-interface.md` §HALT.** Replace the open-question
   wording with a one-paragraph "Decision: keep SP1 `t0 = 0` HALT as a
   local extension" reference to this document, plus an explicit note
   that the syscall ID is handler-side (mirroring the
   `read_input` / `write_output` framing).
2. **Update the mapping table.** Change the `0x00 / HALT` row's
   counterpart cell from `(no counterpart — see Open question)` to
   `(local extension; see host-io-halt-convention.md)`.
3. **File a non-blocking follow-up beads task** (P3, owner
   Hermes-bot) for Option B: draft the upstream zkvm-standards issue
   proposing a `halt()` addition. This task does not block the
   host-I/O migration parent; it is a parallel docs-only thread.
4. **Close `evm-asm-zgd4y`** referencing this document and the
   follow-up task.

## Notes on `step_ecall_halt` semantics

For clarity, the verified Hoare triple `step_ecall_halt`
(`EvmAsm/Rv64/Execution.lean` line 614) only requires:

- the current instruction at PC is `ECALL`,
- `getReg s Reg.x5 = 0` (SP1 `t0 = 0`),

and concludes `step s = none`. It does *not* read or write to the
public-output buffer, the input buffer, or any register beyond the
guard. Switching to Option B would amount to changing the guard's
syscall ID constant; the triple's structure is untouched.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
