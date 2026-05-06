# ADR: zkvm_accelerators.h as the canonical accelerator C ABI

Status: Accepted (2026-05-06)
Authors: @pirapira (decision); Hermes-bot (drafting)
Refs: beads `evm-asm-y4o09`, `evm-asm-nr2sk`; GH #114, #116

## Decision

The canonical C interface that the verified RISC-V guest targets for
cryptographic accelerators is the header

  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`

(vendored from <https://github.com/eth-act/zkvm-standards>). All EVM
precompile dispatch (`0x01`–`0x11`, `0x100`) and the non-precompile
accelerators `KECCAK256` and `secp256k1_verify` lower onto a function
declared in that header. The header — not a particular zkVM — is the
source of truth for argument layout, return-value framing
(`zkvm_status` / `ZKVM_EOK`), and per-function preconditions.

## Why this is non-obvious from the code today

`README.md` historically said "the ECALL-based syscall mechanism follows
SP1's conventions." That is a statement about the *mechanism* (RISC-V
`ECALL` with syscall ID in `a7`/`t0`, args in `a0`–`a2`, etc.), not
about the *function set or signatures*. SP1 ships its own list of
syscall IDs and accelerator argument shapes; the EVM-asm proofs
target the eth-act zkvm-standards function set described in
`zkvm_accelerators.h`. The two coexist:

- The dispatch *mechanism* (instruction encoding, register convention,
  return-via-`a0`) reuses SP1's RISC-V `ECALL` framing because it is
  the same mechanism every RISC-V zkVM uses; nothing in
  `zkvm_accelerators.h` constrains it.
- The *syscall ID table* — which integer in `a7`/`t0` selects which
  accelerator — is an implementation detail of the host zkVM, not of
  the C ABI. We track concrete IDs in the per-precompile bridge beads
  (parent `evm-asm-nr2sk`); a host that ships a different ID table
  remaps in its ECALL handler without affecting the verified guest.

In short: function set + argument layout + status framing come from
`zkvm_accelerators.h`; ECALL framing follows the RISC-V convention SP1
also uses; concrete syscall IDs are handler-side and tracked
separately.

## Coverage map

The header declares 19 entry points. Each one is (or will be) bridged by
a Lean payload type, a syscall-ID constant tying the ECALL handler to
the function, and a Hoare triple linking the RISC-V state transition to
the pure result. Per-function status is tracked in the children of
`evm-asm-nr2sk`.

Non-precompile accelerators:

| C symbol | Status |
|----------|--------|
| `zkvm_keccak256` | partial (input/result payload bridges in `EvmAsm/EL/KeccakInputBridge.lean`, `KeccakResultBridge.lean`); `zkvm_status` plumbing pending |
| `zkvm_secp256k1_verify` | not yet bridged |

Precompiles `0x01`–`0x11` and `0x100`:

| Precompile | Address | C symbol |
|------------|---------|----------|
| ECRECOVER | `0x01` | `zkvm_secp256k1_ecrecover` |
| SHA256 | `0x02` | `zkvm_sha256` |
| RIPEMD160 | `0x03` | `zkvm_ripemd160` |
| IDENTITY | `0x04` | (no accelerator — pure memcpy) |
| MODEXP | `0x05` | `zkvm_modexp` |
| BN254 G1 ADD | `0x06` | `zkvm_bn254_g1_add` |
| BN254 G1 MUL | `0x07` | `zkvm_bn254_g1_mul` |
| BN254 PAIRING | `0x08` | `zkvm_bn254_pairing` |
| BLAKE2F | `0x09` | `zkvm_blake2f` |
| KZG POINT EVAL | `0x0a` | `zkvm_kzg_point_eval` |
| BLS12 G1 ADD | `0x0b` | `zkvm_bls12_g1_add` |
| BLS12 G1 MSM | `0x0c` | `zkvm_bls12_g1_msm` |
| BLS12 G2 ADD | `0x0d` | `zkvm_bls12_g2_add` |
| BLS12 G2 MSM | `0x0e` | `zkvm_bls12_g2_msm` |
| BLS12 PAIRING | `0x0f` | `zkvm_bls12_pairing` |
| BLS12 MAP FP→G1 | `0x10` | `zkvm_bls12_map_fp_to_g1` |
| BLS12 MAP FP2→G2 | `0x11` | `zkvm_bls12_map_fp2_to_g2` |
| secp256r1 verify | `0x100` | `zkvm_secp256r1_verify` |

## Calling convention

The guest follows LP64 as documented in
[`EvmAsm/Evm64/CallingConvention.lean`](../EvmAsm/Evm64/CallingConvention.lean):
arguments in `a0`–`a2` (`x10`–`x12`), return value in `a0`, `sp` saved
by the callee, `ra` saved by the caller of non-leaf routines. Each
accelerator wrapper marshals its `zkvm_accelerators.h` arguments into
that register layout, issues an `ECALL`, and reads back the
`zkvm_status` from `a0`. Concrete bridges live (or will live) under
`EvmAsm/EL/` next to the existing keccak bridges.

## Maintenance

Update this ADR when:

- The vendored `zkvm_accelerators.h` is bumped (record the source
  commit).
- A bridge child of `evm-asm-nr2sk` lands and the coverage table above
  needs ticking.
- The decision itself is revisited (e.g. eth-act zkvm-standards is
  superseded).

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
