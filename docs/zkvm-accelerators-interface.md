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

## Coverage audit table

The header declares 19 entry points. Each one is (or will be) bridged by
a Lean payload type, a syscall-ID constant tying the ECALL handler to
the function, and a Hoare triple linking the RISC-V state transition to
the pure result. Per-function status is tracked in the children of
`evm-asm-nr2sk`.

Selector constants live in
`EvmAsm/Evm64/Accelerators/SyscallIds.lean` as both `Nat` IDs under
`EvmAsm.Accelerators.SyscallId` and RV64 words under
`EvmAsm.Rv64.SyscallIdWord`; the `allSelectors_pairwiseDistinct` and
`accelerator_ids_in_range` theorems pin the table mechanically.

| Surface | C symbol | Selector | Lean payload bridge | ECALL / execution bridge status |
|---------|----------|----------|---------------------|---------------------------------|
| KECCAK256 opcode | `zkvm_keccak256` | `keccak256` / `0x100` | `EvmAsm/EL/KeccakInputBridge.lean`, `EvmAsm/EL/KeccakResultBridge.lean` | `EvmAsm/EL/KeccakEcallBridge.lean`, `EvmAsm/EL/KeccakExecutionBridge.lean`, `EvmAsm/EL/KeccakStackBridge.lean`, `EvmAsm/EL/KeccakStackExecutionBridge.lean` |
| secp256k1 signature verify | `zkvm_secp256k1_verify` | `secp256k1_verify` / `0x101` | `EvmAsm/EL/Secp256k1VerifyInputBridge.lean`, `EvmAsm/EL/Secp256k1VerifyResultBridge.lean` | `EvmAsm/EL/Secp256k1VerifyEcallBridge.lean` |
| ECRECOVER `0x01` | `zkvm_secp256k1_ecrecover` | `secp256k1_ecrecover` / `0x102` | `EvmAsm/EL/Secp256k1EcrecoverInputBridge.lean`, `EvmAsm/EL/Secp256k1EcrecoverResultBridge.lean` | `EvmAsm/EL/Secp256k1EcrecoverEcallBridge.lean` |
| SHA256 `0x02` | `zkvm_sha256` | `sha256` / `0x103` | `EvmAsm/EL/Sha256InputBridge.lean`, `EvmAsm/EL/Sha256ResultBridge.lean` | `EvmAsm/EL/Sha256EcallBridge.lean` |
| RIPEMD160 `0x03` | `zkvm_ripemd160` | `ripemd160` / `0x104` | `EvmAsm/EL/Ripemd160InputBridge.lean`, `EvmAsm/EL/Ripemd160ResultBridge.lean` | `EvmAsm/EL/Ripemd160EcallBridge.lean` |
| IDENTITY `0x04` | none | none | pure memory copy path, no accelerator payload | not applicable |
| MODEXP `0x05` | `zkvm_modexp` | `modexp` / `0x105` | `EvmAsm/EL/ModexpInputBridge.lean`, `EvmAsm/EL/ModexpResultBridge.lean` | `EvmAsm/EL/ModexpEcallBridge.lean` |
| BN254 G1 ADD `0x06` | `zkvm_bn254_g1_add` | `bn254_g1_add` / `0x106` | `EvmAsm/EL/Bn254G1AddInputBridge.lean`, `EvmAsm/EL/Bn254G1AddResultBridge.lean` | `EvmAsm/EL/Bn254G1AddEcallBridge.lean` |
| BN254 G1 MUL `0x07` | `zkvm_bn254_g1_mul` | `bn254_g1_mul` / `0x107` | `EvmAsm/EL/Bn254G1MulInputBridge.lean`, `EvmAsm/EL/Bn254G1MulResultBridge.lean` | `EvmAsm/EL/Bn254G1MulEcallBridge.lean` |
| BN254 PAIRING `0x08` | `zkvm_bn254_pairing` | `bn254_pairing` / `0x108` | `EvmAsm/EL/Bn254PairingInputBridge.lean`, `EvmAsm/EL/Bn254PairingResultBridge.lean` | `EvmAsm/EL/Bn254PairingEcallBridge.lean` |
| BLAKE2F `0x09` | `zkvm_blake2f` | `blake2f` / `0x109` | `EvmAsm/EL/Blake2fInputBridge.lean`, `EvmAsm/EL/Blake2fResultBridge.lean` | `EvmAsm/EL/Blake2fEcallBridge.lean` |
| KZG POINT EVAL `0x0a` | `zkvm_kzg_point_eval` | `kzg_point_eval` / `0x10a` | `EvmAsm/EL/KzgPointEvalInputBridge.lean`, `EvmAsm/EL/KzgPointEvalResultBridge.lean` | `EvmAsm/EL/KzgPointEvalEcallBridge.lean` |
| BLS12 G1 ADD `0x0b` | `zkvm_bls12_g1_add` | `bls12_g1_add` / `0x10b` | `EvmAsm/EL/Bls12G1AddInputBridge.lean`, `EvmAsm/EL/Bls12G1AddResultBridge.lean` | `EvmAsm/EL/Bls12G1AddEcallBridge.lean` |
| BLS12 G1 MSM `0x0c` | `zkvm_bls12_g1_msm` | `bls12_g1_msm` / `0x10c` | `EvmAsm/EL/Bls12G1MsmInputBridge.lean`, `EvmAsm/EL/Bls12G1MsmResultBridge.lean` | `EvmAsm/EL/Bls12G1MsmEcallBridge.lean` |
| BLS12 G2 ADD `0x0d` | `zkvm_bls12_g2_add` | `bls12_g2_add` / `0x10d` | `EvmAsm/EL/Bls12G2AddInputBridge.lean`, `EvmAsm/EL/Bls12G2AddResultBridge.lean` | `EvmAsm/EL/Bls12G2AddEcallBridge.lean` |
| BLS12 G2 MSM `0x0e` | `zkvm_bls12_g2_msm` | `bls12_g2_msm` / `0x10e` | `EvmAsm/EL/Bls12G2MsmInputBridge.lean`, `EvmAsm/EL/Bls12G2MsmResultBridge.lean` | `EvmAsm/EL/Bls12G2MsmEcallBridge.lean` |
| BLS12 PAIRING `0x0f` | `zkvm_bls12_pairing` | `bls12_pairing` / `0x10f` | `EvmAsm/EL/Bls12PairingInputBridge.lean`, `EvmAsm/EL/Bls12PairingResultBridge.lean` | `EvmAsm/EL/Bls12PairingEcallBridge.lean` |
| BLS12 MAP FP TO G1 `0x10` | `zkvm_bls12_map_fp_to_g1` | `bls12_map_fp_to_g1` / `0x110` | `EvmAsm/EL/Bls12MapFpToG1InputBridge.lean`, `EvmAsm/EL/Bls12MapFpToG1ResultBridge.lean` | `EvmAsm/EL/Bls12MapFpToG1EcallBridge.lean` |
| BLS12 MAP FP2 TO G2 `0x11` | `zkvm_bls12_map_fp2_to_g2` | `bls12_map_fp2_to_g2` / `0x111` | `EvmAsm/EL/Bls12MapFp2ToG2InputBridge.lean`, `EvmAsm/EL/Bls12MapFp2ToG2ResultBridge.lean` | `EvmAsm/EL/Bls12MapFp2ToG2EcallBridge.lean` |
| secp256r1 verify `0x100` | `zkvm_secp256r1_verify` | `secp256r1_verify` / `0x112` | `EvmAsm/EL/Secp256r1VerifyInputBridge.lean`, `EvmAsm/EL/Secp256r1VerifyResultBridge.lean` | `EvmAsm/EL/Secp256r1VerifyEcallBridge.lean` |

The table is intentionally path-based: if a bridge module is renamed or split,
this audit should be updated in the same PR so downstream readers can trace
from the C symbol to the Lean payload and ECALL surface.

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
