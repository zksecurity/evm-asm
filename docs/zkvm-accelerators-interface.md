# Accelerator C Interface — design note

Status: accepted (2026-05-06)
Refs: GH discussion in beads `evm-asm-y4o09`, audit tracker `evm-asm-nr2sk`.

## Decision

EvmAsm targets **`zkvm_accelerators.h`** (from the `zkvm-standards` repository, vendored
at `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`)
as the canonical accelerator C ABI for cryptographic precompiles, KECCAK256, and
secp256k1 signature verification.

The host (zkVM prover / runtime) is expected to satisfy the contracts of the
functions declared in that header. The verified RISC-V code uses ECALL to
delegate to those functions; the post-state of each ECALL is specified to match
the C-level postcondition of the corresponding `zkvm_*` function.

## Why a design note?

`README.md` previously stated only that the ECALL syscall mechanism "follows
SP1's conventions." That is true at the *transport* layer (syscall numbering,
register convention) but said nothing about the *semantic* layer (which crypto
functions, with what argument shapes, with what error codes). This document
fixes the gap: SP1 conventions handle how an ECALL is dispatched, while
`zkvm_accelerators.h` defines what each accelerator computes.

## SP1 vs. zkvm_accelerators — what each layer fixes

Layer 1 — syscall transport (SP1):
- `ECALL` with `t0 = id` triggers a syscall.
- Argument registers `a0..a2` carry pointers / counts (LP64 calling
  convention; see `EvmAsm/Evm64/CallingConvention.lean`).
- Reserved IDs in this codebase:
    - `t0 = 0x00` — HALT
    - `t0 = 0x10` — COMMIT (append `(a0, a1)` to committed outputs)
    - `t0 = 0xF0` — HINT_LEN (read `privateInput.length` into `a0`)
    - `t0 = 0xF1` — HINT_READ (read bytes from `privateInput` into memory)
- See `EvmAsm/Rv64/Execution.lean` (HALT/COMMIT/HINT_LEN/HINT_READ) and
  `EvmAsm/Rv64/HintSpecs.lean`.

Layer 2 — accelerator semantics (`zkvm_accelerators.h`):
- One C entry point per accelerated primitive.
- All return `zkvm_status` (see `zkvm_status` enum in the header,
  `ZKVM_EOK = 0`).
- Inputs are byte buffers / fixed-width structs (`zkvm_bytes_32`,
  `zkvm_bn254_g1_point`, …); outputs are written through caller-supplied
  pointers.

The two layers are orthogonal: SP1 fixes the *how* of crossing the host/guest
boundary, `zkvm_accelerators.h` fixes the *what* on the host side. The syscall
ID for each accelerator is part of the bridge work tracked by
`evm-asm-nr2sk` — assignments are not yet final and will be added to the
ECALL dispatch in `EvmAsm/Rv64/Execution.lean` as each bridge lands.

## Mapping from EVM precompiles to accelerator functions

| EVM addr | EVM name           | `zkvm_accelerators.h` symbol           |
|---------:|--------------------|-----------------------------------------|
| 0x01     | ECRECOVER          | `zkvm_secp256k1_ecrecover`              |
| 0x02     | SHA256             | `zkvm_sha256`                           |
| 0x03     | RIPEMD160          | `zkvm_ripemd160`                        |
| 0x04     | IDENTITY           | (no accelerator — pure memory copy)     |
| 0x05     | MODEXP             | `zkvm_modexp`                           |
| 0x06     | BN254_ADD          | `zkvm_bn254_g1_add`                     |
| 0x07     | BN254_MUL          | `zkvm_bn254_g1_mul`                     |
| 0x08     | BN254_PAIRING      | `zkvm_bn254_pairing`                    |
| 0x09     | BLAKE2F            | `zkvm_blake2f`                          |
| 0x0a     | KZG_POINT_EVAL     | `zkvm_kzg_point_eval`                   |
| 0x0b     | BLS12_G1_ADD       | `zkvm_bls12_g1_add`                     |
| 0x0c     | BLS12_G1_MSM       | `zkvm_bls12_g1_msm`                     |
| 0x0d     | BLS12_G2_ADD       | `zkvm_bls12_g2_add`                     |
| 0x0e     | BLS12_G2_MSM       | `zkvm_bls12_g2_msm`                     |
| 0x0f     | BLS12_PAIRING      | `zkvm_bls12_pairing`                    |
| 0x10     | BLS12_MAP_FP_TO_G1 | `zkvm_bls12_map_fp_to_g1`               |
| 0x11     | BLS12_MAP_FP2_TO_G2| `zkvm_bls12_map_fp2_to_g2`              |
| 0x100    | secp256r1_verify   | `zkvm_secp256r1_verify`                 |

Non-precompile accelerators reused by EVM opcode handlers:

| Use site            | `zkvm_accelerators.h` symbol     |
|---------------------|-----------------------------------|
| KECCAK256 opcode    | `zkvm_keccak256`                  |
| ECRECOVER auxiliary | `zkvm_secp256k1_verify` (optional) |

## Calling convention for accelerator ECALLs

All accelerator ECALLs use the LP64 calling convention defined in
`EvmAsm/Evm64/CallingConvention.lean`. By analogy with the C signature, the
guest:

1. Places input pointers / lengths in `a0..a2` (extending to `a3..a5` for
   accelerators with more arguments — concrete bindings are part of each
   bridge slice).
2. Sets `t0` to the syscall ID assigned to that accelerator.
3. Issues `ECALL`.
4. Reads the output through the caller-supplied output pointer; the host
   writes `zkvm_status` to a designated register (`a0` by current convention,
   to be confirmed per bridge).

Output-buffer ownership and validity follow standard separation-logic frame
discipline: the bridge spec asserts `memBufferIs out_ptr (replicate len 0)`
in the precondition and yields `memBufferIs out_ptr <hash bytes>` in the
postcondition, exactly as the existing KECCAK bridge in
`EvmAsm/EL/KeccakInputBridge.lean` and `EvmAsm/EL/KeccakResultBridge.lean`
does.

## Where this lands in the proof stack

- `Rv64/Execution.lean` defines the ECALL handler dispatch table; per-syscall
  cases (HALT, COMMIT, HINT_LEN, HINT_READ today) will gain accelerator IDs
  as bridges land.
- `EvmAsm/EL/Keccak*Bridge.lean` is the canonical example shape: payload
  type matching the C struct, plus a Hoare triple linking the RISC-V state
  transition to the pure result.
- `evm-asm-nr2sk` tracks the per-function bridge audit (Lean payload types,
  syscall ID, bridge spec, status).

## References

- Header: `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
- zkvm-standards repo: https://github.com/eth-act/zkvm-standards
- SP1 zkVM (transport-layer source): https://github.com/succinctlabs/sp1
- LP64 calling convention: `EvmAsm/Evm64/CallingConvention.lean`
- KECCAK bridge precedent: `EvmAsm/EL/KeccakInputBridge.lean`,
  `EvmAsm/EL/KeccakResultBridge.lean`
