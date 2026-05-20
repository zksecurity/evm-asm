/-
  EvmAsm.Stateless.Bridges.Sha256EcallBridge

  ECALL bridge for `zkvm_sha256` -- the SHA-256 hash needed for
  SSZ `hash_tree_root` computation.

  ## Why SHA-256 is needed

  `compute_new_payload_request_root` (in
  `forks/amsterdam/stateless.py`) takes the SSZ
  `hash_tree_root` of the `NewPayloadRequest`, which uses
  SHA-256 internally (per FIPS 180-4 / EIP-7251 SSZ spec). That
  root is stamped into the output `StatelessValidationResult`.

  (See `docs/execution-specs-feedback.md` #1 for the upstream
  discussion about whether the verifier really needs two
  cryptographic hashes -- keccak + SHA-256.)

  ## zkvm-standards C signature

      zkvm_status zkvm_sha256(const uint8_t* data, size_t len,
                              zkvm_sha256_hash* output);

  ## Syscall ID

  Per `EvmAsm/Evm64/Accelerators/SyscallIds.lean` -- TBD slot
  in the `0x100..` band reserved for non-precompile accelerators
  (currently keccak256 = 0x100, secp256k1_verify = 0x101,
  secp256k1_ecrecover = 0x102; SHA-256 will likely be 0x103 or
  higher).

  ## ziskemu intrinsic

  ziskemu exposes a compression intrinsic at `csrs 0x805, a0`
  per `ziskos/entrypoint/src/syscalls/syscall.rs::SYSCALL_SHA256F_ID`.
  Unlike Keccak's permutation (which is the **whole** sponge
  step), SHA-256 compression handles ONE 64-byte block; the
  Merkle-Damgaard wrapper has to live in the guest.

  PR-S1 attempted to pin the intrinsic encoding empirically but
  ran into a version mismatch -- the installed ziskemu (0.18.0)
  uses a different byte/word layout than the cached 0.15.0
  source. **Deferred until 0.18.0 source is available**.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Bridges.Sha256EcallBridge

-- TODO(stateless-bridges): expose `sha256_ecall(data, len,
-- output)` once the ziskemu 0.18.0 intrinsic layout is pinned.

end EvmAsm.Stateless.Bridges.Sha256EcallBridge
