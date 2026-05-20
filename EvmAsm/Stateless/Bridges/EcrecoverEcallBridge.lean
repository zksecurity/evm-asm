/-
  EvmAsm.Stateless.Bridges.EcrecoverEcallBridge

  ECALL bridge for `zkvm_secp256k1_ecrecover` -- secp256k1
  signature recovery. Used by `Stateless.Transaction.RecoverSender`
  to derive the sender's public key (and then address) from a
  transaction's signature.

  ## zkvm-standards C signature

      zkvm_status zkvm_secp256k1_ecrecover(
          const zkvm_secp256k1_hash* msg,        // 32B message digest
          const zkvm_secp256k1_signature* sig,   // 64B (r || s)
          uint8_t recid,                          // 0 or 1
          zkvm_secp256k1_pubkey* output);         // 64B uncompressed pubkey

  ## Syscall ID

  Pinned at `0x102` per `EvmAsm/Evm64/Accelerators/SyscallIds.lean`
  (the host-side ID for secp256k1_ecrecover).

  ## Verified-side ECALL

  Same shape as Keccak:
  - t0 = SYSCALL_ECRECOVER_ID (0x102)
  - a0 = msg ptr
  - a1 = sig ptr
  - a2 = recid (low byte)
  - a3 = output_pubkey ptr
  - returns a0 = ZKVM_EOK on success

  ## ziskemu execution side

  Once the ziskemu intrinsic for secp256k1_ecrecover is pinned
  (analogous to PR-K1 for keccak), the codegen emits the
  equivalent `csrs <csr>, a0` instruction in place of the ECALL.
  Until then, calls route to `unimplemented_exit`.

  ## PR-K12 status

  Scaffold only -- doc + namespace + TODO.
-/

namespace EvmAsm.Stateless.Bridges.EcrecoverEcallBridge

-- TODO(stateless-bridges): expose `ecrecover_ecall(msg, sig,
-- recid, output)` matching the zkvm-standards C signature.

end EvmAsm.Stateless.Bridges.EcrecoverEcallBridge
