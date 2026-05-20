/-
  EvmAsm.Stateless.Transaction.RecoverSender

  Recover the sender's address from a transaction's signature.
  Mirrors Python's `recover_sender` from
  `forks/amsterdam/transactions.py`.

  ## Algorithm

  1. Compute the signing hash: `signing_hash = keccak256(rlp(tx
     without signature fields))`.
  2. Run ECRECOVER:
        pubkey = secp256k1_recover(signing_hash, sig.r, sig.s,
                                     recovery_id)
  3. Address derivation: `address = keccak256(pubkey)[12:32]`.

  ## Bridge dependencies

  Step 2 needs the secp256k1_ecrecover accelerator -- exposed
  via the zkvm-standards C interface as
  `zkvm_secp256k1_ecrecover(msg, sig, recid, output_pubkey)`. The
  bridge lands in PR-E1 (deferred); until then this Program
  routes to `Stateless.unimplemented_exit` with
  `REASON_TX_TYPE_UNSUPPORTED` (effectively making all real txs
  unverifiable, which is OK as long as fixtures use only txs that
  bypass sender recovery).

  Steps 1 and 3 are pure keccak — already available via
  `zkvm_keccak256` (PR-K3).

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Transaction.RecoverSender

-- TODO(stateless-tx): expose `recover_sender(tx_ptr, out_addr)`
-- once the ECRECOVER bridge lands.

end EvmAsm.Stateless.Transaction.RecoverSender
