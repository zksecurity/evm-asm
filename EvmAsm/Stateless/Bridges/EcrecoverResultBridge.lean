/-
  EvmAsm.Stateless.Bridges.EcrecoverResultBridge

  Read the ECRECOVER output. The host writes 64 bytes of
  uncompressed public key (x || y, big-endian) at the output
  pointer. The caller (`Stateless.Transaction.RecoverSender`)
  then keccak-hashes those 64 bytes and takes the last 20 bytes
  as the address.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Bridges.EcrecoverResultBridge

-- TODO(stateless-bridges): expose helpers to read the 64-byte
-- pubkey + the ZKVM_EOK / ZKVM_EFAIL status from the ECALL
-- output region.

end EvmAsm.Stateless.Bridges.EcrecoverResultBridge
