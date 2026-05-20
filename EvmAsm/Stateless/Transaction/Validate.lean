/-
  EvmAsm.Stateless.Transaction.Validate

  Pre-execution validation. Mirrors Python's
  `validate_transaction` from `forks/amsterdam/fork.py`.

  ## Checks

  - **Chain ID**: `tx.chain_id == chain_config.chain_id` (only
    for typed txs with a chain_id field).
  - **Nonce**: `tx.nonce == sender_account.nonce`.
  - **Gas price**: `tx.gas_price >= base_fee_per_gas` for legacy;
    `tx.max_fee_per_gas >= base_fee` and
    `tx.max_priority_fee_per_gas <= tx.max_fee_per_gas` for
    EIP-1559+.
  - **Up-front cost**: `sender.balance >= tx.gas_limit *
    tx.gas_price + tx.value`.
  - **Intrinsic gas**: `tx.gas_limit >= intrinsic_gas(tx.data,
    tx.access_list, tx.create)`. Intrinsic gas is per the
    Berlin/Bedlam schedule plus EIP-3860 init-code length.
  - **Blob constraints** (EIP-4844): `len(tx.blob_hashes) <=
    MAX_BLOB_GAS_PER_TX / GAS_PER_BLOB`, etc. → routes to
    Unimplemented while EIP-4844 is out of scope.

  Failure routes to `unimplemented_exit` with a tx-specific
  reason code (could be split: `REASON_TX_NONCE`,
  `REASON_TX_BALANCE`, etc., or kept as a single
  `REASON_TX_INVALID` covering all).

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Transaction.Validate

-- TODO(stateless-tx): expose `validate_transaction(tx, sender,
-- block_state)` Program.

end EvmAsm.Stateless.Transaction.Validate
