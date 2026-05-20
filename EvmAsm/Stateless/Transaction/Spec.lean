/-
  EvmAsm.Stateless.Transaction.Spec

  Placeholder for cpsTriple specs over the Transaction subtree.

  Final form:

  - `decode_transaction_spec`  -- matches Python's
                                  `decode_transaction(bytes)`.
  - `validate_transaction_spec` -- accepts iff Python accepts.
  - `recover_sender_spec`      -- matches Python's
                                  `recover_sender(tx)`, including
                                  the ECRECOVER → keccak →
                                  address-suffix chain.
  - `process_transaction_spec` -- final (gas_used, success) +
                                  tx_state mutations match
                                  Python's `process_transaction`.

  TODO(stateless-proofs).
-/

namespace EvmAsm.Stateless.Transaction.Spec

-- TODO(stateless-proofs): cpsTripleWithin for the Transaction
-- subtree.

end EvmAsm.Stateless.Transaction.Spec
