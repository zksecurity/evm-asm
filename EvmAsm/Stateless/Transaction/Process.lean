/-
  EvmAsm.Stateless.Transaction.Process

  Process a validated transaction against a tx_state. Mirrors
  Python's `process_transaction` from `forks/amsterdam/fork.py`.

  ## Algorithm

  1. Deduct upfront cost from sender:
       sender.balance -= tx.gas_limit * gas_price
       sender.nonce += 1
  2. Calculate gas left = tx.gas_limit - intrinsic_gas
  3. Execute the message:
       result = execute_message(
           Message(caller=sender, target=tx.to, value=tx.value,
                   data=tx.data, gas=gas_left, ...),
           tx_state)
  4. Refund unused gas + EIP-3529 gas refund cap.
  5. Pay priority fee to coinbase:
       coinbase.balance += priority_fee_per_gas * gas_used
  6. Burn base fee:
       (already deducted upfront, not refunded)

  Returns `(gas_used, success: bool)`.

  ## Reuse

  - `Stateless.VM.Interpreter.execute_message` is the actual EVM
    interpreter loop (scaffolded in PR-K12).
  - `Stateless.State.BlockState` for balance/nonce updates.

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Transaction.Process

-- TODO(stateless-tx): expose `process_transaction(tx, sender,
-- tx_state) -> (gas_used, success)` Program.

end EvmAsm.Stateless.Transaction.Process
