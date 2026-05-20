/-
  EvmAsm.Stateless.Block.ApplyBody

  Apply a block's transaction list + system txs + withdrawals to
  a BlockState. Mirrors Python's `apply_body` from
  `forks/amsterdam/fork.py`.

  ## Algorithm (simplified)

      def apply_body(block, block_state, chain_context):
          # 1. System transactions (deposits, withdrawals, etc.)
          process_system_transactions(block, block_state)

          # 2. Per-tx loop
          gas_used = 0
          for i, encoded_tx in enumerate(block.transactions):
              tx = decode_transaction(encoded_tx)
              sender = recover_sender(tx)
              validate_transaction(tx, sender, block_state)
              tx_state = TransactionState(block_state)
              result = process_transaction(tx, sender, tx_state)
              gas_used += result.gas_used
              if result.success:
                  block_state.commit(tx_state)
              else:
                  block_state.revert(tx_state)
              block_state.pay_priority_fee(tx.gas_tip * result.gas_used,
                                            block.header.coinbase)
          assert gas_used <= block.header.gas_limit

          # 3. Withdrawal credits
          for w in block.withdrawals:
              block_state.add_balance(w.address, w.amount * 1e9)

  ## RISC-V plan

  Big per-tx loop. Each iteration:
  - `Transaction.Decode` to lift the RLP-encoded tx into a struct.
  - `Transaction.RecoverSender` (uses ECRECOVER via the
    zkvm-standards bridge once that lands -- currently
    Unimplemented).
  - `Transaction.Validate` for nonce / balance / gas checks.
  - `Transaction.Process` for the actual STF.

  Withdrawals are simpler: pure balance increments, no EVM
  execution.

  ## PR-K11 status

  Scaffold only. The most complex piece of the block subtree;
  multiple follow-up PRs will implement the per-tx loop and
  the system-tx variants.
-/

namespace EvmAsm.Stateless.Block.ApplyBody

-- TODO(stateless-block): expose `apply_body` Program iterating
-- over `block.transactions`, applying each via the Transaction
-- subtree, plus withdrawal credits and system txs.

end EvmAsm.Stateless.Block.ApplyBody
