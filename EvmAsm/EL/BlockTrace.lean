/-
  EvmAsm.EL.BlockTrace

  Generic trace-cardinality facts for the block transition fold (GH #124).
-/

import EvmAsm.EL.Block

namespace EvmAsm.EL

namespace BlockTrace

open BlockTransition

/-- `applyTransaction` appends exactly one trace item to the accumulator.
    Distinctive token: BlockTrace.transactionResults_length #124. -/
theorem applyTransaction_transactionResults_length
    (executor : TransactionExecutor) (acc : BlockAccumulator) (tx : Transaction) :
    (applyTransaction executor acc tx).transactionResults.length =
      acc.transactionResults.length + 1 := by
  cases h_frame : tx.toCallFrame? with
  | none =>
      simp [applyTransaction, h_frame]
  | some frame =>
      simp [applyTransaction, h_frame]

/-- Folding a list of transactions appends one trace item for every
    transaction, preserving the existing accumulator prefix. -/
theorem applyTransactions_transactionResults_length
    (executor : TransactionExecutor) (acc : BlockAccumulator) (txs : List Transaction) :
    (applyTransactions executor acc txs).transactionResults.length =
      acc.transactionResults.length + txs.length := by
  induction txs generalizing acc with
  | nil =>
      simp [applyTransactions]
  | cons tx txs ih =>
      rw [applyTransactions_cons, ih]
      rw [applyTransaction_transactionResults_length]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The block transition emits exactly one transaction-result trace item per
    input transaction. -/
theorem run_transactionResults_length
    (executor : TransactionExecutor) (input : BlockInput) :
    (run executor input).transactionResults.length =
      input.transactions.length := by
  simp [run, initialAccumulator, applyTransactions_transactionResults_length]

/-- Empty blocks emit an empty transaction-result trace. -/
theorem run_nil_transactionResults
    (executor : TransactionExecutor) (input : BlockInput)
    (h_txs : input.transactions = []) :
    (run executor input).transactionResults = [] := by
  simp [run, initialAccumulator, applyTransactions, h_txs]

end BlockTrace

end EvmAsm.EL
