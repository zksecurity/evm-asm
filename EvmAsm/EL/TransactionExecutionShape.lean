/-
  EvmAsm.EL.TransactionExecutionShape

  Generic option-shape facts for transaction execution (GH #122).
-/

import EvmAsm.EL.TransactionExecution

namespace EvmAsm.EL

namespace TransactionExecutionShape

open TransactionExecution

/-- `execute?` returns a result exactly for message-call transactions.
    Distinctive token: TransactionExecutionShape.execute?_isSome_iff #122. -/
theorem execute?_isSome_iff
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput) :
    (execute? executor input).isSome ↔ input.tx.to.isSome := by
  cases h_to : input.tx.to with
  | none =>
      simp [execute?, Transaction.toCallFrame?_create input.tx h_to]
  | some callee =>
      simp [execute?, Transaction.toCallFrame?_some input.tx h_to]

/-- `execute?` is absent exactly for contract-creation transactions, which are
    handled by the CREATE/CREATE2 layer. -/
theorem execute?_eq_none_iff
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput) :
    execute? executor input = none ↔ input.tx.to = none := by
  cases h_to : input.tx.to with
  | none =>
      simp [execute?, Transaction.toCallFrame?_create input.tx h_to]
  | some callee =>
      simp [execute?, Transaction.toCallFrame?_some input.tx h_to]

/-- Message-call transactions always produce a transaction execution result. -/
theorem execute?_isSome_of_call
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput)
    {callee : Address} (h_to : input.tx.to = some callee) :
    (execute? executor input).isSome := by
  exact (execute?_isSome_iff executor input).2 (by simp [h_to])

/-- Contract-creation transactions are deferred from this ordinary-call
    execution hook. -/
theorem execute?_isNone_of_create
    (executor : MessageCallExecution.CallExecutor) (input : TransactionExecutionInput)
    (h_to : input.tx.to = none) :
    (execute? executor input).isNone := by
  rw [Option.isNone_iff_eq_none]
  exact (execute?_eq_none_iff executor input).2 h_to

end TransactionExecutionShape

end EvmAsm.EL
