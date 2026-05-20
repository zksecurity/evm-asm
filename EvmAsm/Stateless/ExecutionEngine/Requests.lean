/-
  EvmAsm.Stateless.ExecutionEngine.Requests

  Decode the `ExecutionRequests` field of a `NewPayloadRequest`.
  Mirrors Python's `forks/amsterdam/execution_engine/requests.py`.

  ## Shape

      class ExecutionRequests:
          deposits       : list[DepositRequest]
          withdrawals    : list[WithdrawalRequest]
          consolidations : list[ConsolidationRequest]

  Each is RLP-encoded per its EIP (EIP-6110 deposits, EIP-7002
  withdrawals, EIP-7251 consolidations). The amsterdam fork
  defers most details to the previous fork (bpo5).

  ## RISC-V plan

  Lift each list into a flat in-memory record per request type.
  For PR-K12, the placeholder routes to `unimplemented_exit`
  if any request list is non-empty -- handling per-request
  semantics is significant new logic (cross-cutting with
  signature recovery for deposits, balance bookkeeping for
  withdrawals).

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.ExecutionEngine.Requests

-- TODO(stateless-engine): expose `decode_execution_requests` +
-- per-type handlers (deposits, withdrawals, consolidations).

end EvmAsm.Stateless.ExecutionEngine.Requests
