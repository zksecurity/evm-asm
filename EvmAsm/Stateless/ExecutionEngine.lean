/-
  EvmAsm.Stateless.ExecutionEngine

  Umbrella for the consensus-layer `NewPayloadRequest` handling.
  Mirrors `forks/amsterdam/execution_engine/`:

  - `new_payload.py`  -- `execute_new_payload_request`: validates
                         the block-hash + versioned hashes, then
                         hands off to `fork.execute_block`.
  - `requests.py`     -- `ExecutionRequests` RLP/SSZ glue
                         (deposits, withdrawals, consolidations).
  - `types.py`        -- `NewPayloadRequest`, `ExecutionPayload`,
                         `ExecutionPayloadHeader` records.

  ## Top-level flow

  `Stateless.Entry.run_stateless_guest` will call:
  1. `Stateless.SSZ.Decode.deserialize_stateless_input` (already
     scaffolded).
  2. `Stateless.Headers.Validate.validate_headers`.
  3. `Stateless.Witness.{NodeDb, CodeDb}.build_db` (already
     scaffolded).
  4. `Stateless.ExecutionEngine.NewPayload.execute_new_payload_request`
     (this subtree).
  5. `Stateless.SSZ.Encode.serialize_stateless_output` (already
     wired).

  ## Subtree

  - `NewPayload.lean`   — `execute_new_payload_request` entry point.
                          Calls `Block.Execute` after a few
                          consensus-level checks.
  - `Requests.lean`     — `ExecutionRequests` decode (deposits,
                          withdrawals, consolidations RLP/SSZ shape).
  - `Spec.lean`         — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K12.
-/

import EvmAsm.Stateless.ExecutionEngine.NewPayload
import EvmAsm.Stateless.ExecutionEngine.Requests
import EvmAsm.Stateless.ExecutionEngine.Spec
