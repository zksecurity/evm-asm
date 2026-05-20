/-
  EvmAsm.Stateless.ExecutionEngine.NewPayload

  Validate + execute a `NewPayloadRequest` against the pre-state.
  Mirrors Python's `execute_new_payload_request` in
  `forks/amsterdam/execution_engine/new_payload.py`.

  ## Algorithm

      def execute_new_payload_request(request, pre_state,
                                       chain_context):
          # 1. Block-hash check: keccak256(payload_header) ==
          #    request.execution_payload_header.block_hash
          assert _verify_block_hash(request)
          # 2. Versioned-hash check (EIP-4844 blob commitments)
          assert _verify_versioned_hashes(request)
          # 3. Convert NewPayloadRequest -> Block
          block = new_payload_request_to_block(request)
          # 4. Hand off to fork.execute_block
          execute_block(block, pre_state, chain_context)

  ## RISC-V plan

  Compose:
  - `Stateless.Headers.BlockHash` to recompute the payload header
    hash and compare.
  - `Stateless.ExecutionEngine.Requests` to lift the requests
    field.
  - `Stateless.Block.Execute` to run the actual block.

  EIP-4844 versioned-hash checks need KZG (precompile-scoped);
  in PR-K12 / early PRs this routes to `unimplemented_exit` with
  `REASON_EIP4844_BLOB`.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.ExecutionEngine.NewPayload

-- TODO(stateless-engine): expose `execute_new_payload_request`
-- driver.

end EvmAsm.Stateless.ExecutionEngine.NewPayload
