/-
  EvmAsm.Stateless.Block.Execute

  Top-level `execute_block` driver. Composes the pieces of the
  block-level STF.

  ## Algorithm (Python `fork.py:execute_block`)

      def execute_block(block, pre_state, chain_context):
          validate_header(block.header, chain_context)
          block_state = BlockState(pre_state)
          apply_body(block, block_state, chain_context)
          new_root = compute_state_root_and_trie_changes(
                         pre_state, block_state.diff)
          if new_root != block.header.state_root:
              raise InvalidBlock("state root mismatch")

  ## RISC-V plan

  Compose subprograms in order:
  1. `Block.ValidateHeader.validate(header_ptr, chain_ctx)`.
  2. `BlockState.init(pre_state) -> block_state_addr`.
  3. `Block.ApplyBody.apply(block, block_state, chain_ctx)`.
  4. `State.StateRoot.compute(pre_state, block_state.diff) -> new_root`.
  5. memcmp(new_root, header.state_root, 32). On mismatch route
     to `unimplemented_exit` with `REASON_STATE_ROOT_MISMATCH`.

  Output: returns successfully iff all steps pass; otherwise the
  state-root check raises an Unimplemented or the inner functions
  do.

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Block.Execute

-- TODO(stateless-block): expose `execute_block(block_addr,
-- pre_state_addr, chain_ctx_addr)` Program. Composes the four
-- subprograms above.

end EvmAsm.Stateless.Block.Execute
