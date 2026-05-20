/-
  EvmAsm.Stateless.Block

  Umbrella for the block-level STF subtree. Mirrors the Python
  block executor from `forks/amsterdam/fork.py:execute_block` and
  `apply_body`.

  ## Top-level flow

      def execute_block(block, pre_state, chain_context):
          validate_header(block.header, chain_context)
          block_state = BlockState(pre_state)
          apply_body(block, block_state, chain_context)
          new_state_root =
              compute_state_root_and_trie_changes(pre_state, block_state.diff)
          assert new_state_root == block.header.state_root, \
                 "state root mismatch"

  ## Subtree

  - `Execute.lean`         — top-level `execute_block`. Wires
                             ValidateHeader + ApplyBody + StateRoot.
  - `ApplyBody.lean`       — per-tx loop, system txs, withdrawals.
  - `ValidateHeader.lean`  — gas limit, timestamp, base-fee, etc.
                             checks against parent header.
  - `Spec.lean`            — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K11.
-/

import EvmAsm.Stateless.Block.Execute
import EvmAsm.Stateless.Block.ApplyBody
import EvmAsm.Stateless.Block.ValidateHeader
import EvmAsm.Stateless.Block.Spec
