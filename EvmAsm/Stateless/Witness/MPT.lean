/-
  EvmAsm.Stateless.Witness.MPT

  Umbrella for the Merkle Patricia Trie walker. Mirrors the Python
  `IncrementalMPT` (`forks/amsterdam/incremental_mpt.py`) for the
  read-side, and the per-method ops in the Python `WitnessState`
  for mutation (state-root recompute after applying a block).

  ## Subtree

  - `Decode.lean` — RLP-decode a single MPT node (extension /
                    branch / leaf). Branches at the top byte to
                    pick the variant.
  - `Walk.lean`   — drive an MPT lookup by traversing nibble paths.
                    Uses `NodeDb.Lookup` for hash chasing.
  - `Get.lean`    — `mpt_get(root, key) -> Option Bytes`. Composes
                    `Walk` and `Decode` to retrieve a single value.
  - `Set.lean`    — incremental `mpt_set(root, key, value) ->
                    new_root` (for state-root recompute after the
                    block's STF runs).
  - `Root.lean`   — `mpt_root(node_id) -> hash`. Re-hashes a
                    subtree after mutations.
  - `Spec.lean`   — cpsTriple placeholders.

  ## Reuse

  - `Stateless/Witness/NodeDb/Lookup.lean` for hash chasing.
  - `Rv64/RLP/Phase1..3` for primitive RLP decode.
  - `Stateless/Headers/BlockHash.lean` (or directly the keccak
    bridge) for re-hashing after mutation.

  All sub-files are scaffolds in PR-K9.
-/

import EvmAsm.Stateless.Witness.MPT.Decode
import EvmAsm.Stateless.Witness.MPT.Walk
import EvmAsm.Stateless.Witness.MPT.Get
import EvmAsm.Stateless.Witness.MPT.Set
import EvmAsm.Stateless.Witness.MPT.Root
import EvmAsm.Stateless.Witness.MPT.Spec
