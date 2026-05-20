/-
  EvmAsm.Stateless.Witness.NodeDb

  Umbrella for the trie-node lookup table. Mirrors Python's
  `build_node_db` from `forks/amsterdam/witness_state.py`:

      def build_node_db(state):
          return {keccak256(node_bytes): node_bytes for node_bytes in state}

  ## Subtree

  - `Program.lean`  — iterate over `witness.state`, keccak each
                      element via `zkvm_keccak256`, write a
                      `(hash, range)` entry into the lookup table at
                      `NODE_DB_BUCKETS`.
  - `Lookup.lean`   — `nodeDb.get(hash) -> (ptr, len)` lookup. Uses
                      a flat hash-bucket scheme (capacity 2^20 per
                      `MAX_WITNESS_NODES = 2^20`).
  - `Spec.lean`     — cpsTriple placeholders.
-/

import EvmAsm.Stateless.Witness.NodeDb.Program
import EvmAsm.Stateless.Witness.NodeDb.Lookup
import EvmAsm.Stateless.Witness.NodeDb.Spec
