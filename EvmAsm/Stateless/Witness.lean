/-
  EvmAsm.Stateless.Witness

  Umbrella for the witness-state subtree of the stateless guest.
  Implements the Python-side `WitnessState` from
  `execution-specs/src/ethereum/forks/amsterdam/witness_state.py`:

      class WitnessState:
          _node_db   : dict[Bytes32, Bytes]     # keccak hash -> MPT node bytes
          _state_root: Root
          _code_db   : dict[Bytes32, Bytes]     # keccak hash -> contract code

  Construction (host-side):

      pre_state = WitnessState(
          _node_db   = build_node_db(witness.state),
          _state_root = parent_header.state_root,
          _code_db   = build_code_db(witness.codes),
      )

  ## Subtree

  - `NodeDb/`  — keccak each entry of `witness.state` and store
                 `(hash, byte_range)` in a hash table indexed by
                 keccak. The MPT walker uses this table to chase
                 references during account/storage lookups.
  - `CodeDb/`  — same shape, for `witness.codes`. Lookups happen
                 during EXTCODE* opcodes and at the contract-code
                 fetch step of CALL/CREATE.
  - `MPT/`     — nibble walk over the witness-backed Merkle Patricia
                 Trie. Routes leaf/extension/branch nodes via the
                 node_db lookup.

  All sub-files are scaffolds in PR-K9: doc + namespace only. The
  Programs land in follow-up PRs once the keccak bridge (PR-K3..K7)
  is reusable from inside the Stateless tree.
-/

import EvmAsm.Stateless.Witness.NodeDb
import EvmAsm.Stateless.Witness.CodeDb
import EvmAsm.Stateless.Witness.MPT
