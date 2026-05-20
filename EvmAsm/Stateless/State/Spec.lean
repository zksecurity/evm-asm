/-
  EvmAsm.Stateless.State.Spec

  Placeholder for cpsTriple specs over the State subtree.

  Final form:

  - `decode_account_spec`  -- RLP bytes that round-trip through
                              Account's encode/decode match the
                              Python reference's
                              `rlp.decode_to(Account, bytes)`.
  - `pre_state_get_*_spec` -- read paths produce the same value
                              the Python `WitnessState` would
                              for the same inputs.
  - `block_state_*_spec`   -- copy-on-write reads/writes commute
                              with the corresponding Python ops.
  - `tx_state_*_spec`      -- snapshot/commit/revert match Python.
  - `state_root_spec`      -- post-state root equals
                              `compute_state_root_and_trie_changes`
                              over the same inputs.

  TODO(stateless-proofs).
-/

namespace EvmAsm.Stateless.State.Spec

-- TODO(stateless-proofs): cpsTripleWithin for the State subtree.

end EvmAsm.Stateless.State.Spec
