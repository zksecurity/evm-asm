/-
  EvmAsm.Stateless.Headers.Spec

  Placeholder for cpsTriple specs over the modules under
  `EvmAsm/Stateless/Headers/`.

  Final form (once the Programs land):

  - `block_hash_spec_within` -- given input bytes at
    `[a0, a0 + a1)`, after running `BlockHash`, the 32 bytes at
    `[a2, a2 + 32)` equal `keccak256(input bytes)`. CPS triple
    composes the `zkvm_keccak256` spec; the sponge-internal
    proofs come from the keccak bridge.

  - `decode_header_spec_within` -- given RLP-encoded header bytes
    in a region with `well-formed RLP` predicate, after running
    `Decode`, the in-memory record at the output address matches
    `rlp.decode_to(Header, input_bytes)` (the Python reference).

  - `validate_headers_spec_within` -- given `witness.headers` SSZ
    section satisfying the section invariant, after running
    `Validate`, either:
      (a) all parent_hash links match  =>  state mirrors Python's
          `(headers, block_hashes)` return,    or
      (b) any link mismatches           =>  routes to
          `unimplemented_exit` with the mismatch reason code.

  TODO(stateless-proofs): The above triples reference Programs
  that don't exist yet. The current PR-K8 scaffold lives so the
  import graph is wired and future proof PRs have a stable file
  path to claim.
-/

namespace EvmAsm.Stateless.Headers.Spec

-- TODO(stateless-proofs): per-module cpsTripleWithin statements.

end EvmAsm.Stateless.Headers.Spec
