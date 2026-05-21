/-
  EvmAsm.Stateless.Headers

  Umbrella for the header-validation subtree of the stateless guest.
  Implements `validate_headers` from
  `execution-specs/src/ethereum/forks/amsterdam/stateless.py:188`:

      def validate_headers(encoded_headers):
          assert len(encoded_headers) <= 256
          headers = [_decode_header(b) for b in encoded_headers]
          block_hashes = [keccak256(b) for b in encoded_headers]
          for i in range(1, len(headers)):
              if headers[i].parent_hash != block_hashes[i-1]:
                  raise Exception("not contiguous")
          return headers, block_hashes

  ## Subtree

  - `BlockHash.lean`  — keccak of one RLP-encoded header (the
                        canonical block hash). Wraps the ziskemu
                        Keccak-f intrinsic via `zkvm_keccak256` and
                        will eventually carry a CPS triple.
  - `Decode.lean`     — RLP-decode header bytes into a `Header`
                        record. Reuses `EvmAsm/Rv64/RLP/Phase*` for
                        primitive types and adds header-specific
                        composition.
  - `Validate.lean`   — chain validation: hash each header, check
                        `headers[i].parent_hash == block_hashes[i-1]`,
                        return decoded headers + block_hashes.
  - `Spec.lean`       — placeholder for the eventual cpsTriple specs
                        over the modules above.

  All four files are scaffolds in PR-K8: doc comments + namespaces
  only, no Programs yet. The header-validation Programs land in
  follow-up PRs (one per module).
-/

import EvmAsm.Stateless.Headers.BlockHash
import EvmAsm.Stateless.Headers.Decode
import EvmAsm.Stateless.Headers.Validate
import EvmAsm.Stateless.Headers.KeccakChain
import EvmAsm.Stateless.Headers.KeccakArray
import EvmAsm.Stateless.Headers.Spec
