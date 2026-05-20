/-
  EvmAsm.Stateless.Headers.Validate

  Validate that a sequence of RLP-encoded block headers forms a
  contiguous chain. Mirrors the Python `validate_headers` from
  `execution-specs/src/ethereum/forks/amsterdam/stateless.py:178`:

      def validate_headers(encoded_headers):
          assert len(encoded_headers) <= 256, "Too many headers"
          headers      = [_decode_header(b)  for b in encoded_headers]
          block_hashes = [keccak256(b)        for b in encoded_headers]
          for i in range(1, len(headers)):
              if headers[i].parent_hash != block_hashes[i-1]:
                  raise Exception("not contiguous")
          return headers, block_hashes

  ## Algorithm

  Inputs (already navigated to by the caller via
  `EvmAsm.Stateless.SSZ.Decode`):
  - `headers_section_addr` : start of witness.headers SSZ list
  - `headers_section_len`  : section length in bytes
  - `n_headers`            : count derived from first inner u32

  For each header `i in 0..n_headers`:
  1. Compute `el_i_start`, `el_i_end` via the inner offsets table.
  2. `block_hashes[i] := keccak256(bytes[el_i_start..el_i_end])`.
     (Uses `Stateless.Headers.BlockHash`.)
  3. If `i > 0`:
     - RLP-decode `headers[i]` (just enough to extract the
       `parent_hash` field at byte offset 0 of the outer list).
     - Compare `parent_hash == block_hashes[i-1]`.
     - On mismatch, route to `Unimplemented` (PR1 reason
       `WITNESS_NOT_CONTIGUOUS` -- new code to add).

  Output: each `block_hashes[i]` written to a fixed-layout slot
  in `EXECUTION_WITNESS_AREA` (see `MemoryLayout.lean`). The
  decoded headers' `parent_hash` and `state_root` fields are also
  exposed for `Block/Execute` to consume.

  ## Constraint: max 256 headers

  The Python helper asserts `len(encoded_headers) <= 256`. On
  the RISC-V side this becomes a `BNE/BGE` check against
  `n_headers` early; overflow routes to `Unimplemented`.

  ## PR-K8 status

  Scaffold only. The Program lands in a follow-up once
  `BlockHash` is wired (PR-K9) and `Decode` is enough to extract
  `parent_hash`.
-/

namespace EvmAsm.Stateless.Headers.Validate

-- TODO(stateless-headers): expose `validate_headers` Program
-- iterating over `witness.headers`, computing block hashes via
-- `Stateless.Headers.BlockHash`, and verifying parent_hash chain
-- contiguity. On any failure, route to `Stateless.unimplemented_exit`
-- with the appropriate reason code.

end EvmAsm.Stateless.Headers.Validate
