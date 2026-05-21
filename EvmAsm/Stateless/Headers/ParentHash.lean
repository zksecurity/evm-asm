/-
  EvmAsm.Stateless.Headers.ParentHash

  Extract the `parent_hash` field (the first `Bytes32` field) of
  an RLP-encoded Ethereum Block Header.

  ## Why

  `validate_headers` checks `header[i].parent_hash ==
  keccak256(header[i-1])` for `i = 1..N`. Combined with PR-K16's
  `headers_keccak_array` (which produces the array of all
  per-header keccak digests), `parent_hash` extraction is the
  remaining piece needed for the chain check.

  The function is RLP-walk-only -- no full RLP decode of the
  20-odd remaining fields. The cheaper signature lets the
  caller surface just the 32 bytes that the chain check
  consumes.

  ## RLP layout of an Ethereum header

  An RLP-encoded Ethereum header is a list of N fields where
  the first field is a 32-byte `parent_hash`. RLP encoding of
  a list `[item_0, item_1, ...]`:

    - If total payload bytes ≤ 55:
        prefix = 0xc0 + payload_byte_count  (1 byte)
    - If total payload bytes ≥ 56:
        prefix = 0xf7 + length_of_length    (1 byte)
                 ++ length (length_of_length bytes)

  Real Ethereum headers are several hundred bytes, so the
  outer prefix is almost always `0xf9 ll ll` (3 bytes; list of
  256..65535 bytes), occasionally `0xf8 ll` (2 bytes; 56..255).

  After the outer prefix, the first item is the
  `parent_hash: Bytes32`, RLP-encoded as `0xa0` (string of 32
  bytes) followed by the 32 raw bytes. So once the outer list
  prefix is skipped, the next byte should be `0xa0`, then the
  32 bytes of parent_hash follow.

  ## Contract

  Caller convention:

      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr (receives parent_hash)
      ra (input)  : return

      a0 (output) :
        0 -- success; 32 bytes at *a2 = parent_hash
        1 -- RLP parse failure (first byte not in list range,
             item length prefix not 0xa0, or input too short).

  Supports outer list prefixes 0xc0..0xc0+55 (short list),
  0xf8 (1-byte length), and 0xf9 (2-byte length). Outer list
  prefixes 0xfa+ (3+ byte length) require headers >= 64K bytes;
  not seen in practice, but the function gracefully returns
  failure if it sees them.

  ## Implementation shape

  `headersParentHashFunction` emits the labelled function
  `headers_parent_hash:`. Pure register arithmetic (no scratch
  memory), so the function is leaf-callable: caller may pass
  any `sp` (even 0).

  ## PR-K17 status

  Defines the contract. The executable lives in the standalone
  `zisk_headers_parent_hash` probe. PR-K18+ composes this with
  PR-K16's `headers_keccak_array` to implement the
  `validate_headers` parent_hash chain check.
-/

namespace EvmAsm.Stateless.Headers

-- TODO(stateless-headers): expose a `cpsTripleWithin` spec
-- once the overall side-effect surface is captured.

end EvmAsm.Stateless.Headers
