/-
  EvmAsm.Stateless.Headers.Decode

  RLP-decode an Ethereum block header. Mirrors the Python
  `_decode_header` helper from
  `execution-specs/src/ethereum/forks/amsterdam/stateless.py:166`:

      def _decode_header(header_bytes):
          try:
              return rlp.decode_to(Header, header_bytes)
          except rlp.DecodingError:
              return rlp.decode_to(PreviousForkHeader, header_bytes)

  PR-K8 scaffolds only the amsterdam-fork path; the bpo5 fallback
  for fork-transition blocks comes later (Python catches the
  decode error and retries against the previous fork's Header
  schema).

  ## Layout (amsterdam Header, 22 fields per `blocks.py`)

      parent_hash             Hash32  (32 bytes)
      ommers_hash             Hash32
      coinbase                Address (20 bytes)
      state_root              Root    (32)
      transactions_root       Root
      receipt_root            Root
      bloom                   Bloom   (256)
      difficulty              Uint    (variable)
      number                  Uint
      gas_limit               Uint
      gas_used                Uint
      timestamp               U256
      extra_data              Bytes   (variable)
      prev_randao             Bytes32 (32)
      nonce                   Bytes8  (8)
      base_fee_per_gas        Uint
      withdrawals_root        Root
      blob_gas_used           U64
      excess_blob_gas         U64
      parent_beacon_block_root Root
      requests_hash           Hash32
      block_access_list_hash  Hash32

  The whole header is one RLP list. Each field has a fixed or
  variable-size encoding per the RLP spec.

  ## Reuse

  - `EvmAsm/Rv64/RLP/Phase1*.lean` — outer list prefix classifier.
  - `EvmAsm/Rv64/RLP/Phase2*.lean` — length extraction.
  - `EvmAsm/Rv64/RLP/Phase3*.lean` — single-item decode (bytes /
    list head).

  The header decoder composes these phases for each field in
  sequence, writing the decoded values into a fixed-layout
  `HEADER_DECODE_AREA` in working RAM (a slot inside the
  `EXECUTION_WITNESS_AREA` reserved in
  `EvmAsm/Stateless/MemoryLayout.lean`).

  ## PR-K8 status

  Scaffold only. The Programs land in follow-up PRs once the RLP
  phases 4..6 are also in place (currently RLP phases 1..3 are
  upstreamed; see PLAN.md "EL.3 RLP RISC-V Decoder").
-/

namespace EvmAsm.Stateless.Headers.Decode

-- TODO(stateless-headers): expose `decode_header(input_ptr, len,
-- output_addr)` -- a Program that walks the 22 fields of an
-- amsterdam Header from RLP-encoded bytes into a flat in-memory
-- record at `output_addr`.

end EvmAsm.Stateless.Headers.Decode
