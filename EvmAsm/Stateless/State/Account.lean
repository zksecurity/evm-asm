/-
  EvmAsm.Stateless.State.Account

  RLP-encode/decode an Ethereum account record. The on-trie
  account is a 4-field RLP list:

      Account RLP = [
        nonce        : Uint,        # variable-length BE big-int
        balance      : U256,        # variable-length BE big-int
        storage_root : Hash32,      # 32 bytes (or empty for empty trie)
        code_hash    : Hash32,      # 32 bytes
      ]

  ## Decoding (reading from witness MPT)

  Account bytes come from `MPT.Get(state_root, keccak256(address))`.
  Decode lifts them into a flat in-memory record at a caller-
  supplied scratch slot.

  ## Encoding (writing to mutated MPT)

  When the BlockState commits an account change, re-encode the
  4 fields into RLP bytes. The output bytes are then inserted
  into the trie via `MPT.Set`, producing a new state_root.

  ## Special cases

  - `EMPTY_TRIE_ROOT = keccak256(rlp([]))`: when an account has
    no storage, `storage_root` equals this constant.
  - Empty account (nonce=0, balance=0, storage_root=EMPTY,
    code_hash=EMPTY_CODE_HASH): per EIP-161 the account is
    deleted from the trie rather than stored as zero values.

  ## PR-K27 status

  Decode side lands in
  `EvmAsm.Codegen.Programs.accountDecodeFunction`. Splits an
  RLP-encoded account into four caller-supplied output slots:
  `(nonce: u64, balance: u256_be, storage_root: 32 B,
   code_hash: 32 B)`. Composes PR-K20 `rlp_list_nth_item`
  four times.

  Encode side (mutating the trie) is a follow-up.

  Calling convention for `account_decode`:

      Input:
        a0 (input)  : account RLP bytes ptr
        a1 (input)  : account RLP byte length
        a2 (input)  : u64 nonce output ptr (8 bytes;
                      written as little-endian u64)
        a3 (input)  : u256 balance output ptr (32 bytes;
                      written as big-endian u256, left-zero-
                      padded for values < 32 bytes)
        a4 (input)  : storage_root output ptr (32 bytes)
        a5 (input)  : code_hash output ptr (32 bytes)
        ra (input)  : return

      Output:
        a0 = 0  success; all four slots populated
        a0 = 1  parse error (not a 4-item list, nonce/balance
                length out of range, or hash field length ≠ 32)

  Special cases:
    * Empty nonce string (RLP `0x80`) → nonce = 0.
    * Empty balance string → balance = 0 (32 zero bytes).
    * Empty hash strings are NOT accepted (must be exactly 32 B).
      Use the canonical `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH`
      constants to encode missing storage / code.
-/

namespace EvmAsm.Stateless.State.Account

-- TODO(stateless-state): expose `encode_account(in, out_ptr)
-- -> out_len` Program (the mutating side).

end EvmAsm.Stateless.State.Account
