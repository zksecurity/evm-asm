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

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.Account

-- TODO(stateless-state): expose `decode_account(ptr, len, out)`
-- and `encode_account(in, out_ptr) -> out_len` Programs.

end EvmAsm.Stateless.State.Account
