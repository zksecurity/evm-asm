/-
  EvmAsm.Stateless.Witness.MPT.Decode

  RLP-decode a single MPT node. The wire format (Ethereum MPT) is
  one of three RLP shapes selected by item count + first nibble:

  - **Branch node**: 17-item RLP list. Items 0..16 are child
    references (32-byte hash or inlined RLP < 32 bytes). Item 16
    is the value at this prefix (often empty bytes).
  - **Extension node**: 2-item RLP list `[encoded_path,
    child_ref]`. The encoded_path is HP-encoded nibbles with
    flag bits in the first byte indicating "extension".
  - **Leaf node**: 2-item RLP list `[encoded_path, value]`. Same
    HP encoding as extension but with the "leaf" flag set.

  The decoder returns the node variant + decoded fields without
  copying — the input RLP buffer is in the node_db, and the
  decoder just records `(item_start, item_len)` offsets into a
  small node-shape struct in scratch RAM.

  ## PR-K9 status

  Scaffold only. Depends on RLP phase 4..6 (list decoding) which
  are still WIP per `PLAN.md` "EL.3 RLP RISC-V Decoder".
-/

namespace EvmAsm.Stateless.Witness.MPT.Decode

-- TODO(stateless-witness): decode a single MPT node (branch /
-- extension / leaf) into a small shape struct.

end EvmAsm.Stateless.Witness.MPT.Decode
