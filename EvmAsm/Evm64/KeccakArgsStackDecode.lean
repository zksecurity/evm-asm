/-
  EvmAsm.Evm64.KeccakArgsStackDecode

  Pure top-of-stack decoder for KECCAK256/SHA3 arguments (GH #111).
-/

import EvmAsm.Evm64.KeccakArgs

namespace EvmAsm.Evm64

namespace KeccakArgsStackDecode

open KeccakArgs

/--
Decode KECCAK256/SHA3 stack arguments from the top-of-stack list order:
`offset, size`.

Distinctive token: KeccakArgsStackDecode.decodeKeccakStack? #111.
-/
def decodeKeccakStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (keccakArgs offset size)
  | _ => none

theorem decodeKeccakStack?_some
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeKeccakStack? (offset :: size :: rest) =
      some (keccakArgs offset size) := rfl

theorem decoded_inputRange (offset size : EvmWord) :
    inputRange (keccakArgs offset size) =
      { offset := offset, size := size } := rfl

theorem decoded_inputOffsetNat (offset size : EvmWord) :
    inputOffsetNat (keccakArgs offset size) = offset.toNat := rfl

theorem decoded_inputSizeNat (offset size : EvmWord) :
    inputSizeNat (keccakArgs offset size) = size.toNat := rfl

theorem decoded_stackArgumentCount :
    stackArgumentCount = 2 := rfl

theorem decoded_resultCount :
    resultCount = 1 := rfl

end KeccakArgsStackDecode

end EvmAsm.Evm64
