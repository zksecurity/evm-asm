/-
  EvmAsm.EL.Sha256ResultBridge

  Bridge from the zkVM SHA256 accelerator output to the EVM stack word returned
  by the precompile-facing executable spec.
-/

import EvmAsm.EL.KeccakResultBridge

namespace EvmAsm.EL

namespace Sha256ResultBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- The SHA256 accelerator returns `zkvm_sha256_hash`, a 32-byte array. -/
abbrev HashBytes := Fin 32 → Byte

/-- Accelerator output payload for `zkvm_sha256`. -/
structure AcceleratorOutput where
  hash : HashBytes

def hashBytesList (hash : HashBytes) : List Byte :=
  List.ofFn hash

/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  KeccakResultBridge.wordFromBigEndianBytes bytes

/-- Distinctive token: Sha256ResultBridge.stackWordFromAcceleratorHash. -/
def stackWordFromAcceleratorHash (hash : HashBytes) : EvmWord :=
  wordFromBigEndianBytes (hashBytesList hash)

/-- Stack word returned by SHA256 from the accelerator output buffer. -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  stackWordFromAcceleratorHash output.hash

theorem hashBytesList_length (hash : HashBytes) :
    (hashBytesList hash).length = 32 := by
  simp [hashBytesList]

@[simp] theorem wordFromBigEndianBytes_nil :
    wordFromBigEndianBytes [] = 0 := rfl

theorem wordFromBigEndianBytes_cons (byte : Byte) (tail : List Byte) :
    wordFromBigEndianBytes (byte :: tail) =
      BitVec.ofNat 256
        (byte.toNat * 256 ^ tail.length + EvmAsm.EL.RLP.Nat.fromBytesBE tail) := by
  rfl

theorem stackWordFromAcceleratorHash_eq (hash : HashBytes) :
    stackWordFromAcceleratorHash hash =
      BitVec.ofNat 256 (EvmAsm.EL.RLP.Nat.fromBytesBE (hashBytesList hash)) := rfl

theorem stackWordFromAcceleratorOutput_eq (output : AcceleratorOutput) :
    stackWordFromAcceleratorOutput output =
      stackWordFromAcceleratorHash output.hash := rfl

theorem stackWordFromAcceleratorOutput_hash_length (output : AcceleratorOutput) :
    (hashBytesList output.hash).length = 32 :=
  hashBytesList_length output.hash

end Sha256ResultBridge

end EvmAsm.EL
