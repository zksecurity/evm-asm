/-
  EvmAsm.EL.Secp256k1EcrecoverInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_secp256k1_ecrecover` accelerator.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Secp256k1EcrecoverInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A secp256k1 message hash as represented by `zkvm_secp256k1_hash`. -/
abbrev MessageHashBytes := Fin 32 → Byte

/-- A secp256k1 signature as represented by `zkvm_secp256k1_signature`. -/
abbrev SignatureBytes := Fin 64 → Byte

/-- Input payload passed to `zkvm_secp256k1_ecrecover(msg, sig, recid, output)`. -/
structure AcceleratorInput where
  msg : MessageHashBytes
  sig : SignatureBytes
  recid : Byte

/-- Read one fixed-width secp256k1 message hash from executable memory. -/
def messageHashFromMemory (memory : MemoryReader) (start : Nat) : MessageHashBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width secp256k1 signature from executable memory. -/
def signatureFromMemory (memory : MemoryReader) (start : Nat) : SignatureBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Secp256k1EcrecoverInputBridge.secp256k1EcrecoverInputFromMemory.
-/
def secp256k1EcrecoverInputFromMemory
    (memory : MemoryReader) (msgStart sigStart : Nat) (recid : Byte) :
    AcceleratorInput :=
  { msg := messageHashFromMemory memory msgStart
    sig := signatureFromMemory memory sigStart
    recid := recid }

theorem messageHashFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    messageHashFromMemory memory start i = memory (start + i.toNat) := rfl

theorem signatureFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    signatureFromMemory memory start i = memory (start + i.toNat) := rfl

theorem secp256k1EcrecoverInputFromMemory_msg
    (memory : MemoryReader) (msgStart sigStart : Nat) (recid : Byte) :
    (secp256k1EcrecoverInputFromMemory memory msgStart sigStart recid).msg =
      messageHashFromMemory memory msgStart := rfl

theorem secp256k1EcrecoverInputFromMemory_sig
    (memory : MemoryReader) (msgStart sigStart : Nat) (recid : Byte) :
    (secp256k1EcrecoverInputFromMemory memory msgStart sigStart recid).sig =
      signatureFromMemory memory sigStart := rfl

theorem secp256k1EcrecoverInputFromMemory_recid
    (memory : MemoryReader) (msgStart sigStart : Nat) (recid : Byte) :
    (secp256k1EcrecoverInputFromMemory memory msgStart sigStart recid).recid =
      recid := rfl

end Secp256k1EcrecoverInputBridge

end EvmAsm.EL
