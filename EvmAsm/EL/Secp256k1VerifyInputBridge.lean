/-
  EvmAsm.EL.Secp256k1VerifyInputBridge

  Bridge from secp256k1 ECDSA verification call data to the byte-buffer input
  consumed by the zkVM `zkvm_secp256k1_verify` accelerator.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Secp256k1VerifyInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- The 32-byte message hash payload (`zkvm_secp256k1_hash`). -/
abbrev MsgBytes := Fin 32 → Byte

/-- The 64-byte signature payload (`zkvm_secp256k1_signature`). -/
abbrev SigBytes := Fin 64 → Byte

/-- The 64-byte public-key payload (`zkvm_secp256k1_pubkey`). -/
abbrev PubkeyBytes := Fin 64 → Byte

/--
Input payload passed to the
`zkvm_secp256k1_verify(msg, sig, pubkey, *verified)` accelerator.

Distinctive token: Secp256k1VerifyInputBridge.AcceleratorInput zkvm_secp256k1_verify.
-/
structure AcceleratorInput where
  msg    : MsgBytes
  sig    : SigBytes
  pubkey : PubkeyBytes

/-- Read a fixed `n`-byte block starting at `start` from a `MemoryReader`. -/
def readFixed (n : Nat) (memory : MemoryReader) (start : Nat) : Fin n → Byte :=
  fun i => memory (start + i.val)

/-- Build the message-hash payload by reading 32 bytes from memory. -/
def msgBytesFromMemory (memory : MemoryReader) (start : Nat) : MsgBytes :=
  readFixed 32 memory start

/-- Build the signature payload by reading 64 bytes from memory. -/
def sigBytesFromMemory (memory : MemoryReader) (start : Nat) : SigBytes :=
  readFixed 64 memory start

/-- Build the public-key payload by reading 64 bytes from memory. -/
def pubkeyBytesFromMemory (memory : MemoryReader) (start : Nat) : PubkeyBytes :=
  readFixed 64 memory start

/--
Accelerator-call input assembled from three byte-addressed memory slices, one
per fixed-width payload field.
-/
def acceleratorInputFromMemory
    (memory : MemoryReader)
    (msgStart sigStart pubkeyStart : Nat) : AcceleratorInput :=
  { msg    := msgBytesFromMemory memory msgStart
    sig    := sigBytesFromMemory memory sigStart
    pubkey := pubkeyBytesFromMemory memory pubkeyStart }

theorem readFixed_apply (n : Nat) (memory : MemoryReader) (start : Nat) (i : Fin n) :
    readFixed n memory start i = memory (start + i.val) := rfl

theorem msgBytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    msgBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem sigBytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    sigBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem pubkeyBytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    pubkeyBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem acceleratorInputFromMemory_msg
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (acceleratorInputFromMemory memory msgStart sigStart pubkeyStart).msg =
      msgBytesFromMemory memory msgStart := rfl

theorem acceleratorInputFromMemory_sig
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (acceleratorInputFromMemory memory msgStart sigStart pubkeyStart).sig =
      sigBytesFromMemory memory sigStart := rfl

theorem acceleratorInputFromMemory_pubkey
    (memory : MemoryReader) (msgStart sigStart pubkeyStart : Nat) :
    (acceleratorInputFromMemory memory msgStart sigStart pubkeyStart).pubkey =
      pubkeyBytesFromMemory memory pubkeyStart := rfl

end Secp256k1VerifyInputBridge

end EvmAsm.EL
