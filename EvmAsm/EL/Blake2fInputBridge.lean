/-
  EvmAsm.EL.Blake2fInputBridge

  Bridge from EVM BLAKE2F precompile call data to the byte-buffer inputs
  consumed by the zkVM `zkvm_blake2f` accelerator. The accelerator C
  signature is

      zkvm_status zkvm_blake2f(uint32_t rounds,
                               zkvm_blake2f_state* h,
                               const zkvm_blake2f_message* m,
                               const zkvm_blake2f_offset* t,
                               uint8_t f);

  where `zkvm_blake2f_state` is `zkvm_bytes_64`, `zkvm_blake2f_message` is
  `zkvm_bytes_128`, and `zkvm_blake2f_offset` is `zkvm_bytes_16`. This
  module fixes the input payload shape (rounds + h + m + t + f) and exposes
  per-field memory-read decompositions; the result-buffer shape and pure
  execution boundary live in the sibling `Result`/`Ecall` bridges.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Blake2fInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- The 64-byte BLAKE2F state payload (`zkvm_blake2f_state`). -/
abbrev StateBytes := Fin 64 → Byte

/-- The 128-byte BLAKE2F message payload (`zkvm_blake2f_message`). -/
abbrev MessageBytes := Fin 128 → Byte

/-- The 16-byte BLAKE2F offset payload (`zkvm_blake2f_offset`). -/
abbrev OffsetBytes := Fin 16 → Byte

/--
Input payload passed to the
`zkvm_blake2f(rounds, h, m, t, f)` accelerator.

Distinctive token: Blake2fInputBridge.AcceleratorInput zkvm_blake2f.
-/
structure AcceleratorInput where
  rounds : UInt32
  h      : StateBytes
  m      : MessageBytes
  t      : OffsetBytes
  f      : Byte

/-- Read a fixed `n`-byte block starting at `start` from a `MemoryReader`. -/
def readFixed (n : Nat) (memory : MemoryReader) (start : Nat) : Fin n → Byte :=
  fun i => memory (start + i.val)

/-- Build the `h` 64-byte state payload by reading from memory. -/
def stateBytesFromMemory (memory : MemoryReader) (start : Nat) : StateBytes :=
  readFixed 64 memory start

/-- Build the `m` 128-byte message payload by reading from memory. -/
def messageBytesFromMemory (memory : MemoryReader) (start : Nat) : MessageBytes :=
  readFixed 128 memory start

/-- Build the `t` 16-byte offset payload by reading from memory. -/
def offsetBytesFromMemory (memory : MemoryReader) (start : Nat) : OffsetBytes :=
  readFixed 16 memory start

/--
Accelerator-call input assembled from a byte-addressed memory plus the scalar
`rounds` and `f` fields read from the EVM call data prefix.

Distinctive token: Blake2fInputBridge.blake2fInputFromMemory.
-/
def blake2fInputFromMemory
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) : AcceleratorInput :=
  { rounds := rounds
    h      := stateBytesFromMemory memory hStart
    m      := messageBytesFromMemory memory mStart
    t      := offsetBytesFromMemory memory tStart
    f      := f }

/-- Compatibility alias matching the SHA256/BN254 bridge naming. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) : AcceleratorInput :=
  blake2fInputFromMemory memory rounds hStart mStart tStart f

theorem readFixed_apply (n : Nat) (memory : MemoryReader) (start : Nat) (i : Fin n) :
    readFixed n memory start i = memory (start + i.val) := rfl

theorem stateBytesFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    stateBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem messageBytesFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 128) :
    messageBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem offsetBytesFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 16) :
    offsetBytesFromMemory memory start i = memory (start + i.val) := rfl

theorem blake2fInputFromMemory_rounds
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    (blake2fInputFromMemory memory rounds hStart mStart tStart f).rounds = rounds := rfl

theorem blake2fInputFromMemory_h
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    (blake2fInputFromMemory memory rounds hStart mStart tStart f).h =
      stateBytesFromMemory memory hStart := rfl

theorem blake2fInputFromMemory_m
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    (blake2fInputFromMemory memory rounds hStart mStart tStart f).m =
      messageBytesFromMemory memory mStart := rfl

theorem blake2fInputFromMemory_t
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    (blake2fInputFromMemory memory rounds hStart mStart tStart f).t =
      offsetBytesFromMemory memory tStart := rfl

theorem blake2fInputFromMemory_f
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    (blake2fInputFromMemory memory rounds hStart mStart tStart f).f = f := rfl

theorem acceleratorInputFromMemory_eq
    (memory : MemoryReader) (rounds : UInt32)
    (hStart mStart tStart : Nat) (f : Byte) :
    acceleratorInputFromMemory memory rounds hStart mStart tStart f =
      blake2fInputFromMemory memory rounds hStart mStart tStart f := rfl

end Blake2fInputBridge

end EvmAsm.EL
