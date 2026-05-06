/-
  EvmAsm.EL.Ripemd160InputBridge

  Bridge from EVM RIPEMD160 precompile call data to the byte-buffer input
  consumed by the zkVM accelerator interface.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Ripemd160InputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- Input payload passed to the `zkvm_ripemd160(data, len, output)` accelerator. -/
structure AcceleratorInput where
  bytes : List Byte
  deriving Repr

/--
Executable-spec `memory_read_bytes(memory, start, size)` shape: read exactly
`size` bytes starting at `start`.
-/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  KeccakInputBridge.memoryReadBytes memory start size

/-- Distinctive token: Ripemd160InputBridge.ripemd160InputBytesFromMemory. -/
def ripemd160InputBytesFromMemory (memory : MemoryReader) (start size : Nat) : List Byte :=
  memoryReadBytes memory start size

/-- Accelerator-call input assembled from a byte-addressed memory slice. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (start size : Nat) : AcceleratorInput :=
  { bytes := ripemd160InputBytesFromMemory memory start size }

theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_length]

theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_get?, h_i]

@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl

theorem ripemd160InputBytesFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (ripemd160InputBytesFromMemory memory start size).length = size := by
  simp [ripemd160InputBytesFromMemory, memoryReadBytes_length]

theorem ripemd160InputBytesFromMemory_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (ripemd160InputBytesFromMemory memory start size)[i]? =
      some (memory (start + i)) := by
  simp [ripemd160InputBytesFromMemory, memoryReadBytes_get?, h_i]

@[simp] theorem ripemd160InputBytesFromMemory_zero_size
    (memory : MemoryReader) (start : Nat) :
    ripemd160InputBytesFromMemory memory start 0 = [] := rfl

theorem acceleratorInputFromMemory_bytes
    (memory : MemoryReader) (start size : Nat) :
    (acceleratorInputFromMemory memory start size).bytes =
      ripemd160InputBytesFromMemory memory start size := rfl

theorem acceleratorInputFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (acceleratorInputFromMemory memory start size).bytes.length = size := by
  simp [acceleratorInputFromMemory, ripemd160InputBytesFromMemory_length]

end Ripemd160InputBridge

end EvmAsm.EL
