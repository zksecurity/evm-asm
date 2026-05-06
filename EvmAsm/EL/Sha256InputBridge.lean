/-
  EvmAsm.EL.Sha256InputBridge

  Bridge from EVM SHA256 precompile call data to the byte-buffer input consumed
  by the zkVM accelerator interface.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Sha256InputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- Input payload passed to the `zkvm_sha256(data, len, output)` accelerator. -/
structure AcceleratorInput where
  bytes : List Byte
  deriving Repr

/--
Executable-spec `memory_read_bytes(memory, start, size)` shape: read exactly
`size` bytes starting at `start`.
-/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  KeccakInputBridge.memoryReadBytes memory start size

/-- Distinctive token: Sha256InputBridge.sha256InputBytesFromMemory. -/
def sha256InputBytesFromMemory (memory : MemoryReader) (start size : Nat) : List Byte :=
  memoryReadBytes memory start size

/-- Accelerator-call input assembled from a byte-addressed memory slice. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (start size : Nat) : AcceleratorInput :=
  { bytes := sha256InputBytesFromMemory memory start size }

theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_length]

theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_get?, h_i]

@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl

theorem sha256InputBytesFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (sha256InputBytesFromMemory memory start size).length = size := by
  simp [sha256InputBytesFromMemory, memoryReadBytes_length]

theorem sha256InputBytesFromMemory_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (sha256InputBytesFromMemory memory start size)[i]? =
      some (memory (start + i)) := by
  simp [sha256InputBytesFromMemory, memoryReadBytes_get?, h_i]

@[simp] theorem sha256InputBytesFromMemory_zero_size
    (memory : MemoryReader) (start : Nat) :
    sha256InputBytesFromMemory memory start 0 = [] := rfl

theorem acceleratorInputFromMemory_bytes
    (memory : MemoryReader) (start size : Nat) :
    (acceleratorInputFromMemory memory start size).bytes =
      sha256InputBytesFromMemory memory start size := rfl

theorem acceleratorInputFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (acceleratorInputFromMemory memory start size).bytes.length = size := by
  simp [acceleratorInputFromMemory, sha256InputBytesFromMemory_length]

end Sha256InputBridge

end EvmAsm.EL
