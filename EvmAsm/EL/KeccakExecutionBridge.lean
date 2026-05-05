/-
  EvmAsm.EL.KeccakExecutionBridge

  End-to-end pure bridge from KECCAK memory input bytes to the stack word.
-/

import EvmAsm.EL.KeccakInputBridge
import EvmAsm.EL.KeccakResultBridge

namespace EvmAsm.EL

namespace KeccakExecutionBridge

abbrev KeccakArgs := EvmAsm.Evm64.KeccakArgs.Args
abbrev MemoryReader := KeccakInputBridge.MemoryReader
abbrev HashBytes := KeccakResultBridge.HashBytes
abbrev AcceleratorInput := KeccakInputBridge.AcceleratorInput
abbrev AcceleratorOutput := KeccakResultBridge.AcceleratorOutput
abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Abstract KECCAK accelerator/hash function over the exact input byte list
    read from EVM memory. -/
abbrev HashOracle := List Byte → HashBytes

/-- Distinctive token: KeccakExecutionBridge.stackWordFromMemoryHash #111. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (args : KeccakArgs) : AcceleratorInput :=
  KeccakInputBridge.acceleratorInputFromArgs memory args

def acceleratorOutputFromMemoryHash
    (hash : HashOracle) (memory : MemoryReader) (args : KeccakArgs) :
    AcceleratorOutput :=
  { hash := hash (acceleratorInputFromMemory memory args).bytes }

def stackWordFromMemoryHash
    (hash : HashOracle) (memory : MemoryReader) (args : KeccakArgs) : EvmWord :=
  KeccakResultBridge.stackWordFromAcceleratorOutput
    (acceleratorOutputFromMemoryHash hash memory args)

theorem acceleratorInputFromMemory_bytes
    (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromMemory memory args).bytes =
      KeccakInputBridge.keccakInputBytesFromMemory memory args := rfl

theorem acceleratorInputFromMemory_length
    (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromMemory memory args).bytes.length =
      EvmAsm.Evm64.KeccakArgs.inputSizeNat args := by
  exact KeccakInputBridge.acceleratorInputFromArgs_length memory args

theorem acceleratorOutputFromMemoryHash_hash
    (hash : HashOracle) (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorOutputFromMemoryHash hash memory args).hash =
      hash (KeccakInputBridge.keccakInputBytesFromMemory memory args) := rfl

theorem stackWordFromMemoryHash_eq
    (hash : HashOracle) (memory : MemoryReader) (args : KeccakArgs) :
    stackWordFromMemoryHash hash memory args =
      KeccakResultBridge.stackWordFromAcceleratorHash
        (hash (KeccakInputBridge.keccakInputBytesFromMemory memory args)) := rfl

theorem stackWordFromMemoryHash_zero_size
    (hash : HashOracle) (memory : MemoryReader) (offset : EvmAsm.Evm64.EvmWord) :
    stackWordFromMemoryHash hash memory
        (EvmAsm.Evm64.KeccakArgs.keccakArgs offset 0) =
      KeccakResultBridge.stackWordFromAcceleratorHash (hash []) := by
  rfl

end KeccakExecutionBridge

end EvmAsm.EL
