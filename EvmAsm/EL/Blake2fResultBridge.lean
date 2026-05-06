/-
  EvmAsm.EL.Blake2fResultBridge

  Bridge from the zkVM `zkvm_blake2f` accelerator output buffer (the 64-byte
  state written back through the `h` pointer) to the byte-list view consumed
  by EL precompile return-data assembly. Mirrors the BN254 G1 add result
  bridge skeleton; we do NOT compute a stack word here because the BLAKE2F
  output is 64 bytes (does not fit into one EVM stack word) — precompile
  output framing is left to a downstream slice.
-/

import EvmAsm.EL.KeccakInputBridge

namespace EvmAsm.EL

namespace Blake2fResultBridge

/-- The 64-byte BLAKE2F state payload (`zkvm_blake2f_state`). -/
abbrev StateBytes := Fin 64 → Byte

/-- Accelerator output payload for `zkvm_blake2f` (the updated state). -/
structure AcceleratorOutput where
  state : StateBytes

/-- Materialise the output state as a byte list (length 64). -/
def stateBytesList (state : StateBytes) : List Byte :=
  List.ofFn state

/-- Distinctive token: Blake2fResultBridge.outputBytesList. -/
def outputBytesList (output : AcceleratorOutput) : List Byte :=
  stateBytesList output.state

theorem stateBytesList_length (state : StateBytes) :
    (stateBytesList state).length = 64 := by
  simp [stateBytesList]

theorem outputBytesList_length (output : AcceleratorOutput) :
    (outputBytesList output).length = 64 := by
  simp [outputBytesList, stateBytesList_length]

theorem outputBytesList_eq (output : AcceleratorOutput) :
    outputBytesList output = stateBytesList output.state := rfl

end Blake2fResultBridge

end EvmAsm.EL
