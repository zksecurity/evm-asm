/-
  EvmAsm.EL.KeccakStackBridge

  KECCAK256 stack-result bridge for GH #111.
-/

import EvmAsm.EL.KeccakResultBridge

namespace EvmAsm.EL

namespace KeccakStackBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/--
KECCAK256 pushes exactly one stack word: the 256-bit hash returned by the
zkVM accelerator.

Distinctive token: KeccakStackBridge.keccakStackResult #111.
-/
def keccakStackResult (output : KeccakResultBridge.AcceleratorOutput) : List EvmWord :=
  [KeccakResultBridge.stackWordFromAcceleratorOutput output]

theorem keccakStackResult_length (output : KeccakResultBridge.AcceleratorOutput) :
    (keccakStackResult output).length = 1 := rfl

theorem keccakStackResult_head?
    (output : KeccakResultBridge.AcceleratorOutput) :
    (keccakStackResult output).head? =
      some (KeccakResultBridge.stackWordFromAcceleratorOutput output) := rfl

theorem keccakStackResult_get_zero
    (output : KeccakResultBridge.AcceleratorOutput) :
    (keccakStackResult output)[0]? =
      some (KeccakResultBridge.stackWordFromAcceleratorOutput output) := rfl

theorem keccakStackResult_eq_hash
    (hash : KeccakResultBridge.HashBytes) :
    keccakStackResult { hash := hash } =
      [KeccakResultBridge.stackWordFromAcceleratorHash hash] := rfl

theorem keccakStackResult_head_eq_hash
    (hash : KeccakResultBridge.HashBytes) :
    (keccakStackResult { hash := hash }).head? =
      some (KeccakResultBridge.stackWordFromAcceleratorHash hash) := rfl

end KeccakStackBridge

end EvmAsm.EL
