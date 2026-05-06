/-
  EvmAsm.EL.Secp256k1EcrecoverResultBridge

  Bridge from the `zkvm_secp256k1_ecrecover` accelerator output to the
  executable precompile-result surface.
-/

import EvmAsm.Evm64.Accelerators.Status
import EvmAsm.EL.Secp256k1EcrecoverInputBridge

namespace EvmAsm.EL

namespace Secp256k1EcrecoverResultBridge

abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- A secp256k1 public key as represented by `zkvm_secp256k1_pubkey`. -/
abbrev PublicKeyBytes := Fin 64 → Byte

/-- Accelerator output payload for `zkvm_secp256k1_ecrecover`. -/
structure AcceleratorOutput where
  pubkey : PublicKeyBytes

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

def publicKeyBytesList (pubkey : PublicKeyBytes) : List Byte :=
  List.ofFn pubkey

theorem publicKeyBytesList_length (pubkey : PublicKeyBytes) :
    (publicKeyBytesList pubkey).length = 64 := by
  simp [publicKeyBytesList]

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

theorem acceleratorOutput_pubkey_length (output : AcceleratorOutput) :
    (publicKeyBytesList output.pubkey).length = 64 :=
  publicKeyBytesList_length output.pubkey

end Secp256k1EcrecoverResultBridge

end EvmAsm.EL
