/-
  EvmAsm.Evm64.Calldata.LoadStackCode

  CodeReq bridge from the CALLDATALOAD in-bounds byte-window core to the
  reusable MLOAD stack-code surface.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.MLoad.StackSpec

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/--
The in-bounds CALLDATALOAD byte-window core has the same CodeReq shape as
the reusable MLOAD stack-code bundle.

Distinctive token:
Calldata.LoadStackCode.evm_calldataload_window_code_eq_mloadStackCode #104 #99.
-/
theorem evm_calldataload_window_code_eq_mloadStackCode
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word) :
    evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base =
      mloadStackCode offReg byteReg accReg addrReg envPtrReg base := by
  rw [evm_calldataload_window_code_eq_evm_mload_code]
  unfold evm_mload_code mloadStackCode
  rw [mloadPrologueCode_eq_ofProg, mloadFourLimbsCode_eq_ofProg]
  rw [show base + 8 =
      base + BitVec.ofNat 64
        (4 * (LD offReg .x12 0 ;; ADD addrReg envPtrReg offReg).length) from by
    simp [LD, ADD, single, seq]]
  rw [← CodeReq.ofProg_append]
  unfold evm_mload mloadFourLimbsProg mloadTwoLimbsProg
  rfl

/--
Transport an MLOAD stack-code triple to the program-identical in-bounds
CALLDATALOAD window core.
-/
theorem evm_calldataload_window_of_mloadStackCode_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base endPc : Word)
    (h : cpsTripleWithin n base endPc
      (mloadStackCode offReg byteReg accReg addrReg envPtrReg base) P Q) :
    cpsTripleWithin n base endPc
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  exact h

end Calldata
end EvmAsm.Evm64
