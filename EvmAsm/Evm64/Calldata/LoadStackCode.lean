/-
  EvmAsm.Evm64.Calldata.LoadStackCode

  CodeReq bridge from the CALLDATALOAD in-bounds byte-window core to the
  reusable MLOAD stack-code surface.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Calldata.LoadArgs
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

/--
CALLDATALOAD prologue stack spec: pop the calldata offset from the EVM stack
slot at `x12` and resolve the source byte pointer
`addrReg ← envPtrReg + offReg` where `envPtrReg` holds `env.callDataPtr`.

This is the program-identical transport of `mload_prologue_stack_spec_within`
through `evm_calldataload_window_of_mloadStackCode_spec_within`. It splits
the upcoming `evm_calldataload_stack_spec` (evm-asm-pgeuo / GH #104) into a
prologue half plus a four-limb half so subsequent slices only need to wire
the four-limb byte-window read.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_prologue_stack_spec_within #104.
-/
theorem calldataload_window_prologue_stack_spec_within
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
       (sp ↦ₘ offset)) :=
  evm_calldataload_window_of_mloadStackCode_spec_within
    offReg byteReg accReg addrReg envPtrReg base (base + 8)
    (mload_prologue_stack_spec_within offReg byteReg accReg addrReg envPtrReg
      sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0)

/--
Transport the MLOAD four-limbs stack spec to the program-identical in-bounds
CALLDATALOAD window core. Mirrors `calldataload_window_prologue_stack_spec_within`
for the four-limbs side: combined, both pieces give the prologue + byte-window
ingredients for the upcoming `evm_calldataload_stack_spec`
(evm-asm-pgeuo / GH #104).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_four_limbs_stack_spec_within #104.
-/
theorem calldataload_window_four_limbs_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P Q) :
    cpsTripleWithin n (base + 8) (base + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  exact mload_four_limbs_stack_spec_within
    offReg byteReg accReg addrReg envPtrReg base h

/--
CALLDATALOAD window combined stack spec: sequentially compose the prologue
half (`calldataload_window_prologue_stack_spec_within`) with a caller-supplied
four-limbs core triple via `cpsTripleWithin_seq_same_cr`.

Takes the four-limbs core triple as a hypothesis whose precondition matches
the prologue's postcondition (after the `addrReg ← envPtr + offset` resolve)
and whose postcondition is an arbitrary `Q`. The prologue threads
`(sp ↦ₘ offset)` and the resolved address registers through to the four-limbs
side, so the caller only needs to instantiate the four-limbs hypothesis with
a concrete byte-window read (e.g. via `mload_four_limbs_stack_spec_within`
together with a concrete byte-window core spec).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_combined_stack_spec_within #104.
-/
theorem calldataload_window_combined_stack_spec_within
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 376)
        (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
         (sp ↦ₘ offset))
        Q) :
    cpsTripleWithin (2 + n) base (base + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_seq_same_cr
    (calldataload_window_prologue_stack_spec_within
      offReg byteReg accReg addrReg envPtrReg
      sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0)
    h4

/--
The byte-level semantic word produced by the CALLDATALOAD in-bounds window,
phrased through decoded stack arguments.

Distinctive token:
Calldata.LoadStackCode.calldataLoadWindowOutputWordFromArgs #104.
-/
def calldataLoadWindowOutputWordFromArgs
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) : EvmWord :=
  mloadLoadedWordFromBytes
    (CallDataLoadArgs.windowByteFromArgs data args 0)
    (CallDataLoadArgs.windowByteFromArgs data args 1)
    (CallDataLoadArgs.windowByteFromArgs data args 2)
    (CallDataLoadArgs.windowByteFromArgs data args 3)
    (CallDataLoadArgs.windowByteFromArgs data args 4)
    (CallDataLoadArgs.windowByteFromArgs data args 5)
    (CallDataLoadArgs.windowByteFromArgs data args 6)
    (CallDataLoadArgs.windowByteFromArgs data args 7)
    (CallDataLoadArgs.windowByteFromArgs data args 8)
    (CallDataLoadArgs.windowByteFromArgs data args 9)
    (CallDataLoadArgs.windowByteFromArgs data args 10)
    (CallDataLoadArgs.windowByteFromArgs data args 11)
    (CallDataLoadArgs.windowByteFromArgs data args 12)
    (CallDataLoadArgs.windowByteFromArgs data args 13)
    (CallDataLoadArgs.windowByteFromArgs data args 14)
    (CallDataLoadArgs.windowByteFromArgs data args 15)
    (CallDataLoadArgs.windowByteFromArgs data args 16)
    (CallDataLoadArgs.windowByteFromArgs data args 17)
    (CallDataLoadArgs.windowByteFromArgs data args 18)
    (CallDataLoadArgs.windowByteFromArgs data args 19)
    (CallDataLoadArgs.windowByteFromArgs data args 20)
    (CallDataLoadArgs.windowByteFromArgs data args 21)
    (CallDataLoadArgs.windowByteFromArgs data args 22)
    (CallDataLoadArgs.windowByteFromArgs data args 23)
    (CallDataLoadArgs.windowByteFromArgs data args 24)
    (CallDataLoadArgs.windowByteFromArgs data args 25)
    (CallDataLoadArgs.windowByteFromArgs data args 26)
    (CallDataLoadArgs.windowByteFromArgs data args 27)
    (CallDataLoadArgs.windowByteFromArgs data args 28)
    (CallDataLoadArgs.windowByteFromArgs data args 29)
    (CallDataLoadArgs.windowByteFromArgs data args 30)
    (CallDataLoadArgs.windowByteFromArgs data args 31)

/--
The low stack limb of the CALLDATALOAD byte-window word is the packed
least-significant byte block produced by the window core.
-/
theorem getLimbN_calldataLoadWindowOutputWordFromArgs_0
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 0 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 24)
        (CallDataLoadArgs.windowByteFromArgs data args 25)
        (CallDataLoadArgs.windowByteFromArgs data args 26)
        (CallDataLoadArgs.windowByteFromArgs data args 27)
        (CallDataLoadArgs.windowByteFromArgs data args 28)
        (CallDataLoadArgs.windowByteFromArgs data args 29)
        (CallDataLoadArgs.windowByteFromArgs data args 30)
        (CallDataLoadArgs.windowByteFromArgs data args 31) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_0]

theorem getLimbN_calldataLoadWindowOutputWordFromArgs_1
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 1 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 16)
        (CallDataLoadArgs.windowByteFromArgs data args 17)
        (CallDataLoadArgs.windowByteFromArgs data args 18)
        (CallDataLoadArgs.windowByteFromArgs data args 19)
        (CallDataLoadArgs.windowByteFromArgs data args 20)
        (CallDataLoadArgs.windowByteFromArgs data args 21)
        (CallDataLoadArgs.windowByteFromArgs data args 22)
        (CallDataLoadArgs.windowByteFromArgs data args 23) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_1]

theorem getLimbN_calldataLoadWindowOutputWordFromArgs_2
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 2 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 8)
        (CallDataLoadArgs.windowByteFromArgs data args 9)
        (CallDataLoadArgs.windowByteFromArgs data args 10)
        (CallDataLoadArgs.windowByteFromArgs data args 11)
        (CallDataLoadArgs.windowByteFromArgs data args 12)
        (CallDataLoadArgs.windowByteFromArgs data args 13)
        (CallDataLoadArgs.windowByteFromArgs data args 14)
        (CallDataLoadArgs.windowByteFromArgs data args 15) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_2]

/--
Distinctive token:
Calldata.LoadStackCode.getLimbN_calldataLoadWindowOutputWordFromArgs_3 #104 #107.
-/
theorem getLimbN_calldataLoadWindowOutputWordFromArgs_3
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 3 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 0)
        (CallDataLoadArgs.windowByteFromArgs data args 1)
        (CallDataLoadArgs.windowByteFromArgs data args 2)
        (CallDataLoadArgs.windowByteFromArgs data args 3)
        (CallDataLoadArgs.windowByteFromArgs data args 4)
        (CallDataLoadArgs.windowByteFromArgs data args 5)
        (CallDataLoadArgs.windowByteFromArgs data args 6)
        (CallDataLoadArgs.windowByteFromArgs data args 7) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_3]

/--
Fold the four MLOAD-style packed output limbs produced by the CALLDATALOAD
window core into the EVM stack word selected by decoded calldata arguments.
-/
theorem calldataLoadWindowOutputWordFromArgs_evmStackIs_fold
    (sp : Word) (rest : List EvmWord)
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (((sp ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 24)
        (CallDataLoadArgs.windowByteFromArgs data args 25)
        (CallDataLoadArgs.windowByteFromArgs data args 26)
        (CallDataLoadArgs.windowByteFromArgs data args 27)
        (CallDataLoadArgs.windowByteFromArgs data args 28)
        (CallDataLoadArgs.windowByteFromArgs data args 29)
        (CallDataLoadArgs.windowByteFromArgs data args 30)
        (CallDataLoadArgs.windowByteFromArgs data args 31)) **
      ((sp + 8) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 16)
        (CallDataLoadArgs.windowByteFromArgs data args 17)
        (CallDataLoadArgs.windowByteFromArgs data args 18)
        (CallDataLoadArgs.windowByteFromArgs data args 19)
        (CallDataLoadArgs.windowByteFromArgs data args 20)
        (CallDataLoadArgs.windowByteFromArgs data args 21)
        (CallDataLoadArgs.windowByteFromArgs data args 22)
        (CallDataLoadArgs.windowByteFromArgs data args 23)) **
      ((sp + 16) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 8)
        (CallDataLoadArgs.windowByteFromArgs data args 9)
        (CallDataLoadArgs.windowByteFromArgs data args 10)
        (CallDataLoadArgs.windowByteFromArgs data args 11)
        (CallDataLoadArgs.windowByteFromArgs data args 12)
        (CallDataLoadArgs.windowByteFromArgs data args 13)
        (CallDataLoadArgs.windowByteFromArgs data args 14)
        (CallDataLoadArgs.windowByteFromArgs data args 15)) **
      ((sp + 24) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 0)
        (CallDataLoadArgs.windowByteFromArgs data args 1)
        (CallDataLoadArgs.windowByteFromArgs data args 2)
        (CallDataLoadArgs.windowByteFromArgs data args 3)
        (CallDataLoadArgs.windowByteFromArgs data args 4)
        (CallDataLoadArgs.windowByteFromArgs data args 5)
        (CallDataLoadArgs.windowByteFromArgs data args 6)
        (CallDataLoadArgs.windowByteFromArgs data args 7))) **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp (calldataLoadWindowOutputWordFromArgs data args :: rest) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [mloadLoadedWordFromBytes_evmStackIs_fold]

end Calldata
end EvmAsm.Evm64
