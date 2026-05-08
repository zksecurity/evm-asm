import EvmAsm.Evm64.Memory
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
Public MSTORE stack spec with an explicit `evmMemIs` memory frame.

This is a narrow memory-surface entry point: it keeps the abstract EVM memory
region framed across the existing raw-cell byte-window write theorem. A future
slice can replace the raw window cells with an `evmMemIs` extraction/update
lemma without changing callers that already thread the memory region here.

Distinctive token: evm_mstore_stack_spec_within_evmMemIs_frame #53.
-/
theorem evm_mstore_stack_spec_within_evmMemIs_frame
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (offsetHigh1 offsetHigh2 offsetHigh3 : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (memCells : Nat) (contents : Nat → Word)
    (start : Nat) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = offsetHigh1)
    (h_offset2 : offsetWord.getLimbN 2 = offsetHigh2)
    (h_offset3 : offsetWord.getLimbN 3 = offsetHigh3)
    (h_value0 : valueWord.getLimbN 0 = limb0)
    (h_value1 : valueWord.getLimbN 1 = limb1)
    (h_value2 : valueWord.getLimbN 2 = limb2)
    (h_value3 : valueWord.getLimbN 3 = limb3)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start
                  24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        evmStackIs sp (offsetWord :: valueWord :: rest)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3)))) **
       evmMemIs memBase memCells contents)
      ((((.x12 : Reg) ↦ᵣ (sp + 64)) **
       evmStackIs (sp + 64) rest **
       evmWordIs sp offsetWord ** evmWordIs (sp + 32) valueWord **
       ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
        (addrReg ↦ᵣ (memBase + offset)) **
        (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
        (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
        (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
        (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
        (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2))) **
       evmMemIs memBase memCells contents) := by
  have hCore :=
    evm_mstore_stack_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase byteOld accOld
      offsetWord valueWord rest
      offsetHigh1 offsetHigh2 offsetHigh3
      limb0 limb1 limb2 limb3
      loAddr0 hiAddr0 loVal0 hiVal0
      loAddr1 hiAddr1 loVal1 hiVal1
      loAddr2 hiAddr2 loVal2 hiVal2
      loAddr3 hiAddr3 loVal3 hiVal3
      start base
      h_offset0 h_offset1 h_offset2 h_offset3
      h_value0 h_value1 h_value2 h_value3
      h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
      h_window0 h_window1 h_window2 h_window3
  have hFramed :=
    cpsTripleWithin_frameR (evmMemIs memBase memCells contents) (by pcFree) hCore
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    hFramed

end EvmAsm.Evm64
