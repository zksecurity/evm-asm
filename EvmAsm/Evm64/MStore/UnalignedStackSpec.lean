/-
  EvmAsm.Evm64.MStore.UnalignedStackSpec

  MSTORE per-quarter stack-level wrappers shaped to match the `h0/h1/h2/h3`
  hypotheses of `evm_mstore_combined_one_limb_sequence_stack_spec_within`
  (`EvmAsm/Evm64/MStore/StackSpec.lean`). Each wrapper frames the
  prologue-threaded cells on top of `mstore_one_limb_spec_within`
  (`EvmAsm/Evm64/MStore/LimbSpec.lean`) for one quarter of the
  big-endian MSTORE write, so that subsequent slices can compose
  q0/q1/q2/q3 into the topmost `evm_mstore_stack_spec_within`
  (evm-asm-ln8t5 / GH #53 follow-up).

  Direct MSTORE analog of the per-quarter MLOAD lemmas in
  `EvmAsm/Evm64/MLoad/StackSpec.lean`
  (`evm_mload_unaligned_one_limb_q0_stack_spec_within` etc.).
-/

import EvmAsm.Evm64.MStore.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
MSTORE q0 framed per-quarter stack spec: thin frame around
`mstore_one_limb_spec_within` for the most-significant limb of the
big-endian MSTORE write (source offset `32`, byte offsets `24..31`,
i.e. byte index `0` within the high dword of the pair via the
`mstoreLimbWindowOk` / `mstoreDwordPairAddr` indexing).

Unlike the MLOAD q0 case, the source limb at `sp + 32` is a separate
slot from the prologue-threaded `(sp ↦ₘ offset)` cell, so no
`signExtend12 0` collapse is needed. The prologue cells
(`offReg ↦ᵣ offset`, `memBaseReg ↦ᵣ memBase`, `sp ↦ₘ offset`) are
framed unchanged; the underlying `mstore_one_limb_spec_within` already
threads `addrReg ↦ᵣ (memBase + offset)` and `(.x12 ↦ᵣ sp)`.

Pre/post are stated in the same shape as `h0` of
`evm_mstore_combined_one_limb_sequence_stack_spec_within`
(`EvmAsm/Evm64/MStore/StackSpec.lean`), so subsequent compose slices
can plug this in directly.

Sub-slice toward `evm_mstore_stack_spec_within` (evm-asm-ln8t5 / GH #53
follow-up): together with q1/q2/q3 siblings, feeds
`evm_mstore_combined_one_limb_sequence_stack_spec_within` to land the
topmost stack-level MSTORE theorem.

Distinctive token: evm_mstore_unaligned_one_limb_q0_stack_spec_within #53.
-/
theorem evm_mstore_unaligned_one_limb_q0_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal)))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset) **
       (let stored :=
         MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
        (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
        (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) := by
  -- Underlying one-limb MSTORE spec at q0 (srcOff = 32, dst byte offsets 24..31).
  have core := mstore_one_limb_spec_within addrReg byteReg accReg
    (memBase + offset) byteOld accOld loVal hiVal loAddr hiAddr sp limbVal
    start
    (32 : BitVec 12) 24 25 26 27 28 29 30 31 (base + 8)
    h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mstoreOneLimbPre_unfold, mstoreOneLimbPost_unfold] at core
  dsimp only [] at core
  -- Normalize endpoint: `base + 8 + 68 = base + 76`.
  have hpc : ((base + 8) + 68 : Word) = base + 76 := by bv_omega
  rw [show ((base + 8) + 68 : Word) = base + 76 from hpc] at core
  -- Frame the prologue-threaded cells:
  --   (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset).
  -- (`addrReg ↦ᵣ memBase + offset` and `(.x12 ↦ᵣ sp)` are already in `core`'s pre.)
  have framed := cpsTripleWithin_frameL
    (F := (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset))
    (by pcFree) core
  -- Permute pre/post into the goal's grouping.
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

end EvmAsm.Evm64
