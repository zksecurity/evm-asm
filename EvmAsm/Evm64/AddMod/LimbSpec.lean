/-
  EvmAsm.Evm64.AddMod.LimbSpec

  Per-block / per-limb cpsTriple specs for ADDMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- evm_addmod_epilogue (1 instruction, slice evm-asm-hsybl toward evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_epilogue` (defined in `Evm64/AddMod/Program.lean`) is the
-- single-instruction `ADDI x12 x12 32` block that performs the final
-- EVM stack-pointer advance after the result limbs have been written
-- by the upstream phase blocks. Mirrors the shape of
-- `exp_loop_pointer_advance_spec_within` (Exp/LimbSpec.lean §4.5):
-- a `CodeReq.ofProg → singleton` rewrite plus `addi_spec_gen_same_within`.

abbrev evm_addmod_epilogue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_epilogue

theorem evm_addmod_epilogue_spec_within
    (vOld : Word) (base : Word) :
    let code := evm_addmod_epilogue_code base
    cpsTripleWithin 1 base (base + 4) code
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (32 : BitVec 12))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base evm_addmod_epilogue) _ _
  rw [show CodeReq.ofProg base evm_addmod_epilogue =
      CodeReq.singleton base (.ADDI .x12 .x12 32) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_same_within .x12 vOld 32 base (by nofun)

end EvmAsm.Evm64
