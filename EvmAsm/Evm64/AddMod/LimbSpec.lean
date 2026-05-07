/-
  EvmAsm.Evm64.AddMod.LimbSpec

  Per-block / per-limb cpsTriple specs for ADDMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- evm_addmod_prologue (30 instructions, slice evm-asm-hm8z3 toward evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_prologue` (defined in `Evm64/AddMod/Program.lean`) is the
-- 30-instruction prologue that folds `a + b` (mod 2^256) into the second
-- EVM stack slot, leaving the 257th carry-out bit in scratch register `x5`.
-- Per `Evm64/AddMod/Program.lean`, `evm_addmod_prologue := evm_add`, so the
-- spec is a thin wrapper around `evm_add_spec_within` /
-- `evm_add_stack_spec_within` (Evm64/Add/Spec.lean §1, §2).

abbrev evm_addmod_prologue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_prologue

/-- Register/memory-level prologue spec: thin lift of `evm_add_spec_within`
    through the `evm_addmod_prologue := evm_add` alias. -/
theorem evm_addmod_prologue_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_addmod_prologue_code base
    cpsTripleWithin 30 base (base + 120) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
       ((sp + 56) ↦ₘ result3)) := by
  -- `evm_addmod_prologue` is definitionally `evm_add`, so the codes coincide.
  show cpsTripleWithin 30 base (base + 120) (evm_add_code base) _ _
  exact evm_add_spec_within sp base a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11

/-- Stack-level prologue spec on `evmWordIs` surface: thin lift of
    `evm_add_stack_spec_within`. -/
theorem evm_addmod_prologue_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
    let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
    let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
    let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_addmod_prologue_code base
    cpsTripleWithin 30 base (base + 120) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  show cpsTripleWithin 30 base (base + 120) (evm_add_code base) _ _
  exact evm_add_stack_spec_within sp base a b v7 v6 v5 v11

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

-- ============================================================================
-- evm_addmod_phase1_carry (1 instruction, slice evm-asm-ot10w toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase1_carry` (defined in `Evm64/AddMod/Program.lean`) is the
-- single-instruction `ADDI x7 x5 0` block — a register `MV` that copies the
-- 257th carry bit from `x5` into `x7`, freeing `x5` for the modulus-reduction
-- phase that follows. Mirrors the shape of `addi_spec_gen_within`: a
-- `CodeReq.ofProg → singleton` rewrite plus `addi_spec_gen_within` with
-- `imm = 0`.
--
-- Note: post-state register value is `v5 + signExtend12 (0 : BitVec 12)` (the
-- raw shape produced by `addi_spec_gen_within`); downstream callers normalize
-- via `BitVec.add_zero` / `signExtend12` simp lemmas as needed.

abbrev evm_addmod_phase1_carry_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_phase1_carry

theorem evm_addmod_phase1_carry_spec_within
    (v5 vOld : Word) (base : Word) :
    let code := evm_addmod_phase1_carry_code base
    cpsTripleWithin 1 base (base + 4) code
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ vOld))
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ (v5 + signExtend12 (0 : BitVec 12)))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base evm_addmod_phase1_carry) _ _
  rw [show CodeReq.ofProg base evm_addmod_phase1_carry =
      CodeReq.singleton base (.ADDI .x7 .x5 0) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_within .x7 .x5 vOld v5 0 base (by nofun)

-- ============================================================================
-- evm_addmod_phase2_zero_path (4 instructions, slice evm-asm-eu2hw toward
-- evm-asm-s7v49)
-- ============================================================================
--
-- `evm_addmod_phase2_zero_path` (defined in `Evm64/AddMod/Program.lean`) is the
-- 4-instruction `SD x12, x0, {32,40,48,56}` block that writes zeros into the
-- four result limbs at `x12 + 32 .. 56` on the `N = 0` path. Direct analog
-- of the SD chain at the end of `exp_prologue_spec_within`
-- (`Exp/LimbSpec.lean §5`): four `sd_x0_spec_gen_within` applications glued
-- by `runBlock`. Block layout:
--
--   instr  0 (byte  0) :  SD x12, x0, 32   -- result limb 0 := 0
--   instr  1 (byte  4) :  SD x12, x0, 40   -- result limb 1 := 0
--   instr  2 (byte  8) :  SD x12, x0, 48   -- result limb 2 := 0
--   instr  3 (byte 12) :  SD x12, x0, 56   -- result limb 3 := 0

abbrev evm_addmod_phase2_zero_path_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.SD .x12 .x0 32)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x0 40)).union
      ((CodeReq.singleton (base + 8) (.SD .x12 .x0 48)).union
        (CodeReq.singleton (base + 12) (.SD .x12 .x0 56))))

theorem evm_addmod_phase2_zero_path_code_eq_ofProg (base : Word) :
    evm_addmod_phase2_zero_path_code base =
      CodeReq.ofProg base evm_addmod_phase2_zero_path := by
  unfold evm_addmod_phase2_zero_path_code evm_addmod_phase2_zero_path SD single seq
  change _ = CodeReq.ofProg base
    [.SD .x12 .x0 32, .SD .x12 .x0 40, .SD .x12 .x0 48, .SD .x12 .x0 56]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

/-- Register/memory-level zero-store spec: writes `0` into the four result
    limbs at `x12 + 32 .. 56` via `SD x12, x0, k`. Mirrors the SD chain in
    `exp_prologue_spec_within`. -/
theorem evm_addmod_phase2_zero_path_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    let code := evm_addmod_phase2_zero_path_code base
    cpsTripleWithin 4 base (base + 16) code
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  unfold evm_addmod_phase2_zero_path_code
  have hSd0 := generic_sd_x0_spec_within .x12 sp m0
    (32 : BitVec 12) base
  have hSd1 := generic_sd_x0_spec_within .x12 sp m1
    (40 : BitVec 12) (base + 4)
  have hSd2 := generic_sd_x0_spec_within .x12 sp m2
    (48 : BitVec 12) (base + 8)
  have hSd3 := generic_sd_x0_spec_within .x12 sp m3
    (56 : BitVec 12) (base + 12)
  runBlock hSd0 hSd1 hSd2 hSd3

/-- `ofProg`-flavoured zero-store spec: thin lift of
    `evm_addmod_phase2_zero_path_spec_within` through
    `evm_addmod_phase2_zero_path_code_eq_ofProg`. -/
theorem evm_addmod_phase2_zero_path_ofProg_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base evm_addmod_phase2_zero_path)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← evm_addmod_phase2_zero_path_code_eq_ofProg]
  exact evm_addmod_phase2_zero_path_spec_within sp m0 m1 m2 m3 base

end EvmAsm.Evm64
