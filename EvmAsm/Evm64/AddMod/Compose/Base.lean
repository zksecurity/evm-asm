/-
  EvmAsm.Evm64.AddMod.Compose.Base

  Shared composition infrastructure for ADDMOD: `evm_addmod_program_code`
  (the `CodeReq.ofProg` handle for the assembled top-level `evm_addmod`
  Program from slice 3c, beads `evm-asm-xl2jn`), plus per-block
  subsumption helpers tying each sub-block's `CodeReq.ofProg` handle
  back to `evm_addmod_program_code` for use by the slice-3d composition
  (`evm-asm-s7v49`, `evm_addmod_stack_spec_within`).

  Mirrors `EvmAsm.Evm64.Byte.Spec` §"CodeReq subsumption" — each helper
  is a thin wrapper around `CodeReq.ofProg_mono_sub` with the byte
  offset / instruction index / range bound discharged by `decide` /
  `bv_omega`. No proof engineering beyond structural slicing.
-/

import EvmAsm.Evm64.AddMod.LimbSpec
import EvmAsm.Evm64.AddMod.AddrNorm

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

-- ============================================================================
-- Top-level program-code handle
-- ============================================================================

/-- `CodeReq.ofProg` handle for the assembled top-level `evm_addmod`
    Program (33 instructions, 132 bytes). The single-parameter `modOff`
    is the signed 21-bit byte offset from the phase-2 JAL site to the
    entry of `evm_mod_callable`; it is threaded through unchanged from
    the surrounding caller frame. -/
abbrev evm_addmod_program_code (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (evm_addmod modOff)

-- ============================================================================
-- Per-block CodeReq subsumption: each sub-block code ⊆ evm_addmod_program_code
-- ============================================================================
--
-- Block layout (mirrors `evm_addmod_*_byte_off` lemmas in `AddMod/Program.lean`):
--
--   prologue       : instr  0 .. 29  (length 30, bytes   0 ..119)
--   phase1_carry   : instr 30        (length  1, byte  120)
--   phase2_reduce  : instr 31        (length  1, byte  124)
--   epilogue       : instr 32        (length  1, byte  128)

/-- Common slice-equation tactic for the four `mono_sub` calls below.
    `evm_addmod`, `evm_addmod_prologue`, `evm_addmod_phase1_carry`,
    `evm_addmod_phase2_reduce`, and `evm_addmod_epilogue` all reduce to
    plain `List Instr` literals once `seq` and `single` are unfolded;
    `rfl` closes the resulting `List.take .. (List.drop ..) = ..` goal
    since the only remaining free variable `modOff` appears identically
    on both sides as a single concrete `JAL .x1 modOff` constructor. -/
local macro "evm_addmod_slice_rfl" : tactic =>
  `(tactic| (
      unfold evm_addmod evm_addmod_prologue evm_add
        evm_addmod_phase1_carry evm_addmod_phase2_reduce
        evm_addmod_phase2_mod_call evm_addmod_epilogue
      simp only [seq, single]
      rfl))

/-- The `evm_addmod_prologue` sub-block (30 instrs at offset 0) is
    subsumed by `evm_addmod_program_code`. -/
theorem evm_addmod_program_code_prologue_sub
    {base : Word} {modOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg base evm_addmod_prologue) a = some i →
      (evm_addmod_program_code base modOff) a = some i := by
  unfold evm_addmod_program_code
  refine CodeReq.ofProg_mono_sub base base (evm_addmod modOff)
    evm_addmod_prologue 0
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_slice_rfl
  · rw [evm_addmod_length, evm_addmod_prologue_length]; decide
  · rw [evm_addmod_length]; decide

/-- The `evm_addmod_phase1_carry` sub-block (1 instr at offset 120) is
    subsumed by `evm_addmod_program_code`. -/
theorem evm_addmod_program_code_phase1_carry_sub
    {base : Word} {modOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 120) evm_addmod_phase1_carry) a = some i →
      (evm_addmod_program_code base modOff) a = some i := by
  unfold evm_addmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 120) (evm_addmod modOff)
    evm_addmod_phase1_carry 30
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_slice_rfl
  · rw [evm_addmod_length, evm_addmod_phase1_carry_length]; decide
  · rw [evm_addmod_length]; decide

/-- The `evm_addmod_phase2_reduce` sub-block (1 instr at offset 124) is
    subsumed by `evm_addmod_program_code`. -/
theorem evm_addmod_program_code_phase2_reduce_sub
    {base : Word} {modOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 124)
        (evm_addmod_phase2_reduce modOff)) a = some i →
      (evm_addmod_program_code base modOff) a = some i := by
  unfold evm_addmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 124) (evm_addmod modOff)
    (evm_addmod_phase2_reduce modOff) 31
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_slice_rfl
  · rw [evm_addmod_length, evm_addmod_phase2_reduce_length]; decide
  · rw [evm_addmod_length]; decide

/-- The `evm_addmod_epilogue` sub-block (1 instr at offset 128) is
    subsumed by `evm_addmod_program_code`. -/
theorem evm_addmod_program_code_epilogue_sub
    {base : Word} {modOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 128) evm_addmod_epilogue) a = some i →
      (evm_addmod_program_code base modOff) a = some i := by
  unfold evm_addmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 128) (evm_addmod modOff)
    evm_addmod_epilogue 32
    (by bv_omega) ?_ ?_ ?_
  · evm_addmod_slice_rfl
  · rw [evm_addmod_length, evm_addmod_epilogue_length]
  · rw [evm_addmod_length]; decide

/-- Bundled per-block subsumptions for `evm_addmod_program_code`, used by
    slice 3d (`evm-asm-s7v49`) when wiring per-block cpsTriple specs into
    the full `evm_addmod_stack_spec_within` composition. -/
theorem evm_addmod_program_code_block_subs
    {base : Word} {modOff : BitVec 21} :
    (∀ a i, (CodeReq.ofProg base evm_addmod_prologue) a = some i →
      (evm_addmod_program_code base modOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 120) evm_addmod_phase1_carry) a = some i →
      (evm_addmod_program_code base modOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 124)
        (evm_addmod_phase2_reduce modOff)) a = some i →
      (evm_addmod_program_code base modOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 128) evm_addmod_epilogue) a = some i →
      (evm_addmod_program_code base modOff) a = some i) :=
  ⟨evm_addmod_program_code_prologue_sub,
    evm_addmod_program_code_phase1_carry_sub,
    evm_addmod_program_code_phase2_reduce_sub,
    evm_addmod_program_code_epilogue_sub⟩

end EvmAsm.Evm64.AddMod.Compose
