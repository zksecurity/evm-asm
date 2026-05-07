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

-- ============================================================================
-- Per-block leaf specs lifted onto `evm_addmod_program_code`
-- ============================================================================
--
-- Thin wrappers around the four leaf cpsTriple specs in
-- `EvmAsm/Evm64/AddMod/LimbSpec.lean` (prologue / phase1_carry /
-- phase2_reduce / epilogue) that transport each spec from its sub-block
-- `CodeReq.ofProg` handle onto the consolidated `evm_addmod_program_code`
-- via `cpsTripleWithin_extend_code` and the per-block `_sub` lemmas above.
--
-- These are the ADDMOD analogs of the `mstore_*_evm_mstore_spec_within`
-- bridges in `Evm64/MStore/Spec.lean` (e.g. L273
-- `mstore_prologue_evm_mstore_spec_within`, L339
-- `mstore_epilogue_evm_mstore_spec_within`). They let slice 3d
-- (`evm-asm-s7v49`, `evm_addmod_stack_spec_within`) compose the per-block
-- specs directly on the program-code surface without re-doing the
-- monotonicity transport at every call site.

/-- `evm_addmod_prologue` cpsTriple spec lifted from the sub-block
    `CodeReq.ofProg` handle onto `evm_addmod_program_code`. Direct ADDMOD
    analog of `mstore_prologue_evm_mstore_spec_within`. -/
theorem evm_addmod_prologue_evm_addmod_spec_within
    (sp : Word) (base : Word) (modOff : BitVec 21)
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
    cpsTripleWithin 30 base (base + 120)
      (evm_addmod_program_code base modOff)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
       ((sp + 56) ↦ₘ result3)) :=
  cpsTripleWithin_extend_code
    (hmono := evm_addmod_program_code_prologue_sub)
    (h := evm_addmod_prologue_spec_within sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11)

/-- `evm_addmod_phase1_carry` cpsTriple spec lifted from the sub-block
    `CodeReq.ofProg` handle onto `evm_addmod_program_code`. The single
    `ADDI x7 x5 0` MV instruction lives at `base + 120`. -/
theorem evm_addmod_phase1_carry_evm_addmod_spec_within
    (v5 vOld : Word) (base : Word) (modOff : BitVec 21) :
    cpsTripleWithin 1 (base + 120) ((base + 120) + 4)
      (evm_addmod_program_code base modOff)
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ vOld))
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ (v5 + signExtend12 (0 : BitVec 12)))) :=
  cpsTripleWithin_extend_code
    (hmono := evm_addmod_program_code_phase1_carry_sub)
    (h := evm_addmod_phase1_carry_spec_within v5 vOld (base + 120))

/-- `evm_addmod_phase2_reduce` cpsTriple spec lifted from the sub-block
    `CodeReq.ofProg` handle onto `evm_addmod_program_code`. The single
    `JAL x1 modOff` near-call to `evm_mod_callable` lives at `base + 124`. -/
theorem evm_addmod_phase2_reduce_evm_addmod_spec_within
    (vOld : Word) (base : Word) (modOff : BitVec 21) :
    cpsTripleWithin 1 (base + 124) ((base + 124) + signExtend21 modOff)
      (evm_addmod_program_code base modOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + 124) + 4)) :=
  cpsTripleWithin_extend_code
    (hmono := evm_addmod_program_code_phase2_reduce_sub)
    (h := evm_addmod_phase2_reduce_spec_within modOff vOld (base + 124))

/-- `evm_addmod_epilogue` cpsTriple spec lifted from the sub-block
    `CodeReq.ofProg` handle onto `evm_addmod_program_code`. The single
    `ADDI x12 x12 32` stack-pointer advance lives at `base + 128`. -/
theorem evm_addmod_epilogue_evm_addmod_spec_within
    (vOld : Word) (base : Word) (modOff : BitVec 21) :
    cpsTripleWithin 1 (base + 128) ((base + 128) + 4)
      (evm_addmod_program_code base modOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (32 : BitVec 12))) :=
  cpsTripleWithin_extend_code
    (hmono := evm_addmod_program_code_epilogue_sub)
    (h := evm_addmod_epilogue_spec_within vOld (base + 128))

end EvmAsm.Evm64.AddMod.Compose
