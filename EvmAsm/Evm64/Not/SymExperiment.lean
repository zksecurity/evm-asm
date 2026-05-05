/-
  EvmAsm.Evm64.Not.SymExperiment

  #302 slice 1 — pilot: verify a small opcode (NOT) by symbolically
  simulating each `Instr` step on a concrete `MachineState`, using the
  existing `getReg_setReg_*` / `getMem_setMem_*` simp lemmas in
  `Rv64/Basic.lean` and the `stepN` definition. This file is a
  *side-by-side experiment*; it does NOT replace the existing
  cpsTriple-based proof in `EvmAsm/Evm64/Not/Spec.lean`.

  The pilot covers a single limb (LD / XORI / SD — 3 instructions, the
  inner block of `evm_not`). NOT is the simplest 256-bit EVM opcode in
  the tree (12 instructions = 4 limbs of 3) so the per-limb pilot is
  the smallest meaningful symbolic-simulation unit. The full 12-step
  spec would chain four copies of this block.

  Refs: GH #302, beads evm-asm-nbx7, evm-asm-rg94.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.Basic

namespace EvmAsm.Evm64.SymExperiment

open EvmAsm.Rv64
open MachineState

-- ============================================================================
-- Code-map predicate for the 3-instruction NOT limb at `base`.
-- ============================================================================

/-- `LooksLikeNotLimb base off s` says state `s` has, at PC offsets 0/4/8
    from `base`, the three instructions `LD x7 x12 off`,
    `XORI x7 x7 (-1)`, `SD x12 x7 off`. -/
def LooksLikeNotLimb (base : Word) (off : BitVec 12) (s : MachineState) : Prop :=
  s.code base = some (.LD .x7 .x12 off) ∧
  s.code (base + 4) = some (.XORI .x7 .x7 (-1)) ∧
  s.code (base + 8) = some (.SD .x12 .x7 off)

-- ============================================================================
-- Symbolic-simulation pilot for the 3-instruction NOT limb.
-- ============================================================================

/-- Pilot: end-to-end spec of one NOT limb via symbolic simulation.

    Given a concrete `s` whose code memory holds the 3 NOT-limb
    instructions at consecutive 4-byte-aligned addresses starting at
    `base`, whose PC equals `base`, whose `x12` register holds `sp`,
    and whose memory at `sp + signExtend12 off` holds `limb` (and that
    address is a valid dword), `stepN 3 s` lands at a state where:
      - `pc = base + 12`,
      - `x7` and memory at `addr` both hold `limb ^^^ allOnes`,
      - all other components are unchanged. -/
theorem not_limb_sym_experiment
    (s : MachineState) (base : Word) (off : BitVec 12)
    (sp limb : Word)
    (hcode : LooksLikeNotLimb base off s)
    (hpc : s.pc = base)
    (hsp : s.getReg .x12 = sp)
    (hmem : s.getMem (sp + signExtend12 off) = limb)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let limb' := limb ^^^ signExtend12 (-1 : BitVec 12)
    ∃ s', stepN 3 s = some s' ∧
      s'.pc = base + 12 ∧
      s'.getReg .x12 = sp ∧
      s'.getReg .x7 = limb' ∧
      s'.getMem (sp + signExtend12 off) = limb' ∧
      s'.code = s.code := by
  intro limb'
  obtain ⟨h0, h1, h2⟩ := hcode
  -- ----- Step 1: LD x7 x12 off
  have hfetch0 : s.code s.pc = some (.LD .x7 .x12 off) := by rw [hpc]; exact h0
  have haddr0 : s.getReg .x12 + signExtend12 off = sp + signExtend12 off := by
    rw [hsp]
  have hvalid0 :
      isValidDwordAccess (s.getReg .x12 + signExtend12 off) = true := by
    rw [haddr0]; exact hvalid
  have hstep0 : step s = some (execInstrBr s (.LD .x7 .x12 off)) :=
    step_ld hfetch0 hvalid0
  -- s1 := state after step 1.
  let s1 : MachineState :=
    (s.setReg .x7 (s.getMem (s.getReg .x12 + signExtend12 off))).setPC (s.pc + 4)
  have hs1_eq : execInstrBr s (.LD .x7 .x12 off) = s1 := by
    simp [s1, execInstrBr]
  have hs1_pc : s1.pc = base + 4 := by simp [s1, setPC, hpc]
  have hs1_x12 : s1.getReg .x12 = sp := by
    simp [s1, getReg_setPC, getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x12), hsp]
  have hs1_x7 : s1.getReg .x7 = limb := by
    simp only [s1, getReg_setPC]
    rw [getReg_setReg_eq (by decide : Reg.x7 ≠ Reg.x0)]
    rw [haddr0, hmem]
  have hs1_code : s1.code = s.code := by
    simp [s1, setReg, setPC]
  -- ----- Step 2: XORI x7 x7 (-1)
  have hfetch1 : s1.code s1.pc = some (.XORI .x7 .x7 (-1)) := by
    rw [hs1_pc, hs1_code]; exact h1
  have hstep1 : step s1 = some (execInstrBr s1 (.XORI .x7 .x7 (-1))) :=
    step_non_ecall_non_mem hfetch1 (by nofun) (by nofun) (by rfl)
  let s2 : MachineState :=
    (s1.setReg .x7 (s1.getReg .x7 ^^^ signExtend12 (-1))).setPC (s1.pc + 4)
  have hs2_eq : execInstrBr s1 (.XORI .x7 .x7 (-1)) = s2 := by
    simp [s2, execInstrBr]
  have hs2_pc : s2.pc = base + 8 := by
    simp [s2, setPC, hs1_pc]; bv_omega
  have hs2_x12 : s2.getReg .x12 = sp := by
    simp [s2, getReg_setPC, getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x12), hs1_x12]
  have hs2_x7 : s2.getReg .x7 = limb' := by
    simp only [s2, getReg_setPC, limb']
    rw [getReg_setReg_eq (by decide : Reg.x7 ≠ Reg.x0), hs1_x7]
  have hs2_code : s2.code = s.code := by
    simp [s2, setReg, setPC]; exact hs1_code
  -- ----- Step 3: SD x12 x7 off
  have hfetch2 : s2.code s2.pc = some (.SD .x12 .x7 off) := by
    rw [hs2_pc, hs2_code]; exact h2
  have haddr2 : s2.getReg .x12 + signExtend12 off = sp + signExtend12 off := by
    rw [hs2_x12]
  have hvalid2 :
      isValidDwordAccess (s2.getReg .x12 + signExtend12 off) = true := by
    rw [haddr2]; exact hvalid
  have hstep2 : step s2 = some (execInstrBr s2 (.SD .x12 .x7 off)) :=
    step_sd hfetch2 hvalid2
  let s3 : MachineState :=
    (s2.setMem (s2.getReg .x12 + signExtend12 off) (s2.getReg .x7)).setPC (s2.pc + 4)
  have hs3_eq : execInstrBr s2 (.SD .x12 .x7 off) = s3 := by
    simp [s3, execInstrBr]
  have hs3_pc : s3.pc = base + 12 := by
    simp [s3, setPC, hs2_pc]; bv_omega
  -- setMem doesn't touch regs, so s3.regs = s2.regs.
  have hs3_regs : s3.regs = s2.regs := by simp [s3, setMem, setPC]
  have hs3_x12 : s3.getReg .x12 = sp := by
    have : s3.getReg .x12 = s2.getReg .x12 := by
      simp [getReg, hs3_regs]
    rw [this, hs2_x12]
  have hs3_x7 : s3.getReg .x7 = limb' := by
    have : s3.getReg .x7 = s2.getReg .x7 := by
      simp [getReg, hs3_regs]
    rw [this, hs2_x7]
  have hs3_mem : s3.getMem (sp + signExtend12 off) = limb' := by
    simp only [s3, getMem_setPC]
    rw [show sp + signExtend12 off = s2.getReg .x12 + signExtend12 off from by rw [hs2_x12]]
    rw [getMem_setMem_eq, hs2_x7]
  have hs3_code : s3.code = s.code := by
    simp [s3, setMem, setPC]; exact hs2_code
  -- ----- Combine
  refine ⟨s3, ?_, hs3_pc, hs3_x12, hs3_x7, hs3_mem, hs3_code⟩
  -- stepN 3 s = some s3
  show (step s).bind (stepN 2) = some s3
  rw [hstep0]
  show stepN 2 (execInstrBr s (.LD .x7 .x12 off)) = some s3
  rw [hs1_eq]
  show (step s1).bind (stepN 1) = some s3
  rw [hstep1]
  show stepN 1 (execInstrBr s1 (.XORI .x7 .x7 (-1))) = some s3
  rw [hs2_eq, stepN_one, hstep2, hs3_eq]

end EvmAsm.Evm64.SymExperiment

/-!
## Comparison note: symbolic simulation vs cpsTriple

Existing cpsTriple-based proof for the same one-limb NOT block:

  EvmAsm.Evm64.Not.LimbSpec.not_limb_spec_within  (~14 lines: 3 leaf-spec
    helpers `ld_spec_gen_within`, `xori_spec_gen_same_within`,
    `sd_spec_gen_within`, then a single `runBlock L X S`).

This pilot (`not_limb_sym_experiment`):

  - ~120 lines of explicit per-step bookkeeping (fetch, address-arith,
    register/memory equation, register-frame preservation), repeated
    three times.
  - Hypotheses are larger because the symbolic-simulation contract is
    `LooksLikeNotLimb base off s ∧ pc=base ∧ x12=sp ∧ mem(addr)=limb ∧
    isValidDwordAccess addr` — frame information that cpsTriple gives
    "for free" via separation logic must be threaded explicitly.

### Take-aways for #302

1. **Verbosity scales linearly with instruction count.** Each step costs
   ~25 lines of plumbing: fetch lookup at the new pc, address-arith
   alignment, `getReg_setReg_eq/ne` chains for surviving registers, and
   one `getMem` chain. Without per-instruction macros (the future
   `sym_step` tactic, slice 2) this approach is not competitive on
   30-instruction opcodes (ADD, NOT-full, SUB) — projected ~360 lines
   for `evm_not` end-to-end vs the current ~30-line cpsTriple proof.

2. **Heartbeat profile is FLAT.** No `xperm_hyp` / no `simp` AC
   normalization / no `runBlock` orchestration. Each step's `simp`
   closes against a tiny set of `getReg_setReg_*` lemmas with no
   atom-list flattening. There is no obvious heartbeat wall here —
   compare to `runBlock L0 L1 L2 L3 Laddi` for `evm_add` which
   routinely touches 5-figure heartbeat counts on full assemblies.

3. **Frame preservation is the bottleneck.** cpsTriple gets reg/mem
   frame preservation via the separation-logic `R` parameter of
   `cpsTripleWithin` and the tactic `runBlock` machinery. Symbolic
   simulation has to *prove* preservation pointwise (`s'.code = s.code`,
   `s'.getReg r = s.getReg r` for unmodified `r`, etc.). A future
   `sym_step` tactic could carry these as a record-update normal form
   ("the canonical state after k steps") so the pointwise lemmas come
   from `simp` against `getReg_setReg_eq/ne` rather than hand chains.

4. **Code-fetch lookup is the second sub-bottleneck.** `LooksLikeNotLimb`
   listed three explicit `s.code (base + 4*k) = some i` hypotheses.
   For a 30-instruction opcode that's 30 lines of conjunction plus 30
   `rw`-based unpacks. CodeReq.ofProg + the existing `runBlock` lookup
   tactic is dramatically more compact. A symbolic-simulation tactic
   would need its own `CodeReq.ofProg`-aware fetch resolver (the
   RunBlock tactic's `fetch_resolve` is a model — see
   `EvmAsm/Rv64/Tactics/RunBlock.lean`).

### Recommendation for #302 slice 2 (sym_step tactic)

The pilot supports going forward with `sym_step`, but the tactic must
solve three things automatically or the win evaporates:

  (a) Fetch resolution against `CodeReq.ofProg` / `LooksLikeXxx`
      predicates (~5-line per-step otherwise);
  (b) Memory-validity discharge against `isValidDwordAccess` premises
      (~3-line per-step otherwise);
  (c) Register/memory frame propagation across record updates — probably
      as an automatic invariant carried by the tactic state ("the
      symbolic state after k steps is canonical of the form
      `(((s.setReg r1 v1).setMem a1 m1)…).setPC pc'`"), so each new
      step is one `simp [getReg_setReg_eq, getReg_setReg_ne (by decide)]`
      away from closing.

Without all three, the linear plumbing cost dominates and the existing
cpsTriple+runBlock workflow remains the better default for opcode-level
proofs. With all three, symbolic simulation becomes attractive
specifically for *intra-block* reasoning where `xperm_hyp` is currently
hitting heartbeat walls (#265 / #245) — exactly the use case GH #302
flags.
-/
