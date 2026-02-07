/-
  RiscVMacroAsm.Examples.Swap

  A simple swap macro and its CPS-style Hoare triple specification.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.ControlFlow

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Swap macro
-- ============================================================================

/-- Swap the values of two registers using a temporary register.
    swap rd rs tmp :=
      MV tmp, rd
      MV rd, rs
      MV rs, tmp
-/
def swap (rd rs tmp : Reg) : Program :=
  MV tmp rd ;;
  MV rd rs ;;
  MV rs tmp

/-- Test state for swap. -/
def swapTestState : MachineState where
  regs := fun r =>
    match r with
    | .x10 => 42
    | .x11 => 99
    | _    => 0
  mem := fun _ => 0
  pc := 0

/-- Swap correctness on concrete values: x10 gets the old value of x11. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x10 = 99 := by
  native_decide

/-- Swap correctness on concrete values: x11 gets the old value of x10. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x11 = 42 := by
  native_decide

-- ============================================================================
-- CPS-style Hoare triple for swap (symbolic proof, 3 steps)
-- ============================================================================

/-- Swap specification as a cpsTriple: 3 steps of MV instructions.

    Precondition: x10 holds v, x11 holds w, and x5 holds tmp.
    Postcondition: x10 holds w, x11 holds v, and x5 holds v.

    All three registers are in the precondition since the code writes to all of them.
    The frame R is preserved because it's disjoint from all owned registers. -/
theorem swap_cpsTriple (v w tmp : Word) (base : Addr) :
    cpsTriple (loadProgram base (swap .x10 .x11 .x5)) base (base + 12)
      ((.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w) ** (.x5 ↦ᵣ tmp))
      ((.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v) ** (.x5 ↦ᵣ v)) := by
  intro R hR s hPR hpc
  -- Extract register values (P ** R, then drill into P)
  have hP_holds := holdsFor_sepConj_elim_left hPR
  have hx10 : s.getReg .x10 = v :=
    (holdsFor_regIs .x10 v s).mp (holdsFor_sepConj_elim_left hP_holds)
  have hx11_x5 := holdsFor_sepConj_elim_right hP_holds
  have hx11 : s.getReg .x11 = w :=
    (holdsFor_regIs .x11 w s).mp (holdsFor_sepConj_elim_left hx11_x5)
  have hx5 : s.getReg .x5 = tmp :=
    (holdsFor_regIs .x5 tmp s).mp (holdsFor_sepConj_elim_right hx11_x5)
  -- The swap program is [MV x5 x10, MV x10 x11, MV x11 x5]
  have hprog : swap .x10 .x11 .x5 = [Instr.MV .x5 .x10, Instr.MV .x10 .x11, Instr.MV .x11 .x5] := by
    simp only [swap, seq, MV, single, Program]; rfl
  -- Step 1: MV x5 x10
  have hfetch0 : loadProgram base (swap .x10 .x11 .x5) base = some (Instr.MV .x5 .x10) := by
    rw [hprog]; exact loadProgram_at_base base _ _
  have hstep1 : step (loadProgram base (swap .x10 .x11 .x5)) s =
      some (execInstrBr s (Instr.MV .x5 .x10)) := by simp [step, hpc, hfetch0]
  let s1 := execInstrBr s (Instr.MV .x5 .x10)
  have hs1_pc : s1.pc = base + 4 := by simp [s1, execInstrBr, MachineState.setPC, hpc]
  have hs1_x10 : s1.getReg .x10 = v := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hx10]
  have hs1_x11 : s1.getReg .x11 = w := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hx11]
  have hs1_x5 : s1.getReg .x5 = v := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hx10]
  -- Step 2: MV x10 x11
  have hfetch1 : loadProgram base (swap .x10 .x11 .x5) (base + BitVec.ofNat 32 4) =
      some (Instr.MV .x10 .x11) := by
    rw [hprog, loadProgram_at_index base _ 1 (by simp) (by omega)]; simp
  have hstep2 : step (loadProgram base (swap .x10 .x11 .x5)) s1 =
      some (execInstrBr s1 (Instr.MV .x10 .x11)) := by simp [step, hs1_pc, hfetch1]
  let s2 := execInstrBr s1 (Instr.MV .x10 .x11)
  have hs2_pc : s2.pc = base + 8 := by
    simp only [s2, execInstrBr, MachineState.setPC, hs1_pc, BitVec.add_assoc]; rfl
  have hs2_x10 : s2.getReg .x10 = w := by
    simp [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hs1_x11]
  have hs2_x5 : s2.getReg .x5 = v := by
    simp [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs1_x5]
  -- Step 3: MV x11 x5
  have hfetch2 : loadProgram base (swap .x10 .x11 .x5) (base + BitVec.ofNat 32 8) =
      some (Instr.MV .x11 .x5) := by
    rw [hprog, loadProgram_at_index base _ 2 (by simp) (by omega)]; simp
  have hstep3 : step (loadProgram base (swap .x10 .x11 .x5)) s2 =
      some (execInstrBr s2 (Instr.MV .x11 .x5)) := by simp [step, hs2_pc, hfetch2]
  let s3 := execInstrBr s2 (Instr.MV .x11 .x5)
  have hs3_pc : s3.pc = base + 12 := by
    simp only [s3, execInstrBr, MachineState.setPC, hs2_pc, BitVec.add_assoc]; rfl
  have hs3_x10 : s3.getReg .x10 = w := by
    simp [s3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs2_x10]
  have hs3_x11 : s3.getReg .x11 = v := by
    simp [s3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hs2_x5]
  have hs3_x5 : s3.getReg .x5 = v := by
    simp [s3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs2_x5]
  -- Compose 3 steps
  refine ⟨3, s3, ?_, hs3_pc, ?_⟩
  · show (step (loadProgram base (swap .x10 .x11 .x5)) s).bind
      (fun s' => (step (loadProgram base (swap .x10 .x11 .x5)) s').bind
        (fun s' => (step (loadProgram base (swap .x10 .x11 .x5)) s').bind
          (fun s' => some s'))) = some s3
    rw [hstep1, Option.bind, hstep2, Option.bind, hstep3, Option.bind]
  · -- Frame preservation: decompose hPR, chain CompatibleWith on h_R, reconstruct
    -- Decompose hPR into partial states
    obtain ⟨h_top, hcompat_top, h_P, h_R, hdisj_PR, hunion_PR, hP_part, hR_part⟩ := hPR
    obtain ⟨h_x10, h_2, hdisj_1, hunion_1, hx10_eq, h2_part⟩ := hP_part
    obtain ⟨h_x11, h_x5, hdisj_23, hunion_23, hx11_eq, hx5_eq⟩ := h2_part
    rw [regIs] at hx10_eq hx11_eq hx5_eq
    subst hx10_eq; subst hx11_eq; subst hx5_eq
    -- h_R doesn't own x10, x11, x5 (from disjointness with h_P)
    rw [← hunion_PR] at hcompat_top
    have hP_x10 : h_P.regs .x10 ≠ none := by
      rw [← hunion_1]; simp [PartialState.union, PartialState.singletonReg]
    have hP_x11 : h_P.regs .x11 ≠ none := by
      rw [← hunion_1, ← hunion_23]
      simp [PartialState.union, PartialState.singletonReg]
    have hP_x5 : h_P.regs .x5 ≠ none := by
      rw [← hunion_1, ← hunion_23]
      simp [PartialState.union, PartialState.singletonReg]
    have hr_x10 : h_R.regs .x10 = none := by
      rcases hdisj_PR.1 .x10 with h | h; exact absurd h hP_x10; exact h
    have hr_x11 : h_R.regs .x11 = none := by
      rcases hdisj_PR.1 .x11 with h | h; exact absurd h hP_x11; exact h
    have hr_x5 : h_R.regs .x5 = none := by
      rcases hdisj_PR.1 .x5 with h | h; exact absurd h hP_x5; exact h
    have hpc_R : h_R.pc = none := hR h_R hR_part
    -- h_R compatible with s3 via chain of setReg + setPC
    have hcompat_R : h_R.CompatibleWith s := by
      exact ((PartialState.CompatibleWith_union hdisj_PR).mp hcompat_top).2
    have hcompat_R_s3 : h_R.CompatibleWith s3 := by
      apply PartialState.CompatibleWith_setPC _ hpc_R
      apply PartialState.CompatibleWith_setReg _ hr_x11
      apply PartialState.CompatibleWith_setPC _ hpc_R
      apply PartialState.CompatibleWith_setReg _ hr_x10
      apply PartialState.CompatibleWith_setPC _ hpc_R
      exact PartialState.CompatibleWith_setReg hcompat_R hr_x5
    -- Build Q's partial state: same shape, new values
    let h_Q := (PartialState.singletonReg .x10 w).union
               ((PartialState.singletonReg .x11 v).union (PartialState.singletonReg .x5 v))
    -- Disjointness: h_Q and h_R (same register ownership as h_P)
    have hdisj_QR : h_Q.Disjoint h_R := by
      refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
      · simp only [h_Q, PartialState.union, PartialState.singletonReg]
        cases r <;> simp
        all_goals first | exact hr_x10 | exact hr_x11 | exact hr_x5
      · exact fun a => Or.inl (by simp [h_Q, PartialState.union, PartialState.singletonReg])
      · exact Or.inl (by simp [h_Q, PartialState.union, PartialState.singletonReg])
      · exact Or.inl (by simp [h_Q, PartialState.union, PartialState.singletonReg])
      · exact Or.inl (by simp [h_Q, PartialState.union, PartialState.singletonReg])
    -- h_Q compatible with s3
    have hcompat_Q : h_Q.CompatibleWith s3 := by
      refine ⟨fun r val hr => ?_, fun a val ha => ?_, fun val hp => ?_,
              fun val hp => ?_, fun val hp => ?_⟩
      · simp only [h_Q, PartialState.union, PartialState.singletonReg] at hr
        cases r <;> simp_all <;> first | exact hs3_x10 | exact hs3_x11 | exact hs3_x5
      · simp [h_Q, PartialState.union, PartialState.singletonReg] at ha
      · simp [h_Q, PartialState.union, PartialState.singletonReg] at hp
      · simp [h_Q, PartialState.union, PartialState.singletonReg] at hp
      · simp [h_Q, PartialState.union, PartialState.singletonReg] at hp
    -- Q h_Q : the assertion (x10↦w ** x11↦v ** x5↦v) holds for h_Q
    have hQ_part : ((.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v) ** (.x5 ↦ᵣ v)) h_Q := by
      refine ⟨PartialState.singletonReg .x10 w,
              (PartialState.singletonReg .x11 v).union (PartialState.singletonReg .x5 v),
              ?_, rfl, rfl, PartialState.singletonReg .x11 v, PartialState.singletonReg .x5 v,
              ?_, rfl, rfl, rfl⟩
      · refine ⟨fun r => ?_, fun a => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
        simp [PartialState.union, PartialState.singletonReg]
        cases r <;> simp
      · refine ⟨fun r => ?_, fun a => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
        simp [PartialState.singletonReg]; cases r <;> simp
    -- Combine into (Q ** R).holdsFor s3
    exact ⟨h_Q.union h_R,
           (PartialState.CompatibleWith_union hdisj_QR).mpr ⟨hcompat_Q, hcompat_R_s3⟩,
           h_Q, h_R, hdisj_QR, rfl, hQ_part, hR_part⟩

end RiscVMacroAsm.Examples
