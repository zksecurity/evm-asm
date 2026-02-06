/-
  RiscVMacroAsm.Spec

  Hoare-triple specifications for programs.

  Following Kennedy et al. (2013), we provide:
  - A basic Hoare triple {P} prog {Q} meaning: if P holds before
    executing prog, then Q holds after.
  - A frame rule: specifications are local and compose with
    unrelated resources.
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.Program
import RiscVMacroAsm.SepLogic

namespace RiscVMacroAsm

-- ============================================================================
-- Hoare Triples
-- ============================================================================

/-- A Hoare triple: {P} prog {Q} means that if P holds on state s,
    then Q holds on (execProgram s prog). -/
def basic (P : Assertion) (prog : Program) (Q : Assertion) : Prop :=
  ∀ s : MachineState, P s → Q (execProgram s prog)

/-- Notation for Hoare triples. -/
notation:25 "⦃" P "⦄ " prog " ⦃" Q "⦄" => basic P prog Q

-- ============================================================================
-- Structural Rules
-- ============================================================================

/-- Skip rule: {P} skip {P} -/
theorem basic_skip (P : Assertion) : ⦃P⦄ prog_skip ⦃P⦄ := by
  intro s hp
  simp [prog_skip, execProgram]
  exact hp

/-- Sequence rule: {P} p1 {Q} → {Q} p2 {R} → {P} p1;;p2 {R} -/
theorem basic_seq (P Q R : Assertion) (p1 p2 : Program)
    (h1 : ⦃P⦄ p1 ⦃Q⦄) (h2 : ⦃Q⦄ p2 ⦃R⦄) :
    ⦃P⦄ (p1 ;; p2) ⦃R⦄ := by
  intro s hp
  rw [execProgram_seq]
  exact h2 _ (h1 _ hp)

/-- Consequence rule: strengthen precondition and/or weaken postcondition. -/
theorem basic_consequence (P P' Q Q' : Assertion) (prog : Program)
    (hpre  : ∀ s, P' s → P s)
    (hpost : ∀ s, Q s → Q' s)
    (h : ⦃P⦄ prog ⦃Q⦄) :
    ⦃P'⦄ prog ⦃Q'⦄ := by
  intro s hp'
  exact hpost _ (h _ (hpre _ hp'))

/-- Frame rule: {P} prog {Q} → {P ** R} prog {Q ** R}

    This holds because our instructions only modify the resources they
    explicitly write to, and the frame R talks about unmodified resources.

    In general, this needs a side condition that prog does not modify the
    resources in R. We state it with an explicit non-interference hypothesis. -/
theorem basic_frame (P Q R : Assertion) (prog : Program)
    (h : ⦃P⦄ prog ⦃Q⦄)
    (hframe : ∀ s, R s → R (execProgram s prog)) :
    ⦃P ** R⦄ prog ⦃Q ** R⦄ := by
  intro s ⟨hp, hr⟩
  exact ⟨h s hp, hframe s hr⟩

/-- Existential rule: if {P x} prog {Q x} for all x, then
    {∃ x, P x} prog {∃ x, Q x}. -/
theorem basic_exists {α : Type} (P Q : α → Assertion) (prog : Program)
    (h : ∀ x, ⦃P x⦄ prog ⦃Q x⦄) :
    ⦃aExists P⦄ prog ⦃aExists Q⦄ := by
  intro s ⟨a, hp⟩
  exact ⟨a, h a s hp⟩

-- ============================================================================
-- Conjunction Rule
-- ============================================================================

/-- Conjunction: {P₁} prog {Q₁} → {P₂} prog {Q₂} → {P₁ ** P₂} prog {Q₁ ** Q₂} -/
theorem basic_conj (P₁ Q₁ P₂ Q₂ : Assertion) (prog : Program)
    (h1 : ⦃P₁⦄ prog ⦃Q₁⦄) (h2 : ⦃P₂⦄ prog ⦃Q₂⦄) :
    ⦃P₁ ** P₂⦄ prog ⦃Q₁ ** Q₂⦄ := by
  intro s ⟨hp1, hp2⟩
  exact ⟨h1 s hp1, h2 s hp2⟩

end RiscVMacroAsm
