/-
  RiscVMacroAsm.CPSSpec

  CPS-style (continuation-passing style) Hoare triples for branching code.

  Following Jensen/Benton/Kennedy (POPL 2013, PPDP 2013), we specify code
  with multiple exits using CPS-style specifications:
  "if it is safe to continue at each exit point, then it is safe to enter."

  Key types:
  - cpsTriple: single-exit specification (entry → exit with P → Q)
  - cpsBranch: two-exit specification (entry → exit_t with Q_t OR exit_f with Q_f)

  Structural rules:
  - cpsTriple_seq: sequential composition
  - cpsTriple_consequence: pre/post strengthening/weakening
  - cpsBranch_merge: merge two branch exits into a single continuation
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution

namespace RiscVMacroAsm

-- ============================================================================
-- CPS-style specifications
-- ============================================================================

/-- CPS-style code specification: starting from any state where P holds
    and PC = entry, execution reaches a state where Q holds and PC = exit.

    The existential step count makes this a partial-correctness-like spec
    (we assert termination but don't bound it tightly). -/
def cpsTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) : Prop :=
  ∀ s, P s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧ s'.pc = exit_ ∧ Q s'

/-- CPS spec for code with two exits (the branch pattern):
    "If P holds at entry, execution reaches EITHER exit_t with Q_t
     OR exit_f with Q_f." -/
def cpsBranch (code : CodeMem) (entry : Addr) (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion) : Prop :=
  ∀ s, P s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧
      ((s'.pc = exit_t ∧ Q_t s') ∨ (s'.pc = exit_f ∧ Q_f s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (code : CodeMem) (l1 l2 l3 : Addr) (P Q R : Assertion)
    (h1 : cpsTriple code l1 l2 P Q)
    (h2 : cpsTriple code l2 l3 Q R) :
    cpsTriple code l1 l3 P R := by
  intro s hP hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQ⟩ := h1 s hP hpc
  obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h2 s1 hQ hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- Consequence: strengthen precondition and weaken postcondition. -/
theorem cpsTriple_consequence (code : CodeMem) (entry exit_ : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ s, P' s → P s)
    (hpost : ∀ s, Q s → Q' s)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ P' Q' := by
  intro s hP' hpc
  obtain ⟨k, s', hstep, hpc', hQ⟩ := h s (hpre s hP') hpc
  exact ⟨k, s', hstep, hpc', hpost s' hQ⟩

/-- Branch elimination: if both branch exits lead to the same
    continuation exit with R, merge back into a single cpsTriple. -/
theorem cpsBranch_merge (code : CodeMem) (entry l_t l_f exit_ : Addr)
    (P Q_t Q_f R : Assertion)
    (hbr   : cpsBranch code entry P l_t Q_t l_f Q_f)
    (h_t   : cpsTriple code l_t exit_ Q_t R)
    (h_f   : cpsTriple code l_f exit_ Q_f R) :
    cpsTriple code entry exit_ P R := by
  intro s hP hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr s hP hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t s1 hQ_t hpc_t
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f s1 hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- A cpsTriple with zero steps: if entry = exit and P implies Q, trivially holds. -/
theorem cpsTriple_refl (code : CodeMem) (addr : Addr) (P Q : Assertion)
    (h : ∀ s, P s → Q s) :
    cpsTriple code addr addr P Q := by
  intro s hP hpc
  exact ⟨0, s, rfl, hpc, h s hP⟩

end RiscVMacroAsm
