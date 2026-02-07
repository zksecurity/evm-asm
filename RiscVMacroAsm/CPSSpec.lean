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

  All assertions are `Assertion` (predicates on PartialState), bridged to
  MachineState via `holdsFor`.
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
  ∀ s, P.holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧ s'.pc = exit_ ∧ Q.holdsFor s'

/-- CPS spec for code with two exits (the branch pattern):
    "If P holds at entry, execution reaches EITHER exit_t with Q_t
     OR exit_f with Q_f." -/
def cpsBranch (code : CodeMem) (entry : Addr) (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion) : Prop :=
  ∀ s, P.holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧
      ((s'.pc = exit_t ∧ Q_t.holdsFor s') ∨ (s'.pc = exit_f ∧ Q_f.holdsFor s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (code : CodeMem) (l1 l2 l3 : Addr)
    (P Q R : Assertion)
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
    (hpre  : ∀ s, P'.holdsFor s → P.holdsFor s)
    (hpost : ∀ s, Q.holdsFor s → Q'.holdsFor s)
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
    (h : ∀ s, P.holdsFor s → Q.holdsFor s) :
    cpsTriple code addr addr P Q := by
  intro s hP hpc
  exact ⟨0, s, rfl, hpc, h s hP⟩

-- ============================================================================
-- N-exit CPS specifications
-- ============================================================================

/-- CPS spec for code with N exits: "If P holds at entry, execution reaches
    some exit in the list, with its associated assertion holding."

    Generalizes `cpsBranch` from 2 exits to an arbitrary list. -/
def cpsNBranch (code : CodeMem) (entry : Addr) (P : Assertion)
    (exits : List (Addr × Assertion)) : Prop :=
  ∀ s, P.holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ exit.2.holdsFor s'

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit). -/
theorem cpsNBranch_nil_false (code : CodeMem) (entry : Addr) (P : Assertion)
    (h : cpsNBranch code entry P [])
    (s : MachineState) (hP : P.holdsFor s) (hpc : s.pc = entry) : False := by
  obtain ⟨k, s', _, ex, hmem, _, _⟩ := h s hP hpc
  exact List.not_mem_nil hmem

/-- An N-branch with impossible precondition vacuously holds for any exits. -/
theorem cpsNBranch_nil_of_false (code : CodeMem) (entry : Addr) :
    cpsNBranch code entry (fun _ => False) [] := by
  intro s hP _
  exfalso; exact hP.elim (fun _ ⟨_, h⟩ => h)

/-- Reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranch_refl (code : CodeMem) (addr : Addr)
    (P Q : Assertion)
    (h : ∀ s, P.holdsFor s → Q.holdsFor s) :
    cpsNBranch code addr P [(addr, Q)] := by
  intro s hP hpc
  exact ⟨0, s, rfl, (addr, Q), List.Mem.head _, hpc, h s hP⟩

-- ============================================================================
-- Equivalences with existing types
-- ============================================================================

/-- A single-exit cpsTriple can be viewed as a cpsNBranch with one exit. -/
theorem cpsTriple_to_cpsNBranch (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsTriple code entry exit_ P Q) :
    cpsNBranch code entry P [(exit_, Q)] := by
  intro s hP hpc
  obtain ⟨k, s', hstep, hpc', hQ⟩ := h s hP hpc
  exact ⟨k, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQ⟩

/-- A singleton cpsNBranch gives back a cpsTriple. -/
theorem cpsNBranch_to_cpsTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsNBranch code entry P [(exit_, Q)]) :
    cpsTriple code entry exit_ P Q := by
  intro s hP hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQ⟩ := h s hP hpc
  cases hmem with
  | head => exact ⟨k, s', hstep, hpc', hQ⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A 2-exit cpsBranch can be viewed as a cpsNBranch with two exits. -/
theorem cpsBranch_to_cpsNBranch (code : CodeMem) (entry : Addr)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsBranch code entry P exit_t Q_t exit_f Q_f) :
    cpsNBranch code entry P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro s hP hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h s hP hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k, s', hstep, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · exact ⟨k, s', hstep, (exit_f, Q_f), List.Mem.tail _ (List.Mem.head _), hpc_f, hQ_f⟩

/-- A 2-element cpsNBranch gives back a cpsBranch. -/
theorem cpsNBranch_to_cpsBranch (code : CodeMem) (entry : Addr)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsNBranch code entry P [(exit_t, Q_t), (exit_f, Q_f)]) :
    cpsBranch code entry P exit_t Q_t exit_f Q_f := by
  intro s hP hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQ⟩ := h s hP hpc
  refine ⟨k, s', hstep, ?_⟩
  cases hmem with
  | head => left; exact ⟨hpc', hQ⟩
  | tail _ htail =>
    cases htail with
    | head => right; exact ⟨hpc', hQ⟩
    | tail _ h => exact absurd h List.not_mem_nil

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- N-branch merge: if every exit leads to the same continuation,
    compose into a single cpsTriple. This is the main structural rule. -/
theorem cpsNBranch_merge (code : CodeMem) (entry exit_ : Addr)
    (P R : Assertion)
    (exits : List (Addr × Assertion))
    (hbr : cpsNBranch code entry P exits)
    (hall : ∀ exit ∈ exits, cpsTriple code exit.1 exit_ exit.2 R) :
    cpsTriple code entry exit_ P R := by
  intro s hP hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQ⟩ := hbr s hP hpc
  obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := hall ex hmem s1 hQ hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- Consequence: strengthen the precondition of an N-branch. -/
theorem cpsNBranch_weaken_pre (code : CodeMem) (entry : Addr)
    (P P' : Assertion)
    (exits : List (Addr × Assertion))
    (hpre : ∀ s, P'.holdsFor s → P.holdsFor s) (h : cpsNBranch code entry P exits) :
    cpsNBranch code entry P' exits := by
  intro s hP' hpc
  exact h s (hpre s hP') hpc

/-- Monotonicity: expand the exit list (weaken the exit constraint). -/
theorem cpsNBranch_weaken_exits (code : CodeMem) (entry : Addr)
    (P : Assertion)
    (exits exits' : List (Addr × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranch code entry P exits) :
    cpsNBranch code entry P exits' := by
  intro s hP hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQ⟩ := h s hP hpc
  exact ⟨k, s', hstep, ex, hsub ex hmem, hpc', hQ⟩

/-- Extend the head exit by composing a cpsTriple after it. -/
theorem cpsNBranch_extend_head (code : CodeMem) (entry l l' : Addr)
    (P Q R : Assertion)
    (others : List (Addr × Assertion))
    (hbr : cpsNBranch code entry P ((l, Q) :: others))
    (hseq : cpsTriple code l l' Q R) :
    cpsNBranch code entry P ((l', R) :: others) := by
  intro s hP hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQ⟩ := hbr s hP hpc
  cases hmem with
  | head =>
    -- ex = (l, Q), compose with hseq
    obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := hseq s1 hQ hpc1
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2,
           (l', R), List.Mem.head _, hpc2, hR⟩
  | tail _ htail =>
    -- ex ∈ others, pass through
    exact ⟨k1, s1, hstep1, ex, List.Mem.tail _ htail, hpc1, hQ⟩

-- ============================================================================
-- Halt-aware CPS specifications
-- ============================================================================

/-- A state is halted when `step` returns `none` (HALT syscall or no instruction). -/
def isHalted (code : CodeMem) (s : MachineState) : Bool :=
  (step code s).isNone

/-- CPS-style halt specification: starting from any state where P holds
    and PC = entry, execution reaches a halted state where Q holds.
    Unlike `cpsTriple`, there is no exit address — execution simply terminates. -/
def cpsHaltTriple (code : CodeMem) (entry : Addr)
    (P Q : Assertion) : Prop :=
  ∀ s, P.holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧ isHalted code s' = true ∧ Q.holdsFor s'

/-- Promote a `cpsTriple` to a `cpsHaltTriple` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying Q at exit_ is halted,
    then the program halts with Q. -/
theorem cpsTriple_to_cpsHaltTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion)
    (h : cpsTriple code entry exit_ P Q)
    (hhalt : ∀ s, Q.holdsFor s → s.pc = exit_ → isHalted code s = true) :
    cpsHaltTriple code entry P Q := by
  intro s hP hpc
  obtain ⟨k, s', hstep, hpc', hQ⟩ := h s hP hpc
  exact ⟨k, s', hstep, hhalt s' hQ hpc', hQ⟩

/-- Consequence: strengthen precondition and weaken postcondition of a halt triple. -/
theorem cpsHaltTriple_consequence (code : CodeMem) (entry : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ s, P'.holdsFor s → P.holdsFor s)
    (hpost : ∀ s, Q.holdsFor s → Q'.holdsFor s)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry P' Q' := by
  intro s hP' hpc
  obtain ⟨k, s', hstep, hhalt, hQ⟩ := h s (hpre s hP') hpc
  exact ⟨k, s', hstep, hhalt, hpost s' hQ⟩

/-- Sequence a `cpsTriple` followed by a `cpsHaltTriple`:
    if code reaches midpoint with Q, and from midpoint it halts with R, then
    the composition halts with R. -/
theorem cpsTriple_seq_halt (code : CodeMem) (entry mid : Addr)
    (P Q R : Assertion)
    (h1 : cpsTriple code entry mid P Q)
    (h2 : cpsHaltTriple code mid Q R) :
    cpsHaltTriple code entry P R := by
  intro s hP hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQ⟩ := h1 s hP hpc
  obtain ⟨k2, s2, hstep2, hhalt, hR⟩ := h2 s1 hQ hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hhalt, hR⟩

end RiscVMacroAsm
