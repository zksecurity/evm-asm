/-
  EvmAsm.CPSSpec

  CPS-style (continuation-passing style) Hoare triples for branching code,
  with a built-in frame rule.

  Following Jensen/Benton/Kennedy (POPL 2013, PPDP 2013), we specify code
  with multiple exits using CPS-style specifications:
  "if it is safe to continue at each exit point, then it is safe to enter."

  The frame rule is baked into the definitions: all specs universally
  quantify over a pcFree frame R, so P/Q only describe the resources
  the code actually reads/writes.

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

import EvmAsm.Basic
import EvmAsm.SepLogic
import EvmAsm.Execution

namespace EvmAsm

-- ============================================================================
-- CPS-style specifications (with built-in frame rule)
-- ============================================================================

/-- CPS-style code specification with built-in frame rule:
    For any pcFree frame R, starting from any state where (P ** R) holds
    and PC = entry, execution reaches a state where (Q ** R) holds and PC = exit.

    The universal quantification over R means P and Q only describe the
    resources the code actually reads/writes. -/
def cpsTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- CPS spec for code with two exits (the branch pattern) with built-in frame:
    "For any pcFree frame R, if (P ** R) holds at entry, execution reaches
     EITHER exit_t with (Q_t ** R) OR exit_f with (Q_f ** R)." -/
def cpsBranch (code : CodeMem) (entry : Addr) (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨ (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (code : CodeMem) (l1 l2 l3 : Addr)
    (P Q R : Assertion)
    (h1 : cpsTriple code l1 l2 P Q)
    (h2 : cpsTriple code l2 l3 Q R) :
    cpsTriple code l1 l3 P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen precondition and weaken postcondition.
    Note: implications are at the assertion (PartialState) level, not holdsFor level,
    because (P' ** R).holdsFor s → (P ** R).holdsFor s requires P' h → P h pointwise. -/
theorem cpsTriple_consequence (code : CodeMem) (entry exit_ : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ P' Q' := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

-- ============================================================================
-- regOwn / memOwn lifting helpers
-- ============================================================================

/-- Lift a spec quantified over v_old to one with regOwn in tail position:
    (∀ v_old, cpsTriple ... (P ** (r ↦ᵣ v_old)) Q) → cpsTriple ... (P ** regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn
    {code entry exit_ r P Q}
    (h : ∀ v_old, cpsTriple code entry exit_ (P ** (r ↦ᵣ v_old)) Q) :
    cpsTriple code entry exit_ (P ** regOwn r) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with regOwn as entire precondition:
    (∀ v_old, cpsTriple ... (r ↦ᵣ v_old) Q) → cpsTriple ... (regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn_single
    {code entry exit_ r Q}
    (h : ∀ v_old, cpsTriple code entry exit_ (r ↦ᵣ v_old) Q) :
    cpsTriple code entry exit_ (regOwn r) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, ⟨v_old, hv⟩, hR2⟩ := hPR
  exact h v_old R hR s ⟨hp, hcompat, h1, h2, hd, hunion, hv, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with memOwn in tail position:
    (∀ v_old, cpsTriple ... (P ** (a ↦ₘ v_old)) Q) → cpsTriple ... (P ** memOwn a) Q -/
theorem cpsTriple_of_forall_memIs_to_memOwn
    {code entry exit_ a P Q}
    (h : ∀ v_old, cpsTriple code entry exit_ (P ** (a ↦ₘ v_old)) Q) :
    cpsTriple code entry exit_ (P ** memOwn a) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Branch elimination: if both branch exits lead to the same
    continuation exit with R, merge back into a single cpsTriple. -/
theorem cpsBranch_merge (code : CodeMem) (entry l_t l_f exit_ : Addr)
    (P Q_t Q_f R : Assertion)
    (hbr   : cpsBranch code entry P l_t Q_t l_f Q_f)
    (h_t   : cpsTriple code l_t exit_ Q_t R)
    (h_f   : cpsTriple code l_f exit_ Q_f R) :
    cpsTriple code entry exit_ P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr F hF s hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hQ_t hpc_t
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- A cpsTriple with zero steps: if entry = exit and P implies Q, trivially holds. -/
theorem cpsTriple_refl (code : CodeMem) (addr : Addr) (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsTriple code addr addr P Q := by
  intro R hR s hPR hpc
  exact ⟨0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

-- ============================================================================
-- N-exit CPS specifications
-- ============================================================================

/-- CPS spec for code with N exits with built-in frame rule:
    "For any pcFree frame R, if (P ** R) holds at entry, execution reaches
    some exit in the list, with (exit.2 ** R) holding."

    Generalizes `cpsBranch` from 2 exits to an arbitrary list. -/
def cpsNBranch (code : CodeMem) (entry : Addr) (P : Assertion)
    (exits : List (Addr × Assertion)) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ (exit.2 ** R).holdsFor s'

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit). -/
theorem cpsNBranch_nil_false (code : CodeMem) (entry : Addr) (P : Assertion)
    (h : cpsNBranch code entry P [])
    (s : MachineState) (hP : P.holdsFor s) (hpc : s.pc = entry) : False := by
  -- Use empAssertion as the frame
  have hPemp : (P ** empAssertion).holdsFor s := by
    obtain ⟨hp, hcompat, hph⟩ := hP
    exact ⟨hp, hcompat, hp, PartialState.empty, PartialState.Disjoint_empty_right hp,
           PartialState.union_empty_right hp, hph, rfl⟩
  obtain ⟨k, s', _, ex, hmem, _, _⟩ := h empAssertion pcFree_emp s hPemp hpc
  exact List.not_mem_nil hmem

/-- An N-branch with impossible precondition vacuously holds for any exits. -/
theorem cpsNBranch_nil_of_false (code : CodeMem) (entry : Addr) :
    cpsNBranch code entry (fun _ => False) [] := by
  intro R _ s ⟨_, _, h1, h2, _, _, hf, _⟩ _
  exact absurd hf id

/-- Reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranch_refl (code : CodeMem) (addr : Addr)
    (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsNBranch code addr P [(addr, Q)] := by
  intro R hR s hPR hpc
  exact ⟨0, s, rfl, (addr, Q), List.Mem.head _, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

-- ============================================================================
-- Equivalences with existing types
-- ============================================================================

/-- A single-exit cpsTriple can be viewed as a cpsNBranch with one exit. -/
theorem cpsTriple_to_cpsNBranch (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsTriple code entry exit_ P Q) :
    cpsNBranch code entry P [(exit_, Q)] := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQR⟩

/-- A singleton cpsNBranch gives back a cpsTriple. -/
theorem cpsNBranch_to_cpsTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsNBranch code entry P [(exit_, Q)]) :
    cpsTriple code entry exit_ P Q := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
  cases hmem with
  | head => exact ⟨k, s', hstep, hpc', hQR⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A 2-exit cpsBranch can be viewed as a cpsNBranch with two exits. -/
theorem cpsBranch_to_cpsNBranch (code : CodeMem) (entry : Addr)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsBranch code entry P exit_t Q_t exit_f Q_f) :
    cpsNBranch code entry P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hPR hpc
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
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
  refine ⟨k, s', hstep, ?_⟩
  cases hmem with
  | head => left; exact ⟨hpc', hQR⟩
  | tail _ htail =>
    cases htail with
    | head => right; exact ⟨hpc', hQR⟩
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
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hall ex hmem F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen the precondition of an N-branch. -/
theorem cpsNBranch_weaken_pre (code : CodeMem) (entry : Addr)
    (P P' : Assertion)
    (exits : List (Addr × Assertion))
    (hpre : ∀ h, P' h → P h) (h : cpsNBranch code entry P exits) :
    cpsNBranch code entry P' exits := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hPR hpc

/-- Monotonicity: expand the exit list (weaken the exit constraint). -/
theorem cpsNBranch_weaken_exits (code : CodeMem) (entry : Addr)
    (P : Assertion)
    (exits exits' : List (Addr × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranch code entry P exits) :
    cpsNBranch code entry P exits' := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, ex, hsub ex hmem, hpc', hQR⟩

/-- Extend the head exit by composing a cpsTriple after it. -/
theorem cpsNBranch_extend_head (code : CodeMem) (entry l l' : Addr)
    (P Q R : Assertion)
    (others : List (Addr × Assertion))
    (hbr : cpsNBranch code entry P ((l, Q) :: others))
    (hseq : cpsTriple code l l' Q R) :
    cpsNBranch code entry P ((l', R) :: others) := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hPF hpc
  cases hmem with
  | head =>
    -- ex = (l, Q), compose with hseq
    obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hseq F hF s1 hQF hpc1
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2,
           (l', R), List.Mem.head _, hpc2, hRF⟩
  | tail _ htail =>
    -- ex ∈ others, pass through
    exact ⟨k1, s1, hstep1, ex, List.Mem.tail _ htail, hpc1, hQF⟩

-- ============================================================================
-- Halt-aware CPS specifications
-- ============================================================================

/-- A state is halted when `step` returns `none` (HALT syscall or no instruction). -/
def isHalted (code : CodeMem) (s : MachineState) : Bool :=
  (step code s).isNone

/-- CPS-style halt specification with built-in frame rule:
    For any pcFree frame R, starting from any state where (P ** R) holds
    and PC = entry, execution reaches a halted state where (Q ** R) holds.
    Unlike `cpsTriple`, there is no exit address — execution simply terminates. -/
def cpsHaltTriple (code : CodeMem) (entry : Addr)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k code s = some s' ∧ isHalted code s' = true ∧ (Q ** R).holdsFor s'

/-- Promote a `cpsTriple` to a `cpsHaltTriple` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying (Q ** R) at exit_ is halted,
    then the program halts with Q. -/
theorem cpsTriple_to_cpsHaltTriple (code : CodeMem) (entry exit_ : Addr)
    (P Q : Assertion)
    (h : cpsTriple code entry exit_ P Q)
    (hhalt : ∀ (R : Assertion), R.pcFree → ∀ s, (Q ** R).holdsFor s → s.pc = exit_ →
      isHalted code s = true) :
    cpsHaltTriple code entry P Q := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hhalt R hR s' hQR hpc', hQR⟩

/-- Consequence: strengthen precondition and weaken postcondition of a halt triple. -/
theorem cpsHaltTriple_consequence (code : CodeMem) (entry : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry P' Q' := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hhalt, by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Sequence a `cpsTriple` followed by a `cpsHaltTriple`:
    if code reaches midpoint with Q, and from midpoint it halts with R, then
    the composition halts with R. -/
theorem cpsTriple_seq_halt (code : CodeMem) (entry mid : Addr)
    (P Q R : Assertion)
    (h1 : cpsTriple code entry mid P Q)
    (h2 : cpsHaltTriple code mid Q R) :
    cpsHaltTriple code entry P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 code s s1 s2 hstep1 hstep2, hhalt, hRF⟩

/-- Sequential composition with midpoint permutation:
    compose h1 : cpsTriple code s m P Q1 with h2 : cpsTriple code m e Q2 R
    when Q1 and Q2 are AC-permutations (proved by hperm).
    Both Q1 and Q2 are fully determined by h1/h2, so the permutation
    obligation has no metavar ambiguity. -/
theorem cpsTriple_seq_with_perm (code : CodeMem) (s m e : Addr)
    (P Q1 Q2 R : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple code s m P Q1)
    (h2 : cpsTriple code m e Q2 R) :
    cpsTriple code s e P R :=
  cpsTriple_seq code s m e P Q2 R
    (cpsTriple_consequence code s m P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

end EvmAsm
