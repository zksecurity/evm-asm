/-
  RiscVMacroAsm.SepLogic

  Real separation logic with PartialState (partial register + memory + PC maps).

  Following Kennedy et al. (2013), we treat registers, memory locations, and the
  program counter as separable resources. An assertion is a predicate on partial
  states. The separating conjunction (P ** Q) holds when the partial state can be
  split into two disjoint sub-states satisfying P and Q respectively.

  The bridge to full machine states is via `holdsFor`: an assertion holds for a
  machine state when there exists a compatible partial state satisfying it.
-/

import RiscVMacroAsm.Basic

namespace RiscVMacroAsm

-- ============================================================================
-- PartialState: partial register + memory + PC maps
-- ============================================================================

/-- A partial state tracks ownership of registers, memory, and optionally the PC.
    Each field is an option: `some v` means "we own this resource and it has value v",
    `none` means "we don't own this resource". -/
structure PartialState where
  regs : Reg → Option Word
  mem  : Addr → Option Word
  pc   : Option Word
  publicValues : Option (List Word) := none
  privateInput : Option (List Word) := none

namespace PartialState

/-- The empty partial state: owns nothing. -/
def empty : PartialState := ⟨fun _ => none, fun _ => none, none, none, none⟩

/-- A partial state owning just one register. -/
def singletonReg (r : Reg) (v : Word) : PartialState where
  regs := fun r' => if r' == r then some v else none
  mem  := fun _ => none
  pc   := none
  publicValues := none
  privateInput := none

/-- A partial state owning just one memory cell. -/
def singletonMem (a : Addr) (v : Word) : PartialState where
  regs := fun _ => none
  mem  := fun a' => if a' == a then some v else none
  pc   := none
  publicValues := none
  privateInput := none

/-- A partial state owning just the PC. -/
def singletonPC (v : Word) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  pc   := some v
  publicValues := none
  privateInput := none

/-- A partial state owning just the public values. -/
def singletonPublicValues (vals : List Word) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  pc   := none
  publicValues := some vals
  privateInput := none

/-- A partial state owning just the private input. -/
def singletonPrivateInput (vals : List Word) : PartialState where
  regs := fun _ => none
  mem  := fun _ => none
  pc   := none
  publicValues := none
  privateInput := some vals

/-- Two partial states are disjoint if they don't own the same resources. -/
def Disjoint (h1 h2 : PartialState) : Prop :=
  (∀ r, h1.regs r = none ∨ h2.regs r = none) ∧
  (∀ a, h1.mem a = none ∨ h2.mem a = none) ∧
  (h1.pc = none ∨ h2.pc = none) ∧
  (h1.publicValues = none ∨ h2.publicValues = none) ∧
  (h1.privateInput = none ∨ h2.privateInput = none)

/-- Merge two partial states (left-biased on each resource). -/
def union (h1 h2 : PartialState) : PartialState where
  regs := fun r => match h1.regs r with | some v => some v | none => h2.regs r
  mem  := fun a => match h1.mem a with | some v => some v | none => h2.mem a
  pc   := match h1.pc with | some v => some v | none => h2.pc
  publicValues := match h1.publicValues with | some v => some v | none => h2.publicValues
  privateInput := match h1.privateInput with | some v => some v | none => h2.privateInput

/-- A partial state is compatible with a machine state if every owned
    resource has the correct value. -/
def CompatibleWith (h : PartialState) (s : MachineState) : Prop :=
  (∀ r v, h.regs r = some v → s.getReg r = v) ∧
  (∀ a v, h.mem a = some v → s.getMem a = v) ∧
  (∀ v, h.pc = some v → s.pc = v) ∧
  (∀ v, h.publicValues = some v → s.publicValues = v) ∧
  (∀ v, h.privateInput = some v → s.privateInput = v)

-- ============================================================================
-- Disjoint lemmas
-- ============================================================================

theorem Disjoint.symm {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h2.Disjoint h1 := by
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hd
  exact ⟨fun r => (hr r).symm, fun a => (hm a).symm, hpc.symm, hpv.symm, hpi.symm⟩

theorem Disjoint_empty_left (h : PartialState) : empty.Disjoint h := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem Disjoint_empty_right (h : PartialState) : h.Disjoint empty := by
  exact (Disjoint_empty_left h).symm

-- ============================================================================
-- Union lemmas
-- ============================================================================

theorem union_empty_left (h : PartialState) : empty.union h = h := by
  simp [union, empty]

theorem union_empty_right (h : PartialState) : h.union empty = h := by
  simp only [union, empty]
  obtain ⟨regs, mem, pc, publicValues, privateInput⟩ := h
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases regs r <;> rfl
  · funext a; cases mem a <;> rfl
  · cases pc <;> rfl
  · cases publicValues <;> rfl
  · cases privateInput <;> rfl

theorem union_comm_of_disjoint {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h1.union h2 = h2.union h1 := by
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hd
  simp only [union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r
    cases hv1 : h1.regs r <;> cases hv2 : h2.regs r <;> simp
    · have := hr r; rw [hv1, hv2] at this; simp at this
  · funext a
    cases hv1 : h1.mem a <;> cases hv2 : h2.mem a <;> simp
    · have := hm a; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.pc <;> cases hv2 : h2.pc <;> simp
    · have := hpc; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.publicValues <;> cases hv2 : h2.publicValues <;> simp
    · have := hpv; rw [hv1, hv2] at this; simp at this
  · cases hv1 : h1.privateInput <;> cases hv2 : h2.privateInput <;> simp
    · have := hpi; rw [hv1, hv2] at this; simp at this

-- ============================================================================
-- CompatibleWith lemmas
-- ============================================================================

theorem CompatibleWith_empty (s : MachineState) : empty.CompatibleWith s := by
  exact ⟨fun _ _ h => by simp [empty] at h, fun _ _ h => by simp [empty] at h,
         fun _ h => by simp [empty] at h, fun _ h => by simp [empty] at h,
         fun _ h => by simp [empty] at h⟩

theorem CompatibleWith_singletonReg (r : Reg) (v : Word) (s : MachineState) :
    (singletonReg r v).CompatibleWith s ↔ s.getReg r = v := by
  constructor
  · intro ⟨hr, _, _, _, _⟩
    have : (if r == r then some v else none) = some v := by simp
    exact hr r v this
  · intro heq
    refine ⟨fun r' v' h => ?_, fun _ _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h,
            fun _ h => by simp [singletonReg] at h⟩
    simp only [singletonReg] at h
    split at h
    · rename_i heq'; rw [beq_iff_eq] at heq'; subst heq'
      simp at h; rw [← h]; exact heq
    · simp at h

theorem CompatibleWith_singletonMem (a : Addr) (v : Word) (s : MachineState) :
    (singletonMem a v).CompatibleWith s ↔ s.getMem a = v := by
  constructor
  · intro ⟨_, hm, _, _, _⟩
    have : (if a == a then some v else none) = some v := by simp
    exact hm a v this
  · intro heq
    refine ⟨fun _ _ h => by simp [singletonMem] at h,
            fun a' v' h => ?_,
            fun _ h => by simp [singletonMem] at h,
            fun _ h => by simp [singletonMem] at h,
            fun _ h => by simp [singletonMem] at h⟩
    simp only [singletonMem] at h
    split at h
    · rename_i heq'; rw [beq_iff_eq] at heq'; subst heq'
      simp at h; rw [← h]; exact heq
    · simp at h

theorem CompatibleWith_singletonPC (v : Word) (s : MachineState) :
    (singletonPC v).CompatibleWith s ↔ s.pc = v := by
  constructor
  · intro ⟨_, _, hpc, _, _⟩
    exact hpc v rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPC] at h,
           fun _ _ h => by simp [singletonPC] at h,
           fun v' h => by simp [singletonPC] at h; rw [← h]; exact heq,
           fun _ h => by simp [singletonPC] at h,
           fun _ h => by simp [singletonPC] at h⟩

theorem CompatibleWith_union {h1 h2 : PartialState} {s : MachineState}
    (hd : h1.Disjoint h2) :
    (h1.union h2).CompatibleWith s ↔ h1.CompatibleWith s ∧ h2.CompatibleWith s := by
  obtain ⟨hdr, hdm, hdpc, hdpv, hdpi⟩ := hd
  constructor
  · intro ⟨hr, hm, hpc, hpv, hpi⟩
    constructor
    · refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · exact hr r v (by simp [union, hv])
      · exact hm a v (by simp [union, hv])
      · exact hpc v (by simp [union, hv])
      · exact hpv v (by simp [union, hv])
      · exact hpi v (by simp [union, hv])
    · refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · have := hdr r
        rcases this with h1none | h2none
        · exact hr r v (by show (union h1 h2).regs r = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · have := hdm a
        rcases this with h1none | h2none
        · exact hm a v (by show (union h1 h2).mem a = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpc with h1none | h2none
        · exact hpc v (by show (union h1 h2).pc = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpv with h1none | h2none
        · exact hpv v (by show (union h1 h2).publicValues = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
      · rcases hdpi with h1none | h2none
        · exact hpi v (by show (union h1 h2).privateInput = some v; simp only [union]; rw [h1none]; exact hv)
        · rw [h2none] at hv; simp at hv
  · intro ⟨⟨hr1, hm1, hpc1, hpv1, hpi1⟩, ⟨hr2, hm2, hpc2, hpv2, hpi2⟩⟩
    refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [union] at hv
      cases h1r : h1.regs r <;> simp [h1r] at hv
      · exact hr2 r v hv
      · exact hr1 r v (by rw [← hv]; exact h1r)
    · simp only [union] at hv
      cases h1m : h1.mem a <;> simp [h1m] at hv
      · exact hm2 a v hv
      · exact hm1 a v (by rw [← hv]; exact h1m)
    · simp only [union] at hv
      cases h1pc : h1.pc <;> simp [h1pc] at hv
      · exact hpc2 v hv
      · exact hpc1 v (by rw [← hv]; exact h1pc)
    · simp only [union] at hv
      cases h1pv : h1.publicValues <;> simp [h1pv] at hv
      · exact hpv2 v hv
      · exact hpv1 v (by rw [← hv]; exact h1pv)
    · simp only [union] at hv
      cases h1pi : h1.privateInput <;> simp [h1pi] at hv
      · exact hpi2 v hv
      · exact hpi1 v (by rw [← hv]; exact h1pi)

end PartialState

-- ============================================================================
-- Assertion type
-- ============================================================================

/-- An assertion is a predicate on partial states. -/
def Assertion := PartialState → Prop

instance : Inhabited Assertion := ⟨fun _ => True⟩

-- ============================================================================
-- Basic Assertions
-- ============================================================================

/-- Register r holds value v. -/
def regIs (r : Reg) (v : Word) : Assertion :=
  fun h => h = PartialState.singletonReg r v

/-- Notation: r ↦ᵣ v means register r holds value v. -/
notation:50 r " ↦ᵣ " v => regIs r v

/-- Memory at address a holds value v. -/
def memIs (a : Addr) (v : Word) : Assertion :=
  fun h => h = PartialState.singletonMem a v

/-- Notation: a ↦ₘ v means memory at address a holds value v. -/
notation:50 a " ↦ₘ " v => memIs a v

/-- PC holds value v. -/
def pcIs (v : Word) : Assertion :=
  fun h => h = PartialState.singletonPC v

/-- The empty assertion: owns no resources. -/
def empAssertion : Assertion := fun h => h = PartialState.empty

-- ============================================================================
-- Separating Conjunction
-- ============================================================================

/-- Separating conjunction: P ** Q holds on h when h can be split into
    two disjoint sub-states h1, h2 with P h1 and Q h2. -/
def sepConj (P Q : Assertion) : Assertion :=
  fun h => ∃ h1 h2, h1.Disjoint h2 ∧ h1.union h2 = h ∧ P h1 ∧ Q h2

/-- Notation: P ** Q is the separating conjunction. -/
infixr:35 " ** " => sepConj

/-- Separating implication (magic wand). -/
def sepImpl (P Q : Assertion) : Assertion :=
  fun h => ∀ h', h.Disjoint h' → P h' → Q (h.union h')

infixr:30 " -* " => sepImpl

-- ============================================================================
-- holdsFor: bridge from Assertion to MachineState
-- ============================================================================

/-- An assertion holds for a machine state when there exists a compatible
    partial state satisfying it. -/
def Assertion.holdsFor (P : Assertion) (s : MachineState) : Prop :=
  ∃ h : PartialState, h.CompatibleWith s ∧ P h

-- ============================================================================
-- pcFree: assertions that don't own the PC
-- ============================================================================

/-- An assertion is PC-free if it doesn't own/constrain the PC. -/
def Assertion.pcFree (P : Assertion) : Prop := ∀ h, P h → h.pc = none

-- ============================================================================
-- holdsFor simplification lemmas
-- ============================================================================

@[simp]
theorem holdsFor_regIs (r : Reg) (v : Word) (s : MachineState) :
    (regIs r v).holdsFor s ↔ s.getReg r = v := by
  simp only [Assertion.holdsFor, regIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonReg r v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonReg r v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_memIs (a : Addr) (v : Word) (s : MachineState) :
    (memIs a v).holdsFor s ↔ s.getMem a = v := by
  simp only [Assertion.holdsFor, memIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonMem a v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonMem a v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_pcIs (v : Word) (s : MachineState) :
    (pcIs v).holdsFor s ↔ s.pc = v := by
  simp only [Assertion.holdsFor, pcIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPC v s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPC v s).mpr heq, rfl⟩

@[simp]
theorem holdsFor_emp (s : MachineState) :
    empAssertion.holdsFor s ↔ True := by
  simp only [Assertion.holdsFor, empAssertion, iff_true]
  exact ⟨PartialState.empty, PartialState.CompatibleWith_empty s, rfl⟩

-- ============================================================================
-- holdsFor for sepConj of atoms
-- ============================================================================

private theorem singletonReg_disjoint_singletonReg {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint (PartialState.singletonReg r2 v2) := by
  refine ⟨fun r => ?_, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  simp only [PartialState.singletonReg]
  by_cases h1 : r == r1
  · simp [h1]
    by_cases h2 : r == r2
    · exfalso
      have := beq_iff_eq.mp h1
      have := beq_iff_eq.mp h2
      exact hne (by rw [← ‹r = r1›, ← ‹r = r2›])
    · exact fun hr2 => h2 (beq_iff_eq.mpr hr2)
  · simp [h1]

private theorem singletonReg_disjoint_singletonMem (r : Reg) (v : Word) (a : Addr) (w : Word) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem holdsFor_sepConj_regIs_regIs {r1 r2 : Reg} {v1 v2 : Word} {s : MachineState}
    (hne : r1 ≠ r2) :
    ((regIs r1 v1) ** (regIs r2 v2)).holdsFor s ↔ s.getReg r1 = v1 ∧ s.getReg r2 = v2 := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1 hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r1 v1 s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonReg r2 v2 s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonReg hne (v1 := v1) (v2 := v2)
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r1 v1 s).mpr h1,
       (PartialState.CompatibleWith_singletonReg r2 v2 s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

theorem holdsFor_sepConj_regIs_memIs {r : Reg} {v : Word} {a : Addr} {w : Word}
    {s : MachineState} :
    ((regIs r v) ** (memIs a w)).holdsFor s ↔ s.getReg r = v ∧ s.getMem a = w := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [memIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonMem a w s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonMem r v a w
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonMem a w s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- pcFree lemmas
-- ============================================================================

theorem pcFree_regIs (r : Reg) (v : Word) : (regIs r v).pcFree := by
  intro h hp; rw [regIs] at hp; subst hp; rfl

theorem pcFree_memIs (a : Addr) (v : Word) : (memIs a v).pcFree := by
  intro h hp; rw [memIs] at hp; subst hp; rfl

theorem pcFree_emp : empAssertion.pcFree := by
  intro h hp; rw [empAssertion] at hp; subst hp; rfl

theorem pcFree_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ** Q).pcFree := by
  intro h ⟨h1, h2, hd, hunion, hp1, hp2⟩
  have hp1 := hP h1 hp1
  have hp2 := hQ h2 hp2
  rw [← hunion]; simp [PartialState.union, hp1, hp2]

-- ============================================================================
-- Algebraic properties
-- ============================================================================

theorem sepConj_comm (P Q : Assertion) :
    ∀ h, (P ** Q) h ↔ (Q ** P) h := by
  intro h
  constructor
  · intro ⟨h1, h2, hd, hunion, hp1, hp2⟩
    exact ⟨h2, h1, hd.symm, by rw [PartialState.union_comm_of_disjoint hd.symm, hunion], hp2, hp1⟩
  · intro ⟨h1, h2, hd, hunion, hp1, hp2⟩
    exact ⟨h2, h1, hd.symm, by rw [PartialState.union_comm_of_disjoint hd.symm, hunion], hp2, hp1⟩

theorem sepConj_emp_left (P : Assertion) :
    ∀ h, (empAssertion ** P) h ↔ P h := by
  intro h
  constructor
  · intro ⟨h1, h2, _, hunion, hemp, hp⟩
    rw [empAssertion] at hemp; subst hemp
    rw [PartialState.union_empty_left] at hunion
    rw [← hunion]; exact hp
  · intro hp
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left h,
           PartialState.union_empty_left h, rfl, hp⟩

theorem sepConj_emp_right (P : Assertion) :
    ∀ h, (P ** empAssertion) h ↔ P h := by
  intro h
  rw [sepConj_comm]
  exact sepConj_emp_left P h

/-- Helper: union is associative. -/
private theorem union_assoc (h1 h2 h3 : PartialState) :
    (h1.union h2).union h3 = h1.union (h2.union h3) := by
  simp only [PartialState.union, PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases h1.regs r <;> simp
  · funext a; cases h1.mem a <;> simp
  · cases h1.pc <;> simp
  · cases h1.publicValues <;> simp
  · cases h1.privateInput <;> simp

/-- Helper: extract disjointness facts from nested unions. -/
private theorem disjoint_of_union_disjoint_right
    {h1 h2 h3 : PartialState} (hd12 : h1.Disjoint h2)
    (hd_union_3 : (h1.union h2).Disjoint h3) :
    h2.Disjoint h3 := by
  obtain ⟨hdr, hdm, hdpc, hdpv, hdpi⟩ := hd_union_3
  obtain ⟨hdr12, hdm12, hdpc12, hdpv12, hdpi12⟩ := hd12
  refine ⟨fun r => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr12 r with h1none | h2none
    · have h := hdr r
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdm12 a with h1none | h2none
    · have h := hdm a
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpc12 with h1none | h2none
    · have h := hdpc
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpv12 with h1none | h2none
    · have h := hdpv
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none
  · rcases hdpi12 with h1none | h2none
    · have h := hdpi
      simp only [PartialState.union] at h
      rw [h1none] at h; simp at h; exact h
    · exact Or.inl h2none

private theorem disjoint_of_union_disjoint_left
    {h1 h2 h3 : PartialState} (hd12 : h1.Disjoint h2)
    (hd_union_3 : (h1.union h2).Disjoint h3) :
    h1.Disjoint (h2.union h3) := by
  obtain ⟨hdr, hdm, hdpc, hdpv, hdpi⟩ := hd_union_3
  obtain ⟨hdr12, hdm12, hdpc12, hdpv12, hdpi12⟩ := hd12
  refine ⟨fun r => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr12 r with h1none | h2none
    · exact Or.inl h1none
    · have h := hdr r
      simp only [PartialState.union] at h
      cases h1r : h1.regs r
      · exact Or.inl rfl
      · rw [h1r] at h; simp at h
        right; show (PartialState.union h2 h3).regs r = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdm12 a with h1none | h2none
    · exact Or.inl h1none
    · have h := hdm a
      simp only [PartialState.union] at h
      cases h1m : h1.mem a
      · exact Or.inl rfl
      · rw [h1m] at h; simp at h
        right; show (PartialState.union h2 h3).mem a = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpc12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpc
      simp only [PartialState.union] at h
      cases h1pc : h1.pc
      · exact Or.inl rfl
      · rw [h1pc] at h; simp at h
        right; show (PartialState.union h2 h3).pc = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpv12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpv
      simp only [PartialState.union] at h
      cases h1pv : h1.publicValues
      · exact Or.inl rfl
      · rw [h1pv] at h; simp at h
        right; show (PartialState.union h2 h3).publicValues = none
        simp only [PartialState.union]; rw [h2none]; exact h
  · rcases hdpi12 with h1none | h2none
    · exact Or.inl h1none
    · have h := hdpi
      simp only [PartialState.union] at h
      cases h1pi : h1.privateInput
      · exact Or.inl rfl
      · rw [h1pi] at h; simp at h
        right; show (PartialState.union h2 h3).privateInput = none
        simp only [PartialState.union]; rw [h2none]; exact h

private theorem disjoint_left_of_disjoint_union_right
    {h1 h2 h3 : PartialState} (hd1_23 : h1.Disjoint (h2.union h3)) :
    h1.Disjoint h2 := by
  obtain ⟨hdr, hdm, hdpc, hdpv, hdpi⟩ := hd1_23
  refine ⟨fun r => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases (hdr r) with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2r : h2.regs r <;> rw [h2r] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases (hdm a) with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2m : h2.mem a <;> rw [h2m] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpc with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pc : h2.pc <;> rw [h2pc] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpv with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pv : h2.publicValues <;> rw [h2pv] at h23none <;> simp at h23none
      exact Or.inr rfl
  · rcases hdpi with h1none | h23none
    · exact Or.inl h1none
    · simp only [PartialState.union] at h23none
      cases h2pi : h2.privateInput <;> rw [h2pi] at h23none <;> simp at h23none
      exact Or.inr rfl

private theorem disjoint_union_left_of_disjoint_union_right
    {h1 h2 h3 : PartialState} (hd23 : h2.Disjoint h3)
    (hd1_23 : h1.Disjoint (h2.union h3)) :
    (h1.union h2).Disjoint h3 := by
  obtain ⟨hdr, hdm, hdpc, hdpv, hdpi⟩ := hd1_23
  obtain ⟨hdr23, hdm23, hdpc23, hdpv23, hdpi23⟩ := hd23
  refine ⟨fun r => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · rcases hdr23 r with h2none | h3none
    · have h := hdr r
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).regs r = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdm23 a with h2none | h3none
    · have h := hdm a
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).mem a = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpc23 with h2none | h3none
    · have h := hdpc
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).pc = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpv23 with h2none | h3none
    · have h := hdpv
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).publicValues = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none
  · rcases hdpi23 with h2none | h3none
    · have h := hdpi
      simp only [PartialState.union] at h
      rw [h2none] at h; simp at h
      rcases h with h1none | h3none
      · left; show (PartialState.union h1 h2).privateInput = none
        simp only [PartialState.union]; rw [h1none]; simp [h2none]
      · exact Or.inr h3none
    · exact Or.inr h3none

theorem sepConj_assoc (P Q R : Assertion) :
    ∀ h, ((P ** Q) ** R) h ↔ (P ** (Q ** R)) h := by
  intro h
  constructor
  · intro ⟨h12, h3, hd12_3, hunion12_3, ⟨h1, h2, hd12, hunion12, hp, hq⟩, hr⟩
    subst hunion12
    have hd2_3 := disjoint_of_union_disjoint_right hd12 hd12_3
    have hd1_23 := disjoint_of_union_disjoint_left hd12 hd12_3
    exact ⟨h1, h2.union h3, hd1_23,
           by rw [← union_assoc, hunion12_3],
           hp, h2, h3, hd2_3, rfl, hq, hr⟩
  · intro ⟨h1, h23, hd1_23, hunion1_23, hp, h2, h3, hd23, hunion23, hq, hr⟩
    subst hunion23
    have hd12 := disjoint_left_of_disjoint_union_right hd1_23
    have hd12_3 := disjoint_union_left_of_disjoint_union_right hd23 hd1_23
    exact ⟨h1.union h2, h3, hd12_3,
           by rw [union_assoc, hunion1_23],
           ⟨h1, h2, hd12, rfl, hp, hq⟩, hr⟩

-- ============================================================================
-- Pure modality: lifting Prop into Assertion
-- ============================================================================

/-- The pure assertion: holds on the empty partial state when P is true.
    This is the standard separation logic ⌜P⌝ modality. -/
def pure (P : Prop) : Assertion :=
  fun h => h = PartialState.empty ∧ P

/-- Notation: ⌜P⌝ is the pure assertion lifting P into the assertion language. -/
notation "⌜" P "⌝" => RiscVMacroAsm.pure P

@[simp]
theorem holdsFor_pure (P : Prop) (s : MachineState) :
    (⌜P⌝).holdsFor s ↔ P := by
  simp only [Assertion.holdsFor, pure]
  constructor
  · rintro ⟨h, _, rfl, hp⟩; exact hp
  · intro hp; exact ⟨PartialState.empty, PartialState.CompatibleWith_empty s, rfl, hp⟩

theorem pcFree_pure (P : Prop) : (⌜P⌝).pcFree := by
  intro h ⟨hemp, _⟩; subst hemp; rfl

theorem pure_true_eq_emp : ⌜True⌝ = empAssertion := by
  funext h; simp [pure, empAssertion]

theorem sepConj_pure_left (P : Prop) (Q : Assertion) :
    ∀ h, (⌜P⌝ ** Q) h ↔ P ∧ Q h := by
  intro h
  constructor
  · intro ⟨h1, h2, _, hunion, ⟨hemp, hp⟩, hq⟩
    subst hemp; rw [PartialState.union_empty_left] at hunion
    exact ⟨hp, hunion ▸ hq⟩
  · intro ⟨hp, hq⟩
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left h,
           PartialState.union_empty_left h, ⟨rfl, hp⟩, hq⟩

theorem sepConj_pure_right (P : Assertion) (Q : Prop) :
    ∀ h, (P ** ⌜Q⌝) h ↔ P h ∧ Q := by
  intro h
  rw [sepConj_comm]
  simp only [sepConj_pure_left]
  exact And.comm

-- ============================================================================
-- Logical combinators (preserved for backward compatibility)
-- ============================================================================

/-- Universal quantification over assertions. -/
def aForall {α : Type} (P : α → Assertion) : Assertion :=
  fun h => ∀ a, P a h

/-- Existential quantification over assertions. -/
def aExists {α : Type} (P : α → Assertion) : Assertion :=
  fun h => ∃ a, P a h

-- ============================================================================
-- publicValuesIs assertion
-- ============================================================================

/-- Public values stream equals a given list. -/
def publicValuesIs (vals : List Word) : Assertion :=
  fun h => h = PartialState.singletonPublicValues vals

-- ============================================================================
-- CompatibleWith / holdsFor for publicValuesIs
-- ============================================================================

namespace PartialState

theorem CompatibleWith_singletonPublicValues (vals : List Word) (s : MachineState) :
    (singletonPublicValues vals).CompatibleWith s ↔ s.publicValues = vals := by
  constructor
  · intro ⟨_, _, _, hpv, _⟩
    exact hpv vals rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPublicValues] at h,
           fun _ _ h => by simp [singletonPublicValues] at h,
           fun _ h => by simp [singletonPublicValues] at h,
           fun v' h => by simp [singletonPublicValues] at h; rw [← h]; exact heq,
           fun _ h => by simp [singletonPublicValues] at h⟩

end PartialState

@[simp]
theorem holdsFor_publicValuesIs (vals : List Word) (s : MachineState) :
    (publicValuesIs vals).holdsFor s ↔ s.publicValues = vals := by
  simp only [Assertion.holdsFor, publicValuesIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPublicValues vals s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPublicValues vals s).mpr heq, rfl⟩

-- ============================================================================
-- pcFree for publicValuesIs
-- ============================================================================

theorem pcFree_publicValuesIs (vals : List Word) : (publicValuesIs vals).pcFree := by
  intro h hp; rw [publicValuesIs] at hp; subst hp; rfl

-- ============================================================================
-- Disjointness lemmas for publicValuesIs composition
-- ============================================================================

private theorem singletonReg_disjoint_singletonPublicValues (r : Reg) (v : Word) (vals : List Word) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonPublicValues vals) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonMem_disjoint_singletonPublicValues (a : Addr) (v : Word) (vals : List Word) :
    (PartialState.singletonMem a v).Disjoint (PartialState.singletonPublicValues vals) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

-- ============================================================================
-- holdsFor_sepConj convenience lemmas for publicValuesIs
-- ============================================================================

theorem holdsFor_sepConj_regIs_publicValuesIs {r : Reg} {v : Word}
    {vals : List Word} {s : MachineState} :
    ((regIs r v) ** (publicValuesIs vals)).holdsFor s ↔
      s.getReg r = v ∧ s.publicValues = vals := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [publicValuesIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonPublicValues vals s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonPublicValues r v vals
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonPublicValues vals s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- privateInputIs assertion
-- ============================================================================

/-- Private input stream equals a given list. -/
def privateInputIs (vals : List Word) : Assertion :=
  fun h => h = PartialState.singletonPrivateInput vals

-- ============================================================================
-- CompatibleWith / holdsFor for privateInputIs
-- ============================================================================

namespace PartialState

theorem CompatibleWith_singletonPrivateInput (vals : List Word) (s : MachineState) :
    (singletonPrivateInput vals).CompatibleWith s ↔ s.privateInput = vals := by
  constructor
  · intro ⟨_, _, _, _, hpi⟩
    exact hpi vals rfl
  · intro heq
    exact ⟨fun _ _ h => by simp [singletonPrivateInput] at h,
           fun _ _ h => by simp [singletonPrivateInput] at h,
           fun _ h => by simp [singletonPrivateInput] at h,
           fun _ h => by simp [singletonPrivateInput] at h,
           fun v' h => by simp [singletonPrivateInput] at h; rw [← h]; exact heq⟩

end PartialState

@[simp]
theorem holdsFor_privateInputIs (vals : List Word) (s : MachineState) :
    (privateInputIs vals).holdsFor s ↔ s.privateInput = vals := by
  simp only [Assertion.holdsFor, privateInputIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    exact (PartialState.CompatibleWith_singletonPrivateInput vals s).mp hcompat
  · intro heq
    exact ⟨_, (PartialState.CompatibleWith_singletonPrivateInput vals s).mpr heq, rfl⟩

-- ============================================================================
-- pcFree for privateInputIs
-- ============================================================================

theorem pcFree_privateInputIs (vals : List Word) : (privateInputIs vals).pcFree := by
  intro h hp; rw [privateInputIs] at hp; subst hp; rfl

-- ============================================================================
-- Disjointness lemmas for privateInputIs composition
-- ============================================================================

private theorem singletonReg_disjoint_singletonPrivateInput (r : Reg) (v : Word) (vals : List Word) :
    (PartialState.singletonReg r v).Disjoint (PartialState.singletonPrivateInput vals) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonMem_disjoint_singletonPrivateInput (a : Addr) (v : Word) (vals : List Word) :
    (PartialState.singletonMem a v).Disjoint (PartialState.singletonPrivateInput vals) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem singletonPublicValues_disjoint_singletonPrivateInput (pv : List Word) (pi : List Word) :
    (PartialState.singletonPublicValues pv).Disjoint (PartialState.singletonPrivateInput pi) := by
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩

-- ============================================================================
-- holdsFor_sepConj convenience lemmas for privateInputIs
-- ============================================================================

theorem holdsFor_sepConj_regIs_privateInputIs {r : Reg} {v : Word}
    {vals : List Word} {s : MachineState} :
    ((regIs r v) ** (privateInputIs vals)).holdsFor s ↔
      s.getReg r = v ∧ s.privateInput = vals := by
  constructor
  · rintro ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
    rw [regIs] at hp1; rw [privateInputIs] at hp2; subst hp1; subst hp2
    rw [← hunion] at hcompat
    rw [PartialState.CompatibleWith_union hd] at hcompat
    exact ⟨(PartialState.CompatibleWith_singletonReg r v s).mp hcompat.1,
           (PartialState.CompatibleWith_singletonPrivateInput vals s).mp hcompat.2⟩
  · intro ⟨h1, h2⟩
    have hd := singletonReg_disjoint_singletonPrivateInput r v vals
    exact ⟨_, (PartialState.CompatibleWith_union hd).mpr
      ⟨(PartialState.CompatibleWith_singletonReg r v s).mpr h1,
       (PartialState.CompatibleWith_singletonPrivateInput vals s).mpr h2⟩,
      _, _, hd, rfl, rfl, rfl⟩

-- ============================================================================
-- fullState: a partial state owning all tracked resources
-- ============================================================================

namespace PartialState

/-- A partial state that owns regs, mem, pc, publicValues, privateInput
    with values from a full machine state. -/
def fullState (s : MachineState) : PartialState where
  regs := fun r => some (s.getReg r)
  mem  := fun a => some (s.getMem a)
  pc   := some s.pc
  publicValues := some s.publicValues
  privateInput := some s.privateInput

theorem CompatibleWith_fullState (s : MachineState) :
    (fullState s).CompatibleWith s := by
  refine ⟨fun r v h => ?_, fun a v h => ?_, fun v h => ?_, fun v h => ?_, fun v h => ?_⟩ <;>
  simp [fullState] at h <;> exact h ▸ rfl

end PartialState

-- ============================================================================
-- stateIs: exact state match (up to committed field)
-- ============================================================================

/-- Assert that the machine state matches the target on all resources tracked by PartialState
    (registers, memory, PC, publicValues, privateInput). -/
def stateIs (target : MachineState) : Assertion :=
  fun h => h = PartialState.fullState target

@[simp]
theorem holdsFor_stateIs (target : MachineState) (s : MachineState) :
    (stateIs target).holdsFor s ↔
      (∀ r, s.getReg r = target.getReg r) ∧
      (∀ a, s.getMem a = target.getMem a) ∧
      s.pc = target.pc ∧
      s.publicValues = target.publicValues ∧
      s.privateInput = target.privateInput := by
  simp only [Assertion.holdsFor, stateIs]
  constructor
  · rintro ⟨h, hcompat, rfl⟩
    obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hcompat
    exact ⟨fun r => hr r (target.getReg r) (by simp [PartialState.fullState]),
           fun a => hm a (target.getMem a) (by simp [PartialState.fullState]),
           hpc target.pc (by simp [PartialState.fullState]),
           hpv target.publicValues (by simp [PartialState.fullState]),
           hpi target.privateInput (by simp [PartialState.fullState])⟩
  · intro ⟨hregs, hmem, hpc, hpv, hpi⟩
    refine ⟨PartialState.fullState target, ?_, rfl⟩
    refine ⟨fun r v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · simp [PartialState.fullState] at hv; rw [hregs, hv]
    · simp [PartialState.fullState] at hv; rw [hmem, hv]
    · simp [PartialState.fullState] at hv; rw [hpc, hv]
    · simp [PartialState.fullState] at hv; rw [hpv, hv]
    · simp [PartialState.fullState] at hv; rw [hpi, hv]


-- ============================================================================
-- holdsFor_pcFree_setPC: pcFree assertions are preserved by setPC
-- ============================================================================

theorem holdsFor_pcFree_setPC {P : Assertion} (hP : P.pcFree) (s : MachineState) (v : Word) :
    P.holdsFor s → P.holdsFor (s.setPC v) := by
  intro ⟨h, hcompat, hp⟩
  have hpc_none := hP h hp
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hcompat
  exact ⟨h, ⟨fun r' v' hv => by rw [MachineState.getReg_setPC]; exact hr r' v' hv,
              fun a' v' hv => by simp [MachineState.getMem, MachineState.setPC]; exact hm a' v' hv,
              fun v' hv => by rw [hpc_none] at hv; simp at hv,
              fun v' hv => by simp [MachineState.setPC] at *; exact hpv v' hv,
              fun v' hv => by simp [MachineState.setPC] at *; exact hpi v' hv⟩, hp⟩

-- ============================================================================
-- liftPred: lift a MachineState predicate to Assertion
-- ============================================================================

/-- Lift a predicate on MachineState to an Assertion.
    `(liftPred P).holdsFor s ↔ P s` for predicates P that only depend on
    registers, memory, PC, publicValues, and privateInput (not committed). -/
def liftPred (P : MachineState → Prop) : Assertion :=
  fun h => ∀ s, h.CompatibleWith s → P s

/-- The forward direction of holdsFor for liftPred always works. -/
theorem holdsFor_liftPred_mp {P : MachineState → Prop} {s : MachineState}
    (h : (liftPred P).holdsFor s) : P s := by
  obtain ⟨h, hcompat, hP⟩ := h
  exact hP s hcompat

/-- Backward: construct holdsFor for liftPred using fullState.
    Requires proving P transfers through compatible states. -/
theorem holdsFor_liftPred_intro {P : MachineState → Prop} {s : MachineState}
    (htransfer : ∀ t : MachineState,
      (∀ r, t.getReg r = s.getReg r) → (∀ a, t.getMem a = s.getMem a) →
      t.pc = s.pc → t.publicValues = s.publicValues → t.privateInput = s.privateInput →
      P t) :
    (liftPred P).holdsFor s := by
  refine ⟨PartialState.fullState s, PartialState.CompatibleWith_fullState s, fun t hcompat => ?_⟩
  apply htransfer
  · intro r; exact hcompat.1 r (s.getReg r) (by simp [PartialState.fullState])
  · intro a; exact hcompat.2.1 a (s.getMem a) (by simp [PartialState.fullState])
  · exact hcompat.2.2.1 s.pc (by simp [PartialState.fullState])
  · exact hcompat.2.2.2.1 s.publicValues (by simp [PartialState.fullState])
  · exact hcompat.2.2.2.2 s.privateInput (by simp [PartialState.fullState])

/-- Simpler backward direction: if P only depends on tracked fields
    (getReg, getMem, pc, publicValues, privateInput), then P s → (liftPred P).holdsFor s. -/
theorem holdsFor_liftPred_of {P : MachineState → Prop} {s : MachineState}
    (hPs : P s)
    (hstable : ∀ t : MachineState,
      (∀ r, t.getReg r = s.getReg r) → (∀ a, t.getMem a = s.getMem a) →
      t.pc = s.pc → t.publicValues = s.publicValues → t.privateInput = s.privateInput →
      P s → P t) :
    (liftPred P).holdsFor s :=
  holdsFor_liftPred_intro (fun t hr hm hpc hpv hpi => hstable t hr hm hpc hpv hpi hPs)

end RiscVMacroAsm
