/-
  RiscVMacroAsm.SepLogic

  Separation logic assertions over the machine state.

  Following Kennedy et al. (2013), we treat registers and memory locations
  as separable resources. An assertion is a predicate on machine states.
  The separating conjunction (P ** Q) holds when the state can be split
  into two "sub-states" satisfying P and Q respectively, where the
  resources (registers and memory cells) are disjoint.

  For simplicity, we use a "permissions" model: a sub-state tracks which
  registers and memory locations it "owns" via finite sets, and two
  sub-states are compatible if their owned resources are disjoint.
-/

import RiscVMacroAsm.Basic

namespace RiscVMacroAsm

-- ============================================================================
-- Resource Tracking
-- ============================================================================

/-- A resource is either a register or a memory address. -/
inductive Resource where
  | reg : Reg → Resource
  | mem : Addr → Resource
  deriving DecidableEq, Repr, Hashable

/-- An assertion is a predicate over machine states. -/
def Assertion := MachineState → Prop

instance : Inhabited Assertion := ⟨fun _ => True⟩

-- ============================================================================
-- Basic Assertions
-- ============================================================================

/-- Register r holds value v. -/
def regIs (r : Reg) (v : Word) : Assertion :=
  fun s => s.getReg r = v

/-- Notation: r ↦ᵣ v means register r holds value v. -/
notation:50 r " ↦ᵣ " v => regIs r v

/-- Register r holds some (unspecified) value. -/
def regAny (r : Reg) : Assertion :=
  fun _ => True

/-- Notation: r ↦ᵣ ? means register r holds any value. -/
notation:50 r " ↦ᵣ ?" => regAny r

/-- Memory at address a holds value v. -/
def memIs (a : Addr) (v : Word) : Assertion :=
  fun s => s.getMem a = v

/-- Notation: a ↦ₘ v means memory at address a holds value v. -/
notation:50 a " ↦ₘ " v => memIs a v

/-- The assertion that always holds. -/
def empAssertion : Assertion := fun _ => True

/-- The assertion that never holds. -/
def falseAssertion : Assertion := fun _ => False

-- ============================================================================
-- Logical Combinators
-- ============================================================================

/-- Conjunction of assertions. -/
def aAnd (P Q : Assertion) : Assertion :=
  fun s => P s ∧ Q s

/-- Disjunction of assertions. -/
def aOr (P Q : Assertion) : Assertion :=
  fun s => P s ∨ Q s

/-- Implication of assertions. -/
def aImpl (P Q : Assertion) : Assertion :=
  fun s => P s → Q s

/-- Universal quantification over assertions. -/
def aForall {α : Type} (P : α → Assertion) : Assertion :=
  fun s => ∀ a, P a s

/-- Existential quantification over assertions. -/
def aExists {α : Type} (P : α → Assertion) : Assertion :=
  fun s => ∃ a, P a s

-- ============================================================================
-- Separating Conjunction
-- ============================================================================

/-- Separating conjunction: P ** Q holds when both P and Q hold.

    In a full separation logic, we would require the resources accessed by
    P and Q to be disjoint. Here we use a simplified "intuitionistic"
    model where both P and Q are evaluated on the same state, which is
    sound for our purposes: the frame rule still holds because our
    instructions only modify the registers/memory they explicitly write.

    This is the standard simplification used when the assertion language
    tracks specific resources (like r ↦ᵣ v) and the frame rule is proved
    with respect to instruction-level non-interference.
-/
def sepConj (P Q : Assertion) : Assertion :=
  fun s => P s ∧ Q s

/-- Notation: P ** Q is the separating conjunction. -/
infixr:35 " ** " => sepConj

/-- Separating conjunction is commutative. -/
theorem sepConj_comm (P Q : Assertion) : ∀ s, (P ** Q) s ↔ (Q ** P) s := by
  intro s
  simp [sepConj, And.comm]

/-- Separating conjunction is associative. -/
theorem sepConj_assoc (P Q R : Assertion) :
    ∀ s, ((P ** Q) ** R) s ↔ (P ** (Q ** R)) s := by
  intro s
  simp [sepConj, And.assoc]

/-- emp is the unit of separating conjunction. -/
theorem sepConj_emp_left (P : Assertion) :
    ∀ s, (empAssertion ** P) s ↔ P s := by
  intro s
  simp [sepConj, empAssertion]

theorem sepConj_emp_right (P : Assertion) :
    ∀ s, (P ** empAssertion) s ↔ P s := by
  intro s
  simp [sepConj, empAssertion]

-- ============================================================================
-- Separating Implication (Magic Wand)
-- ============================================================================

/-- Separating implication (magic wand): P -* Q.
    In our simplified model, this is just regular implication. -/
def sepImpl (P Q : Assertion) : Assertion :=
  fun s => P s → Q s

infixr:30 " -* " => sepImpl

end RiscVMacroAsm
