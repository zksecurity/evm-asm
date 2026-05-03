/-
  EvmAsm.EL.Conformance

  Lean-side conformance vector surface for GH #125.
-/

namespace EvmAsm.EL
namespace Conformance

/-- Expected result for a conformance vector: either a value or an expected error. -/
inductive ExpectedResult (α : Type) where
  | value (output : α)
  | error (label : String)
  deriving Repr

/-- Typed conformance vector. Later slices can instantiate `ι`/`ο` with
    opcode inputs, transaction/state inputs, or decoded execution-spec cases. -/
structure TestVector (ι ο : Type) where
  id : String
  input : ι
  expected : ExpectedResult ο
  deriving Repr

/-- Result of checking one vector against an executable specification. -/
inductive CheckResult where
  | passed
  | failed (id : String)
  | errored (id label : String)
  deriving DecidableEq, Repr

namespace CheckResult

def isPassed : CheckResult → Prop
  | passed => True
  | _ => False

@[simp] theorem isPassed_passed : passed.isPassed := trivial

@[simp] theorem not_isPassed_failed (id : String) :
    ¬ (failed id).isPassed := by
  simp [isPassed]

@[simp] theorem not_isPassed_errored (id label : String) :
    ¬ (errored id label).isPassed := by
  simp [isPassed]

end CheckResult

/-- Check a vector whose expected result is a concrete output. -/
def checkVector [DecidableEq ο] (run : ι → ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      if run vector.input = expected then .passed else .failed vector.id
  | .error label => .errored vector.id label

/-- Check a vector against a partial executable specification. -/
def checkVector? [DecidableEq ο] (run : ι → Option ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      match run vector.input with
      | some actual => if actual = expected then .passed else .failed vector.id
      | none => .failed vector.id
  | .error label =>
      match run vector.input with
      | some _ => .failed vector.id
      | none => .errored vector.id label

theorem checkVector_value_passed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector, h_run]

theorem checkVector_value_failed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input ≠ expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .failed id := by
  simp [checkVector, h_run]

theorem checkVector_error_errored
    [DecidableEq ο] (run : ι → ο) (id label : String) (input : ι) :
    checkVector run { id := id, input := input, expected := .error label } = .errored id label := rfl

theorem checkVector?_some_passed
    [DecidableEq ο] (run : ι → Option ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = some expected) :
    checkVector? run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector?, h_run]

theorem checkVector?_none_error
    [DecidableEq ο] (run : ι → Option ο) (id label : String) (input : ι)
    (h_run : run input = none) :
    checkVector? run { id := id, input := input, expected := .error label } = .errored id label := by
  simp [checkVector?, h_run]

end Conformance
end EvmAsm.EL
