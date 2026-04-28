/-
  EvmAsm.Evm64.DivMod.SpecPredicates

  EvmWord-level wrappers around the Word-tuple runtime condition predicates
  used by the n=4 stack-level DIV/MOD specs.

  Each definition is a thin shim over a Word-level predicate plus a `_def`
  `rfl` lemma. Extracted from `Spec.lean` to keep that file under the file-size
  guardrail. No content changes — every definition / `_def` lemma here is
  byte-identical to its previous home in `Spec.lean`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- EvmWord-level runtime condition predicates for the n=4 max path
-- ============================================================================

-- The full-path DIV spec `evm_div_n4_full_max_skip_spec` takes runtime
-- conditions (`isMaxTrialN4`, `isSkipBorrowN4Max`) keyed off eight Word
-- limbs. For the EvmWord-level stack spec, it's more natural to express
-- these on `a b : EvmWord` directly — the wrappers below defer to the
-- Word-level predicates via `a.getLimbN k` / `b.getLimbN k`.

/-- Max trial quotient condition at n=4 in EvmWord form: `u4 ≥ b3'` after
    normalization, i.e., the algorithm uses the maximum trial quotient
    (`signExtend12 4095 = 2^64 - 1`). -/
def isMaxTrialN4Evm (a b : EvmWord) : Prop :=
  isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

/-- Skip-addback condition at n=4 max in EvmWord form: the runtime borrow
    check `u4 < mulsubN4_c3` does not fire, so the algorithm skips the
    addback step and uses `qHat` as the quotient digit. -/
def isSkipBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isMaxTrialN4Evm_def {a b : EvmWord} :
    isMaxTrialN4Evm a b =
    isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isSkipBorrowN4MaxEvm_def {a b : EvmWord} :
    isSkipBorrowN4MaxEvm a b =
    isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Call trial condition at n=4 in EvmWord form: `u4 < b3'` after
    normalization, i.e., the max trial is too large so the algorithm falls
    through to `div128` for a tighter quotient. -/
def isCallTrialN4Evm (a b : EvmWord) : Prop :=
  isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

/-- Skip-addback condition at n=4 call path in EvmWord form: the runtime
    borrow check does not fire, so the algorithm skips addback after the
    `div128`-computed trial quotient. -/
def isSkipBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                     (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Addback-needed condition at n=4 call path in EvmWord form: the runtime
    borrow check fires, so the algorithm decrements the trial quotient and
    adds back `v` to the partial remainder. -/
def isAddbackBorrowN4CallEvm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isCallTrialN4Evm_def {a b : EvmWord} :
    isCallTrialN4Evm a b =
    isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isSkipBorrowN4CallEvm_def {a b : EvmWord} :
    isSkipBorrowN4CallEvm a b =
    isSkipBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isAddbackBorrowN4CallEvm_def {a b : EvmWord} :
    isAddbackBorrowN4CallEvm a b =
    isAddbackBorrowN4Call (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Carry-2-non-zero condition at n=4 call path in EvmWord form: the
    double-addback branch indicator used by the BEQ variant. Wraps the
    raw-limb form `isAddbackCarry2NzN4CallAb`. -/
def isAddbackCarry2NzN4CallEvm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4CallAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4CallEvm_def {a b : EvmWord} :
    isAddbackCarry2NzN4CallEvm a b =
    isAddbackCarry2NzN4CallAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- v2 mirror of `isAddbackBorrowN4CallEvm` — uses `div128Quot_v2` via
    `isAddbackBorrowN4Call_v2`. Issue #1337 algorithm fix migration. -/
def isAddbackBorrowN4CallEvm_v2 (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Call_v2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4CallEvm_v2_def {a b : EvmWord} :
    isAddbackBorrowN4CallEvm_v2 a b =
    isAddbackBorrowN4Call_v2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- v2 mirror of `isAddbackCarry2NzN4CallEvm` — uses `div128Quot_v2` via
    `isAddbackCarry2NzN4CallAb_v2`. Issue #1337 algorithm fix migration. -/
def isAddbackCarry2NzN4CallEvm_v2 (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4CallAb_v2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                               (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4CallEvm_v2_def {a b : EvmWord} :
    isAddbackCarry2NzN4CallEvm_v2 a b =
    isAddbackCarry2NzN4CallAb_v2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                                 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Addback-needed condition at n=4 max path in EvmWord form: the runtime
    borrow check fires (mulsub underflowed), so the algorithm decrements
    the max trial quotient and adds back `b'` to the partial remainder
    (possibly twice — see `isAddbackCarry2NzN4MaxAbEvm`). -/
def isAddbackBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4MaxEvm_def {a b : EvmWord} :
    isAddbackBorrowN4MaxEvm a b =
    isAddbackBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                         (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Double-addback carry2≠0 condition at n=4 max path in EvmWord form: after
    mulsub underflow + first-addback (carry1 = 0), the second addback fires
    (carry2 ≠ 0). Together with `isAddbackBorrowN4MaxEvm` this pins the
    algorithm to the double-addback branch. -/
def isAddbackCarry2NzN4MaxAbEvm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4MaxAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4MaxAbEvm_def {a b : EvmWord} :
    isAddbackCarry2NzN4MaxAbEvm a b =
    isAddbackCarry2NzN4MaxAb (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

end EvmAsm.Evm64
