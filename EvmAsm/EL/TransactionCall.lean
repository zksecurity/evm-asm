/-
  EvmAsm.EL.TransactionCall

  Bridge from validated transactions to message-call frames for GH #122.
-/

import EvmAsm.EL.Transaction
import EvmAsm.EL.MessageCall

namespace EvmAsm.EL
namespace Transaction

/--
  Initial message-call frame for ordinary transactions. Contract-creation
  transactions (`to = none`) are intentionally left for CREATE/CREATE2 work.
-/
def toCallFrame? (tx : Transaction) : Option CallFrame :=
  match tx.to with
  | none => none
  | some callee => some (CallFrame.forCall tx.sender callee tx.value tx.data tx.gasLimit false)

theorem toCallFrame?_create (tx : Transaction) (h_to : tx.to = none) :
    tx.toCallFrame? = none := by
  simp [toCallFrame?, h_to]

theorem toCallFrame?_some
    (tx : Transaction) {callee : Address} (h_to : tx.to = some callee) :
    tx.toCallFrame? = some (CallFrame.forCall tx.sender callee tx.value tx.data tx.gasLimit false) := by
  simp [toCallFrame?, h_to]

theorem toCallFrame?_callee
    (tx : Transaction) {callee : Address} {frame : CallFrame}
    (h_frame : tx.toCallFrame? = some frame) (h_to : tx.to = some callee) :
    frame.callee = callee := by
  rw [toCallFrame?_some tx h_to] at h_frame
  injection h_frame with h_frame
  rw [← h_frame]
  rfl

theorem toCallFrame?_caller
    (tx : Transaction) {frame : CallFrame}
    (h_frame : tx.toCallFrame? = some frame) :
    frame.caller = tx.sender := by
  unfold toCallFrame? at h_frame
  split at h_frame
  · cases h_frame
  · injection h_frame with h_frame
    rw [← h_frame]
    rfl

theorem toCallFrame?_value
    (tx : Transaction) {frame : CallFrame}
    (h_frame : tx.toCallFrame? = some frame) :
    frame.transferredValue = tx.value ∧ frame.apparentValue = tx.value := by
  unfold toCallFrame? at h_frame
  split at h_frame
  · cases h_frame
  · injection h_frame with h_frame
    rw [← h_frame]
    exact ⟨rfl, rfl⟩

theorem toCallFrame?_input
    (tx : Transaction) {frame : CallFrame}
    (h_frame : tx.toCallFrame? = some frame) :
    frame.input = tx.data := by
  unfold toCallFrame? at h_frame
  split at h_frame
  · cases h_frame
  · injection h_frame with h_frame
    rw [← h_frame]
    rfl

theorem toCallFrame?_nonstatic
    (tx : Transaction) {frame : CallFrame}
    (h_frame : tx.toCallFrame? = some frame) :
    frame.isStatic = false := by
  unfold toCallFrame? at h_frame
  split at h_frame
  · cases h_frame
  · injection h_frame with h_frame
    rw [← h_frame]
    rfl

end Transaction
end EvmAsm.EL
