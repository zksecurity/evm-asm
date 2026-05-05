/-
  EvmAsm.Evm64.HandlerTableCompose

  Composition helpers for pure opcode handler tables (GH #107).
-/

import EvmAsm.Evm64.HandlerTable

namespace EvmAsm.Evm64

namespace HandlerTable

/--
Left-biased composition of independently verified handler tables.

Distinctive token: HandlerTableCompose.orElse #107.
-/
def orElse (left right : HandlerTable) : HandlerTable :=
  fun opcode =>
    match left opcode with
    | some handler => some handler
    | none => right opcode

@[simp] theorem orElse_left_some
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) :
    orElse left right opcode = some handler := by
  simp [orElse, h_left]

@[simp] theorem orElse_left_none
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) :
    orElse left right opcode = right opcode := by
  simp [orElse, h_left]

@[simp] theorem orElse_empty_left (right : HandlerTable) :
    orElse empty right = right := by
  funext opcode
  simp [orElse]

theorem orElse_empty_right_apply (left : HandlerTable) (opcode : EvmOpcode) :
    orElse left empty opcode = left opcode := by
  cases h_left : left opcode with
  | none => simp [orElse, h_left]
  | some handler => simp [orElse, h_left]

@[simp] theorem orElse_empty_right (left : HandlerTable) :
    orElse left empty = left := by
  funext opcode
  exact orElse_empty_right_apply left opcode

theorem dispatchOpcode?_orElse_left
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) (state : EvmState) :
    dispatchOpcode? (orElse left right) opcode state = some (handler state) := by
  simp [dispatchOpcode?, h_left]

theorem dispatchOpcode?_orElse_right
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (state : EvmState) :
    dispatchOpcode? (orElse left right) opcode state =
      dispatchOpcode? right opcode state := by
  simp [dispatchOpcode?, h_left]

theorem dispatchOpcode_orElse_left
    {left right : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_left : left opcode = some handler) (state : EvmState) :
    dispatchOpcode (orElse left right) opcode state = handler state := by
  simp [dispatchOpcode, dispatchOpcode?_orElse_left h_left state]

theorem dispatchOpcode_orElse_right
    {left right : HandlerTable} {opcode : EvmOpcode}
    (h_left : left opcode = none) (state : EvmState) :
    dispatchOpcode (orElse left right) opcode state =
      dispatchOpcode right opcode state := by
  simp [dispatchOpcode, dispatchOpcode?_orElse_right h_left state]

end HandlerTable

end EvmAsm.Evm64
