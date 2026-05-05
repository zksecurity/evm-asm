/-
  EvmAsm.Evm64.StackHandlers

  Pure POP/PUSH0 handler entries for the interpreter handler table (GH #107).
-/

import EvmAsm.Evm64.HandlerTable

namespace EvmAsm.Evm64

namespace StackHandlers

/-- POP removes the top stack item; stack underflow follows the INVALID path. -/
def popHandler : OpcodeHandler :=
  fun state =>
    match state.stack with
    | _ :: stack => state.withStack stack
    | [] => state.invalid

/-- PUSH0 pushes the zero EVM word. -/
def push0Handler : OpcodeHandler :=
  fun state => state.withStack (0 :: state.stack)

/-- Lookup just the stack handlers introduced in this slice. -/
def stackHandler? : EvmOpcode → Option OpcodeHandler
  | .POP => some popHandler
  | .PUSH0 => some push0Handler
  | _ => none

/-- Handler table containing POP and PUSH0 entries.
    Distinctive token: StackHandlers.stackHandlerTable #107. -/
def stackHandlerTable : HandlerTable :=
  HandlerTable.setHandler
    (HandlerTable.setHandler HandlerTable.empty .POP popHandler)
    .PUSH0 push0Handler

@[simp] theorem stackHandler?_POP :
    stackHandler? .POP = some popHandler := rfl

@[simp] theorem stackHandler?_PUSH0 :
    stackHandler? .PUSH0 = some push0Handler := rfl

theorem popHandler_cons_stack
    (state : EvmState) (word : EvmWord) (stack : List EvmWord) :
    (popHandler { state with stack := word :: stack }).stack = stack := rfl

theorem popHandler_nil_status (state : EvmState) :
    (popHandler { state with stack := [] }).status = .error := rfl

theorem popHandler_nil_stack (state : EvmState) :
    (popHandler { state with stack := [] }).stack = [] := rfl

@[simp] theorem push0Handler_stack (state : EvmState) :
    (push0Handler state).stack = 0 :: state.stack := rfl

@[simp] theorem push0Handler_status (state : EvmState) :
    (push0Handler state).status = state.status := rfl

@[simp] theorem stackHandlerTable_POP :
    stackHandlerTable .POP = some popHandler := by
  unfold stackHandlerTable
  rw [HandlerTable.setHandler_ne]
  · simp
  · decide

@[simp] theorem stackHandlerTable_PUSH0 :
    stackHandlerTable .PUSH0 = some push0Handler := by
  simp [stackHandlerTable]

@[simp] theorem dispatchOpcode?_stackHandlerTable_POP (state : EvmState) :
    HandlerTable.dispatchOpcode? stackHandlerTable .POP state =
      some (popHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_stackHandlerTable_POP (state : EvmState) :
    HandlerTable.dispatchOpcode stackHandlerTable .POP state =
      popHandler state := by
  simp [HandlerTable.dispatchOpcode]

@[simp] theorem dispatchOpcode?_stackHandlerTable_PUSH0 (state : EvmState) :
    HandlerTable.dispatchOpcode? stackHandlerTable .PUSH0 state =
      some (push0Handler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_stackHandlerTable_PUSH0 (state : EvmState) :
    HandlerTable.dispatchOpcode stackHandlerTable .PUSH0 state =
      push0Handler state := by
  simp [HandlerTable.dispatchOpcode]

end StackHandlers

end EvmAsm.Evm64
