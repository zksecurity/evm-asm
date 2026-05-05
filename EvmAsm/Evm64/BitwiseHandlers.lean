/-
  EvmAsm.Evm64.BitwiseHandlers

  Pure handler-table entries for bitwise opcodes (GH #107).
-/

import EvmAsm.Evm64.HandlerTable

namespace EvmAsm.Evm64
namespace BitwiseHandlers

/-- Pure stack transform for binary bitwise opcodes. -/
def binaryStack? (op : EvmWord → EvmWord → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: b :: rest => some (op a b :: rest)
  | _ => none

/-- Pure stack transform for unary bitwise opcodes. -/
def unaryStack? (op : EvmWord → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: rest => some (op a :: rest)
  | [] => none

def binaryHandler (op : EvmWord → EvmWord → EvmWord) : OpcodeHandler :=
  fun state =>
    match binaryStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

def unaryHandler (op : EvmWord → EvmWord) : OpcodeHandler :=
  fun state =>
    match unaryStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid

def andHandler : OpcodeHandler :=
  binaryHandler (fun a b => a &&& b)

def orHandler : OpcodeHandler :=
  binaryHandler (fun a b => a ||| b)

def xorHandler : OpcodeHandler :=
  binaryHandler (fun a b => a ^^^ b)

def notHandler : OpcodeHandler :=
  unaryHandler (fun a => ~~~a)

/-- Lookup surface for bitwise handlers. -/
def bitwiseHandler? : EvmOpcode → Option OpcodeHandler
  | .AND => some andHandler
  | .OR => some orHandler
  | .XOR => some xorHandler
  | .NOT => some notHandler
  | _ => none

/-- Handler table containing AND/OR/XOR/NOT entries.
    Distinctive token: BitwiseHandlers.bitwiseHandlerTable #107. -/
def bitwiseHandlerTable : HandlerTable :=
  bitwiseHandler?

@[simp] theorem binaryStack?_two
    (op : EvmWord → EvmWord → EvmWord)
    (a b : EvmWord) (rest : List EvmWord) :
    binaryStack? op (a :: b :: rest) = some (op a b :: rest) := rfl

@[simp] theorem unaryStack?_one
    (op : EvmWord → EvmWord) (a : EvmWord) (rest : List EvmWord) :
    unaryStack? op (a :: rest) = some (op a :: rest) := rfl

@[simp] theorem binaryStack?_nil
    (op : EvmWord → EvmWord → EvmWord) :
    binaryStack? op [] = none := rfl

@[simp] theorem unaryStack?_nil
    (op : EvmWord → EvmWord) :
    unaryStack? op [] = none := rfl

theorem binaryHandler_stack_of_binaryStack?_some
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    {stack' : List EvmWord}
    (h_stack : binaryStack? op state.stack = some stack') :
    (binaryHandler op state).stack = stack' := by
  simp [binaryHandler, h_stack]

theorem unaryHandler_stack_of_unaryStack?_some
    {op : EvmWord → EvmWord} {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? op state.stack = some stack') :
    (unaryHandler op state).stack = stack' := by
  simp [unaryHandler, h_stack]

theorem binaryHandler_status_of_binaryStack?_none
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    (h_stack : binaryStack? op state.stack = none) :
    (binaryHandler op state).status = .error := by
  simp [binaryHandler, h_stack]

theorem unaryHandler_status_of_unaryStack?_none
    {op : EvmWord → EvmWord} {state : EvmState}
    (h_stack : unaryStack? op state.stack = none) :
    (unaryHandler op state).status = .error := by
  simp [unaryHandler, h_stack]

@[simp] theorem andHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (andHandler { state with stack := a :: b :: rest }).stack =
      (a &&& b) :: rest := rfl

@[simp] theorem orHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (orHandler { state with stack := a :: b :: rest }).stack =
      (a ||| b) :: rest := rfl

@[simp] theorem xorHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (xorHandler { state with stack := a :: b :: rest }).stack =
      (a ^^^ b) :: rest := rfl

@[simp] theorem notHandler_stack
    (a : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (notHandler { state with stack := a :: rest }).stack =
      (~~~a) :: rest := rfl

@[simp] theorem bitwiseHandlerTable_eq :
    bitwiseHandlerTable = bitwiseHandler? := rfl

@[simp] theorem bitwiseHandler?_AND :
    bitwiseHandler? .AND = some andHandler := rfl

@[simp] theorem bitwiseHandler?_OR :
    bitwiseHandler? .OR = some orHandler := rfl

@[simp] theorem bitwiseHandler?_XOR :
    bitwiseHandler? .XOR = some xorHandler := rfl

@[simp] theorem bitwiseHandler?_NOT :
    bitwiseHandler? .NOT = some notHandler := rfl

theorem dispatchOpcode?_bitwiseHandlerTable_AND
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .AND state =
      some (andHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_AND state

theorem dispatchOpcode?_bitwiseHandlerTable_OR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .OR state =
      some (orHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_OR state

theorem dispatchOpcode?_bitwiseHandlerTable_XOR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .XOR state =
      some (xorHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_XOR state

theorem dispatchOpcode?_bitwiseHandlerTable_NOT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .NOT state =
      some (notHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_NOT state

theorem dispatchOpcode_bitwiseHandlerTable_AND
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .AND state =
      andHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_AND state

theorem dispatchOpcode_bitwiseHandlerTable_OR
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .OR state =
      orHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_OR state

theorem dispatchOpcode_bitwiseHandlerTable_XOR
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .XOR state =
      xorHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_XOR state

theorem dispatchOpcode_bitwiseHandlerTable_NOT
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .NOT state =
      notHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_NOT state

end BitwiseHandlers
end EvmAsm.Evm64
