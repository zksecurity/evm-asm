/-
  EvmAsm.Evm64.MemoryHandlers

  Pure memory-metadata handler-table entries for the interpreter handler
  layer (GH #107).
-/

import EvmAsm.Evm64.HandlerTable

namespace EvmAsm.Evm64

namespace MemoryHandlers

/-- EVM word pushed by MSIZE for the current abstract state. -/
def msizeWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.memSize

/-- MSIZE pushes the current EVM memory high-water mark in bytes. -/
def msizeHandler : OpcodeHandler :=
  fun state => state.withStack (msizeWord state :: state.stack)

/-- Lookup just the memory-metadata handler introduced in this slice. -/
def memoryHandler? : EvmOpcode → Option OpcodeHandler
  | .MSIZE => some msizeHandler
  | _ => none

/-- Handler table fragment containing the MSIZE entry.
    Distinctive token: MemoryHandlers.msizeHandlerTable #107. -/
def msizeHandlerTable : HandlerTable :=
  memoryHandler?

@[simp] theorem memoryHandler?_MSIZE :
    memoryHandler? .MSIZE = some msizeHandler := rfl

@[simp] theorem msizeHandler_stack (state : EvmState) :
    (msizeHandler state).stack = msizeWord state :: state.stack := rfl

@[simp] theorem msizeHandler_status (state : EvmState) :
    (msizeHandler state).status = state.status := rfl

@[simp] theorem msizeHandler_memSize (state : EvmState) :
    (msizeHandler state).memSize = state.memSize := rfl

@[simp] theorem msizeHandlerTable_MSIZE :
    msizeHandlerTable .MSIZE = some msizeHandler := rfl

@[simp] theorem dispatchOpcode?_msizeHandlerTable_MSIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? msizeHandlerTable .MSIZE state =
      some (msizeHandler state) := by
  simp [HandlerTable.dispatchOpcode?]

@[simp] theorem dispatchOpcode_msizeHandlerTable_MSIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode msizeHandlerTable .MSIZE state =
      msizeHandler state := by
  simp [HandlerTable.dispatchOpcode]

end MemoryHandlers

end EvmAsm.Evm64
