/-
  EvmAsm.Evm64.CodeHandlers

  Pure handler-table entries for code-inspection opcodes currently exposed by
  `EvmState` (GH #107).
-/

import EvmAsm.Evm64.HandlerTable

namespace EvmAsm.Evm64
namespace CodeHandlers

/-- Pure CODESIZE handler. The interpreter state carries the bytecode length
    explicitly as `codeLen`; gas and PC charging belong to later wrappers. -/
def codeSizeHandler : OpcodeHandler :=
  fun state => state.withStack (BitVec.ofNat 256 state.codeLen :: state.stack)

/-- Lookup surface for code-inspection opcode handlers currently supported at
    the pure `EvmState` level. Distinctive token:
    CodeHandlers.codeSizeHandlerTable #107. -/
def codeHandler? : EvmOpcode → Option OpcodeHandler
  | .CODESIZE => some codeSizeHandler
  | _ => none

/-- Handler table containing currently supported code-inspection entries. -/
def codeHandlerTable : HandlerTable :=
  codeHandler?

@[simp] theorem codeSizeHandler_stack (state : EvmState) :
    (codeSizeHandler state).stack =
      BitVec.ofNat 256 state.codeLen :: state.stack := rfl

@[simp] theorem codeSizeHandler_status (state : EvmState) :
    (codeSizeHandler state).status = state.status := rfl

@[simp] theorem codeSizeHandler_code (state : EvmState) :
    (codeSizeHandler state).code = state.code := rfl

@[simp] theorem codeSizeHandler_codeLen (state : EvmState) :
    (codeSizeHandler state).codeLen = state.codeLen := rfl

@[simp] theorem codeHandlerTable_eq :
    codeHandlerTable = codeHandler? := rfl

@[simp] theorem codeHandler?_CODESIZE :
    codeHandler? .CODESIZE = some codeSizeHandler := rfl

@[simp] theorem codeHandlerTable_CODESIZE :
    codeHandlerTable .CODESIZE = some codeSizeHandler := rfl

theorem dispatchOpcode?_codeHandlerTable_CODESIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? codeHandlerTable .CODESIZE state =
      some (codeSizeHandler state) := by
  exact HandlerTable.dispatchOpcode?_some
    codeHandlerTable_CODESIZE state

theorem dispatchOpcode_codeHandlerTable_CODESIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode codeHandlerTable .CODESIZE state =
      codeSizeHandler state := by
  exact HandlerTable.dispatchOpcode_some
    codeHandlerTable_CODESIZE state

end CodeHandlers
end EvmAsm.Evm64
