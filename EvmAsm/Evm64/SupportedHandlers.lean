/-
  EvmAsm.Evm64.SupportedHandlers

  Combined pure handler table for the currently shipped interpreter handler
  families (GH #107).
-/

import EvmAsm.Evm64.HandlerTableCompose
import EvmAsm.Evm64.TerminatingHandlers
import EvmAsm.Evm64.StackHandlers
import EvmAsm.Evm64.PushHandlers
import EvmAsm.Evm64.ControlHandlers
import EvmAsm.Evm64.EnvHandlers
import EvmAsm.Evm64.ArithmeticHandlers
import EvmAsm.Evm64.BitwiseHandlers
import EvmAsm.Evm64.ComparisonHandlers
import EvmAsm.Evm64.ShiftHandlers
import EvmAsm.Evm64.CalldataHandlers
import EvmAsm.Evm64.DupSwapHandlers

namespace EvmAsm.Evm64

namespace SupportedHandlers

/--
One left-biased table containing every pure handler family currently modeled
on `main` for the interpreter.

Distinctive token: SupportedHandlers.supportedHandlerTable #107.
-/
def supportedHandlerTable : HandlerTable :=
  HandlerTable.orElse TerminatingHandlers.terminatingHandlerTable <|
  HandlerTable.orElse StackHandlers.stackHandlerTable <|
  HandlerTable.orElse PushHandlers.pushHandlerTable <|
  HandlerTable.orElse ControlHandlers.controlHandlerTable <|
  HandlerTable.orElse EnvHandlers.simpleEnvHandlerTable <|
  HandlerTable.orElse ArithmeticHandlers.arithmeticHandlerTable <|
  HandlerTable.orElse BitwiseHandlers.bitwiseHandlerTable <|
  HandlerTable.orElse ComparisonHandlers.comparisonHandlerTable
    (HandlerTable.orElse ShiftHandlers.shiftHandlerTable
      (HandlerTable.orElse CalldataHandlers.calldataHandlerTable
        DupSwapHandlers.dupSwapHandlerTable))

theorem lookup_of_terminating
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup :
      TerminatingHandlers.terminatingHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_stack
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_lookup : StackHandlers.stackHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_control
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_lookup : ControlHandlers.controlHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_push
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_lookup : PushHandlers.pushHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_env
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_lookup : EnvHandlers.simpleEnvHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_arithmetic
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_lookup : ArithmeticHandlers.arithmeticHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_bitwise
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_lookup : BitwiseHandlers.bitwiseHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_comparison
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_lookup : ComparisonHandlers.comparisonHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_shift
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_lookup : ShiftHandlers.shiftHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  exact HandlerTable.orElse_left_some h_lookup

theorem lookup_of_dupSwap
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_shift : ShiftHandlers.shiftHandlerTable opcode = none)
    (h_calldata : CalldataHandlers.calldataHandlerTable opcode = none)
    (h_lookup : DupSwapHandlers.dupSwapHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  rw [HandlerTable.orElse_left_none h_shift]
  rw [HandlerTable.orElse_left_none h_calldata]
  exact h_lookup

theorem lookup_of_calldata
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_terminating :
      TerminatingHandlers.terminatingHandlerTable opcode = none)
    (h_stack : StackHandlers.stackHandlerTable opcode = none)
    (h_push : PushHandlers.pushHandlerTable opcode = none)
    (h_control : ControlHandlers.controlHandlerTable opcode = none)
    (h_env : EnvHandlers.simpleEnvHandlerTable opcode = none)
    (h_arithmetic : ArithmeticHandlers.arithmeticHandlerTable opcode = none)
    (h_bitwise : BitwiseHandlers.bitwiseHandlerTable opcode = none)
    (h_comparison : ComparisonHandlers.comparisonHandlerTable opcode = none)
    (h_shift : ShiftHandlers.shiftHandlerTable opcode = none)
    (h_lookup : CalldataHandlers.calldataHandlerTable opcode = some handler) :
    supportedHandlerTable opcode = some handler := by
  unfold supportedHandlerTable
  rw [HandlerTable.orElse_left_none h_terminating]
  rw [HandlerTable.orElse_left_none h_stack]
  rw [HandlerTable.orElse_left_none h_push]
  rw [HandlerTable.orElse_left_none h_control]
  rw [HandlerTable.orElse_left_none h_env]
  rw [HandlerTable.orElse_left_none h_arithmetic]
  rw [HandlerTable.orElse_left_none h_bitwise]
  rw [HandlerTable.orElse_left_none h_comparison]
  rw [HandlerTable.orElse_left_none h_shift]
  exact HandlerTable.orElse_left_some h_lookup

theorem dispatchOpcode?_of_lookup
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? supportedHandlerTable opcode state =
      some (handler state) :=
  HandlerTable.dispatchOpcode?_some h_lookup state

theorem dispatchOpcode_of_lookup
    {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchOpcode supportedHandlerTable opcode state =
      handler state :=
  HandlerTable.dispatchOpcode_some h_lookup state

@[simp] theorem supportedHandlerTable_STOP :
    supportedHandlerTable .STOP =
      some TerminatingHandlers.stopHandler := by
  exact lookup_of_terminating TerminatingHandlers.terminatingHandlerTable_STOP

@[simp] theorem supportedHandlerTable_PUSH0 :
    supportedHandlerTable .PUSH0 =
      some StackHandlers.push0Handler := by
  exact lookup_of_stack
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    StackHandlers.stackHandlerTable_PUSH0

@[simp] theorem supportedHandlerTable_CALLDATASIZE :
    supportedHandlerTable .CALLDATASIZE =
      some CalldataHandlers.callDataSizeHandler := by
  exact lookup_of_calldata
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    CalldataHandlers.calldataHandlerTable_CALLDATASIZE

theorem supportedHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true) :
    supportedHandlerTable (.PUSH n) =
      some (PushHandlers.pushHandler n) := by
  exact lookup_of_push
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (PushHandlers.pushHandler?_PUSH_of_valid h_valid)

theorem supportedHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true) :
    supportedHandlerTable (.DUP n) =
      some (DupSwapHandlers.dupHandler n) := by
  exact lookup_of_dupSwap
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    (by simp [CalldataHandlers.calldataHandlerTable,
      CalldataHandlers.calldataHandler?])
    (DupSwapHandlers.dupSwapHandler?_DUP_of_valid h_valid)

theorem supportedHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true) :
    supportedHandlerTable (.SWAP n) =
      some (DupSwapHandlers.swapHandler n) := by
  exact lookup_of_dupSwap
    (by simp [TerminatingHandlers.terminatingHandlerTable, HandlerTable.setHandler])
    (by simp [StackHandlers.stackHandlerTable, HandlerTable.setHandler])
    (by simp [PushHandlers.pushHandlerTable, PushHandlers.pushHandler?])
    (by simp [ControlHandlers.controlHandlerTable, ControlHandlers.controlHandler?])
    (by rfl)
    (by simp [ArithmeticHandlers.arithmeticHandlerTable,
      ArithmeticHandlers.arithmeticHandler?])
    (by simp [BitwiseHandlers.bitwiseHandlerTable, BitwiseHandlers.bitwiseHandler?])
    (by simp [ComparisonHandlers.comparisonHandlerTable,
      ComparisonHandlers.comparisonHandler?])
    (by simp [ShiftHandlers.shiftHandlerTable, ShiftHandlers.shiftHandler?])
    (by simp [CalldataHandlers.calldataHandlerTable,
      CalldataHandlers.calldataHandler?])
    (DupSwapHandlers.dupSwapHandler?_SWAP_of_valid h_valid)

end SupportedHandlers

end EvmAsm.Evm64
