/-
  EvmAsm.Evm64.SupportedHandlerByte

  Raw-byte dispatch bridge for the combined supported interpreter handler
  table (GH #106 / GH #107).
-/

import EvmAsm.Evm64.HandlerTableByte
import EvmAsm.Evm64.SupportedHandlers

namespace EvmAsm.Evm64
namespace SupportedHandlerByte

theorem dispatchByte_supported_of_lookup
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      handler state := by
  rw [HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state

theorem dispatchByte_supported_of_lookup_status
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (handler state).status := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]

theorem dispatchByte_supported_of_decode
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state := by
  exact HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode

theorem dispatchByte_supported_of_decode_status
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state).status := by
  rw [dispatchByte_supported_of_decode h_decode state]

/--
Byte-level dispatch of a decoded valid PUSH opcode through the combined
supported-handler table has the same program-counter and stack effect as the
executable PUSH bridge.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_effectFromCode #101 #107.
-/
theorem dispatchByte_supported_PUSH_effectFromCode
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [dispatchByte_supported_of_decode h_decode state]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    h_valid state

/--
Status projection for byte-level dispatch of a decoded valid PUSH opcode
through the combined supported-handler table.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_status #101 #107.
-/
theorem dispatchByte_supported_PUSH_status
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      state.status := by
  rw [dispatchByte_supported_of_decode h_decode state]
  rw [HandlerTable.dispatchOpcode_some
    (SupportedHandlers.supportedHandlerTable_PUSH_of_valid h_valid) state]
  exact PushHandlers.pushHandler_status n state

/--
Concrete STOP byte dispatch through the combined supported-handler table
terminates the state successfully.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_byte #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state = state.stop := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_STOP
    SupportedHandlers.supportedHandlerTable_STOP state

@[simp] theorem dispatchByte_supported_STOP_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state).status = .stopped := by
  rw [dispatchByte_supported_STOP_byte]
  exact EvmState.stop_status state

theorem dispatchByte_supported_INVALID_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state = state.invalid := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_INVALID
    SupportedHandlers.supportedHandlerTable_INVALID state

@[simp] theorem dispatchByte_supported_INVALID_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_INVALID_byte]
  exact EvmState.invalid_status state

theorem dispatchByte_supported_undecoded
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  exact HandlerTable.dispatchByte_undecoded
    SupportedHandlers.supportedHandlerTable b state h_decode

theorem dispatchByte_supported_undecoded_status
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  exact HandlerTable.dispatchByte_undecoded_status
    SupportedHandlers.supportedHandlerTable b state h_decode

/--
Byte-level dispatch of any byte that decodes to STOP through the combined
supported-handler table executes the `state.stop` step. Generalises the
concrete `dispatchByte_supported_STOP_byte` (which is the `b = 0x00` instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.stop := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_STOP state]
  rfl

/-- Status projection of `dispatchByte_supported_STOP_of_decode`. -/
theorem dispatchByte_supported_STOP_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .stopped := by
  rw [dispatchByte_supported_STOP_of_decode h_decode state]
  exact EvmState.stop_status state

/--
Byte-level dispatch of any byte that decodes to INVALID through the combined
supported-handler table executes the `state.invalid` step. Generalises the
concrete `dispatchByte_supported_INVALID_byte` (which is the `b = 0xfe`
instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_INVALID_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_INVALID_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_INVALID state]
  rfl

/-- Status projection of `dispatchByte_supported_INVALID_of_decode`. -/
theorem dispatchByte_supported_INVALID_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  rw [dispatchByte_supported_INVALID_of_decode h_decode state]
  exact EvmState.invalid_status state

end SupportedHandlerByte
end EvmAsm.Evm64
