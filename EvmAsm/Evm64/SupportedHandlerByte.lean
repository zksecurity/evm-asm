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

theorem dispatchByte_supported_of_decode
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state := by
  exact HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode

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

end SupportedHandlerByte
end EvmAsm.Evm64
