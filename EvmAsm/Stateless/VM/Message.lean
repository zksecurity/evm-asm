/-
  EvmAsm.Stateless.VM.Message

  Message-call frame record. Mirrors Python's `Message` /
  `MessageCall` dataclasses in `forks/amsterdam/vm/`.

  ## Fields

      struct Message {
          caller        : Address
          target        : Address                # 0x00..00 for CREATE
          value         : U256
          data          : Bytes                  # calldata
          gas           : Uint                   # gas available
          depth         : u8                     # 0..1024
          code          : Bytes                  # to-execute bytecode
          code_address  : Address                # what the code came from
          should_transfer : bool                 # false for STATICCALL
          is_static     : bool                   # STATIC context
          accessed_addresses : set[Address]      # warm/cold
          accessed_storage   : set[(Address, Slot)]
      }

  ## Frame stack

  Each CALL / CREATE / STATICCALL / DELEGATECALL pushes a new
  Message frame. Max depth 1024 (per EIP-150).

  Storage layout: per-frame slot in `EVM_FRAME_STACK` (256 KiB
  total, sized for 1024 × 256 bytes per frame at the upper bound).

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.VM.Message

-- TODO(stateless-vm): expose Message record + helpers.

end EvmAsm.Stateless.VM.Message
