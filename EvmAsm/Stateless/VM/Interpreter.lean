/-
  EvmAsm.Stateless.VM.Interpreter

  Top-level EVM interpreter. Mirrors Python's `execute_message`
  in `forks/amsterdam/vm/interpreter.py`.

  ## Loop

      def execute_message(message, env):
          frame = MessageFrame(message)
          while frame.pc < len(frame.code):
              opcode = frame.code[frame.pc]
              handler = OPCODES[opcode]
              gas_cost = compute_gas(opcode, frame)
              if frame.gas < gas_cost:
                  return OutOfGas
              frame.gas -= gas_cost
              handler(frame, env)
              frame.pc += 1   # or jump-aware
          return Success(frame.output, frame.gas_remaining)

  ## RISC-V plan

  Reuse the M5b dispatch loop already in
  `EvmAsm/Codegen/Programs.lean::tinyInterpDispatchPrologue`:

  - `_start` block initialises code pointer + value stack pointer.
  - Per-opcode handlers (from `EvmAsm/Evm64/<Op>/Program.lean`)
    are wrapped as subroutines with a JALR-based return.
  - 256-entry jump table dispatches on the fetched opcode byte.

  Gas accounting + memory expansion + call/create depth tracking
  are wrapped around the dispatch loop. Failure modes (out-of-gas,
  invalid opcode, depth-overflow) route to `unimplemented_exit`
  with specific reason codes -- or, when STF semantics demand
  REVERT-without-abort, are surfaced as `(success=false,
  gas_used)` outputs.

  ## What's already proven

  52 opcodes (per `PLAN.md`): arithmetic, bitwise, shift,
  comparison, stack, byte/sign-extend. These wire into the
  dispatcher and inherit their `cpsTripleWithin` specs.

  ## What's deliberately Unimplemented

  - All 17 precompile addresses (0x01..0x14): route to
    `Stateless.VM.Precompiles`, which routes to
    `unimplemented_exit`.
  - SLOAD / SSTORE (per `PLAN.md` Phase 5).
  - CALL / CREATE family (require deeper recursion than M5b).
  - LOG (no observable effect in the STF skeleton).
  - SELFDESTRUCT (EIP-6049 -- semantics changing, scope deferred).

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.VM.Interpreter

-- TODO(stateless-vm): expose `execute_message(msg, env) ->
-- (output, gas_used, success)` driver. Composes the dispatcher
-- from `EvmAsm.Codegen.Programs` with new gas/memory frame
-- tracking.

end EvmAsm.Stateless.VM.Interpreter
