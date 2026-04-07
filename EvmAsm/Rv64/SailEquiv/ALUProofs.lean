/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for ALU register-register instructions:
  ADD, SUB, AND, OR, XOR.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- ADD: the first proof
-- ============================================================================

/-- ADD rd rs1 rs2: the SAIL execute_RTYPE for rop.ADD produces a state
    that agrees with Rv64's execInstrBr on registers and memory.
    PC is not asserted (handled at the step level). -/
theorem add_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      (∀ r : Reg, sailRegVal s_sail' r =
        some ((execInstrBr s_rv (.ADD rd rs1 rs2)).getReg r)) ∧
      s_sail'.mem = s_sail.mem := by
  sorry

end EvmAsm.Rv64.SailEquiv
