/-
  EvmAsm.Rv64

  Root import file for the 64-bit RISC-V machine model (RV64IM).
-/

-- SyscallSpecs transitively imports Basic, Instructions, Program, SepLogic,
-- Execution, CPSSpec, GenericSpecs, InstructionSpecs, ByteOps, HalfwordOps,
-- WordOps, and Tactics.SpecDb. ControlFlow also covers Program directly.
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
-- RunBlock → SeqFrame → {XCancel, PerfTrace, InstructionSpecs} + SpecDb.
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.LiftSpec
import EvmAsm.Rv64.RLP
-- The `*Attr` files are imported by their non-Attr counterparts.
import EvmAsm.Rv64.RegOps
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ByteAlg
-- SailEquiv leaves (each transitively imports ALUProofs → MonadLemmas → StateRel).
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.BranchProofs
import EvmAsm.Rv64.SailEquiv.MemProofs
import EvmAsm.Rv64.SailEquiv.MExtProofs
