/-
  EvmAsm.Rv64

  Root import file for the 64-bit RISC-V machine model (RV64IM).
-/

-- SyscallSpecs transitively imports Basic, Instructions, SepLogic, Execution,
-- CPSSpec, GenericSpecs, InstructionSpecs, ByteOps, HalfwordOps, WordOps,
-- and Tactics.SpecDb.
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.PerfTrace
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XCancel
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.LiftSpec
import EvmAsm.Rv64.RLP
import EvmAsm.Rv64.RegOpsAttr
import EvmAsm.Rv64.RegOps
import EvmAsm.Rv64.AddrNormAttr
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ByteAlgAttr
import EvmAsm.Rv64.ByteAlg
-- SailEquiv leaves (each transitively imports ALUProofs → MonadLemmas → StateRel).
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.BranchProofs
import EvmAsm.Rv64.SailEquiv.MemProofs
import EvmAsm.Rv64.SailEquiv.MExtProofs
