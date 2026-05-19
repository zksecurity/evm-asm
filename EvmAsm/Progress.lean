/-
  EvmAsm.Progress

  Drift-proof registry of per-opcode verification state across the
  143 EVM opcode bytes modeled by `EvmAsm.Evm64.EvmOpcode`. The
  registry is the single source of truth for the coverage tables in
  `PROGRESS.md`; renaming or deleting a theorem named below fails
  this file's elaboration via the witness `abbrev`s at the bottom.

  See `scripts/progress-report.sh` for how the registry is consumed.
  See `PROGRESS.md` for the rendered report.

  Conventions:
  * `ProofTier` classifies an `EvmOpcode` constructor by how deep
    its verification reaches.
  * `OpcodeEntry` is one row of the registry.
  * Parameterized opcode families (`DUP n`, `SWAP n`, `LOG kind`)
    are one row each.
  * Counts are kernel-checked via `by decide` theorems.
-/

import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.Sub.Spec
import EvmAsm.Evm64.Multiply.Spec
import EvmAsm.Evm64.SignExtend.Spec
import EvmAsm.Evm64.And.Spec
import EvmAsm.Evm64.Or.Spec
import EvmAsm.Evm64.Xor.Spec
import EvmAsm.Evm64.Not.Spec
import EvmAsm.Evm64.Byte.Spec
import EvmAsm.Evm64.Shift.Semantic
import EvmAsm.Evm64.Shift.ShlSemantic
import EvmAsm.Evm64.Shift.SarSemantic
import EvmAsm.Evm64.Lt.Spec
import EvmAsm.Evm64.Gt.Spec
import EvmAsm.Evm64.Eq.Spec
import EvmAsm.Evm64.IsZero.Spec
import EvmAsm.Evm64.Slt.Spec
import EvmAsm.Evm64.Sgt.Spec
import EvmAsm.Evm64.Pop.Spec
import EvmAsm.Evm64.Push0.Spec
import EvmAsm.Evm64.Push.Spec
import EvmAsm.Evm64.Dup.Spec
import EvmAsm.Evm64.Swap.Spec
import EvmAsm.Evm64.MSize.Spec
import EvmAsm.Evm64.MStore8.Spec
import EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec
import EvmAsm.Evm64.MStore.UnalignedFramedStackSpec
import EvmAsm.Evm64.DivMod.Spec.Unified
import EvmAsm.Evm64.SDiv.Spec
import EvmAsm.Evm64.AddMod.Spec
import EvmAsm.Evm64.Env.Wrappers
import EvmAsm.Evm64.Calldata.SizeSpec
import EvmAsm.Evm64.Calldata.CopySpec

namespace EvmAsm.Progress

/-- Verification depth for one EVM opcode (or parameterized family). -/
inductive ProofTier
  /-- Top-level stack-level Hoare triple is proven for the full opcode. -/
  | proven
  /-- Program defined + `EvmWord.<op>_correct` theorem proven, but no
      top-level `evm_<op>_stack_spec_within` wrap yet. -/
  | partly
  /-- Pure executable-spec / handler / bridge semantics only; no RV64
      subroutine produces the EVM result for this opcode. -/
  | execSpec
  /-- Not represented in `EvmOpcode` yet (e.g. unimplemented EIPs). -/
  | notStarted
  deriving DecidableEq, BEq, Repr

/-- One row of the progress registry. -/
structure OpcodeEntry where
  /-- Display name; usually the EVM mnemonic. Parameterized families
      use a width range, e.g. "PUSH1" or "DUP1..16". -/
  name : String
  /-- Verification depth. -/
  tier : ProofTier
  /-- Best-available witness theorem name, for diff readability. -/
  proofRef : Option String
  /-- Optional short note for the rendered report. -/
  notes : String := ""
  deriving Repr

/-! ## Registry

    Ordering follows EVM opcode bytes 0x00..0xff for easy cross-reference
    with `EvmAsm.Evm64.EvmOpcode.byte?`. -/
def registry : List OpcodeEntry := [
  -- Stop and arithmetic (0x00..0x0b)
  ⟨"STOP", .execSpec, none,
      "executable-spec only; `Termination.lean` + `TerminatingArgs.lean`"⟩,
  ⟨"ADD", .proven, some "evm_add_stack_spec_within", "N=30"⟩,
  ⟨"MUL", .proven, some "evm_mul_stack_spec_within", "N=63"⟩,
  ⟨"SUB", .proven, some "evm_sub_stack_spec_within", "N=30"⟩,
  ⟨"DIV", .partly, some "evm_div_stack_spec",
      "stack spec parametric over DivStackSpecCase (bzero / n=1,2,3, all " ++
      "require b.getLimbN 3 = 0); n=4 path not covered. Executable evm_div " ++
      "uses divK_div128_v4 (PR #4992, full Knuth Alg D). Full-domain " ++
      "unconditional closure tracked by bead evm-asm-9iqmw / gh-61"⟩,
  ⟨"SDIV", .partly, some "evm_sdiv_exact_callable_return_stack_spec_within",
      "callable+dispatch shim; evm_sdiv_stack_spec_within conditional on " ++
      "hStack (discharged for divisor=0 and n=1/2/3/n4-call-skip); blocked " ++
      "on DIV/MOD spec-layer migration (bead evm-asm-9iqmw)"⟩,
  ⟨"MOD", .partly, some "evm_mod_stack_spec",
      "stack spec parametric over ModStackSpecCase (bzero / n=1,2,3, all " ++
      "require b.getLimbN 3 = 0); n=4 path not covered. Executable evm_mod " ++
      "uses divK_div128_v4 (PR #4992). Full-domain unconditional closure " ++
      "tracked by bead evm-asm-9iqmw / gh-61"⟩,
  ⟨"SMOD", .partly, none, "smod_correct proven; no top-level Hoare triple"⟩,
  ⟨"ADDMOD", .partly, some "evm_addmod_b0_n0_spec_within",
      "addmod_correct proven; only b=0 stack-spec done"⟩,
  ⟨"MULMOD", .partly, none, "mulmod_correct proven; no top-level Hoare triple"⟩,
  ⟨"EXP", .partly, none, "exp_correct proven; program in active development"⟩,
  ⟨"SIGNEXTEND", .proven, some "evm_signextend_stack_spec_within", "N=28"⟩,

  -- Comparison and bitwise (0x10..0x1d)
  ⟨"LT", .proven, some "evm_lt_stack_spec_within", "N=26"⟩,
  ⟨"GT", .proven, some "evm_gt_stack_spec_within", "N=26"⟩,
  ⟨"SLT", .proven, some "evm_slt_stack_spec_within", "N=25"⟩,
  ⟨"SGT", .proven, some "evm_sgt_stack_spec_within", "N=25"⟩,
  ⟨"EQ", .proven, some "evm_eq_stack_spec_within", "N=21"⟩,
  ⟨"ISZERO", .proven, some "evm_iszero_stack_spec_within", "N=12"⟩,
  ⟨"AND", .proven, some "evm_and_stack_spec_within", "N=17"⟩,
  ⟨"OR", .proven, some "evm_or_stack_spec_within", "N=17"⟩,
  ⟨"XOR", .proven, some "evm_xor_stack_spec_within", "N=17"⟩,
  ⟨"NOT", .proven, some "evm_not_stack_spec_within", "N=12"⟩,
  ⟨"BYTE", .proven, some "evm_byte_stack_spec_within", "N=29"⟩,
  ⟨"SHL", .proven, some "evm_shl_stack_spec_within", "N=90"⟩,
  ⟨"SHR", .proven, some "evm_shr_stack_spec_within", "N=90"⟩,
  ⟨"SAR", .proven, some "evm_sar_stack_spec_within", "N=95"⟩,

  -- KECCAK (0x20)
  ⟨"KECCAK256", .execSpec, none,
      "delegated to zkvm_keccak256 accelerator; EL/Keccak*Bridge"⟩,

  -- Environment (0x30..0x3e)
  ⟨"ADDRESS", .proven, some "Env.evm_address_stack_spec_within", ""⟩,
  ⟨"BALANCE", .execSpec, none, "not in EvmOpcode enum yet"⟩,
  ⟨"ORIGIN", .proven, some "Env.evm_origin_stack_spec_within", ""⟩,
  ⟨"CALLER", .proven, some "Env.evm_caller_stack_spec_within", ""⟩,
  ⟨"CALLVALUE", .proven, some "Env.evm_callvalue_stack_spec_within", ""⟩,
  ⟨"CALLDATALOAD", .execSpec, none,
      "program in Calldata/LoadProgram.lean; no stack spec yet"⟩,
  ⟨"CALLDATASIZE", .proven,
      some "Calldata.evm_calldatasize_stack_spec_within", ""⟩,
  ⟨"CALLDATACOPY", .partly,
      some "Calldata.evm_calldatacopy_preamble_stack_spec_within",
      "preamble + partial memory effect; full loop pending"⟩,
  ⟨"CODESIZE", .execSpec, none, "env read in Code/Basic.lean"⟩,
  ⟨"CODECOPY", .execSpec, none, "Code/CopyExec.lean + CopyMemory.lean"⟩,
  ⟨"GASPRICE", .proven, some "Env.evm_gasprice_stack_spec_within", ""⟩,
  ⟨"EXTCODESIZE", .execSpec, none, "not in EvmOpcode enum yet"⟩,
  ⟨"EXTCODECOPY", .execSpec, none, "not in EvmOpcode enum yet"⟩,
  ⟨"RETURNDATASIZE", .execSpec, none,
      "ReturnDataHandlers.lean; table dispatch only"⟩,
  ⟨"RETURNDATACOPY", .execSpec, none, "ReturnData/CopyExec + CopyMemory"⟩,
  ⟨"EXTCODEHASH", .execSpec, none, "not in EvmOpcode enum yet"⟩,

  -- Block (0x40..0x4a)
  ⟨"BLOCKHASH", .execSpec, none, "env-bridge level"⟩,
  ⟨"COINBASE", .proven, some "Env.evm_coinbase_stack_spec_within", ""⟩,
  ⟨"TIMESTAMP", .proven, some "Env.evm_timestamp_stack_spec_within", ""⟩,
  ⟨"NUMBER", .proven, some "Env.evm_number_stack_spec_within", ""⟩,
  ⟨"PREVRANDAO", .proven, some "Env.evm_prevrandao_stack_spec_within", ""⟩,
  ⟨"GASLIMIT", .proven, some "Env.evm_gaslimit_stack_spec_within", ""⟩,
  ⟨"CHAINID", .proven, some "Env.evm_chainid_stack_spec_within", ""⟩,
  ⟨"SELFBALANCE", .proven, some "Env.evm_selfbalance_stack_spec_within", ""⟩,
  ⟨"BASEFEE", .proven, some "Env.evm_basefee_stack_spec_within", ""⟩,
  ⟨"BLOBHASH", .execSpec, none, "env-bridge level"⟩,
  ⟨"BLOBBASEFEE", .execSpec, none, "env-bridge level"⟩,

  -- Stack/Memory/Storage/Flow (0x50..0x5f)
  ⟨"POP", .proven, some "evm_pop_stack_spec_within", "N=1"⟩,
  ⟨"MLOAD", .proven, some "evm_mload_stack_spec_within",
      "aligned spec proven; unaligned _public variants in progress"⟩,
  ⟨"MSTORE", .proven, some "evm_mstore_stack_spec_within",
      "aligned spec proven; unaligned _public variants in progress"⟩,
  ⟨"MSTORE8", .proven, some "evm_mstore8_stack_spec_within", "N=5"⟩,
  ⟨"SLOAD", .execSpec, none, "Storage*.lean; ECALL → host"⟩,
  ⟨"SSTORE", .execSpec, none, "Storage*.lean; ECALL → host"⟩,
  ⟨"JUMP", .execSpec, none, "handled by interpreter PC update"⟩,
  ⟨"JUMPI", .execSpec, none, "handled by interpreter PC update"⟩,
  ⟨"PC", .execSpec, none, "reads EVM PC from EvmState"⟩,
  ⟨"MSIZE", .proven, some "evm_msize_stack_spec_within", "N=6"⟩,
  ⟨"GAS", .execSpec, none, "reads remaining gas from EvmState"⟩,
  ⟨"JUMPDEST", .execSpec, none, "no-op opcode; gas-only"⟩,
  ⟨"TLOAD", .notStarted, none, "EIP-1153 (Cancun); not in EvmOpcode enum"⟩,
  ⟨"TSTORE", .notStarted, none, "EIP-1153 (Cancun); not in EvmOpcode enum"⟩,
  ⟨"MCOPY", .notStarted, none, "EIP-5656 (Cancun); not in EvmOpcode enum"⟩,
  ⟨"PUSH0", .proven, some "evm_push0_stack_spec_within", "N=5"⟩,

  -- Push family (0x60..0x7f). PUSH1 has its own top-level spec; PUSH2..32
  -- share the parameterized zero-slot spec — see editorial note #2 in
  -- PROGRESS.md.
  ⟨"PUSH1", .proven, some "evm_push1_stack_spec_within", ""⟩,
  ⟨"PUSH2..32", .partly, some "evm_push_zero_slot_full_stack_spec_within",
      "zero-slot only; non-zero-slot path pending; 31 byte-codes"⟩,

  -- Dup/Swap families (0x80..0x9f) — single generic proof each
  ⟨"DUP1..16", .proven, some "evm_dup_stack_spec_within",
      "single proof generic over n=1..16"⟩,
  ⟨"SWAP1..16", .proven, some "evm_swap_stack_spec_within",
      "single proof generic over n=1..16"⟩,

  -- Log family (0xa0..0xa4)
  ⟨"LOG0..4", .execSpec, none,
      "LogArgs + LogDataBridge + LogExecutionBridge; 5 byte-codes"⟩,

  -- System (0xf0..0xff)
  ⟨"CREATE", .execSpec, none,
      "Create.lean + CreateAddress + CreateArgsBridge + CreateEffects"⟩,
  ⟨"CALL", .execSpec, none, "CallArgs + Call*Bridge family"⟩,
  ⟨"CALLCODE", .execSpec, none, "not in EvmOpcode enum yet"⟩,
  ⟨"RETURN", .execSpec, none, "TerminatingArgs + TerminatingExecutionBridge"⟩,
  ⟨"DELEGATECALL", .execSpec, none, "CallArgs kind = .delegatecall"⟩,
  ⟨"CREATE2", .execSpec, none, "shared Create family"⟩,
  ⟨"STATICCALL", .execSpec, none, "CallArgs kind = .staticcall"⟩,
  ⟨"REVERT", .execSpec, none, "TerminatingArgs"⟩,
  ⟨"INVALID", .execSpec, none, "TerminatingArgs"⟩,
  ⟨"SELFDESTRUCT", .execSpec, none, "SelfdestructEffects + terminating bridge"⟩,
]

/-! ## Counts (kernel-checked) -/

/-- Count of registry entries at a given tier. -/
def countTier (t : ProofTier) : Nat :=
  registry.countP (fun e => e.tier == t)

def provenCount     : Nat := countTier .proven
def partialCount    : Nat := countTier .partly
def execSpecCount   : Nat := countTier .execSpec
def notStartedCount : Nat := countTier .notStarted
def totalEntries    : Nat := registry.length

theorem provenCount_eq     : provenCount     = 41 := by decide
theorem partialCount_eq    : partialCount    = 9  := by decide
theorem execSpecCount_eq   : execSpecCount   = 32 := by decide
theorem notStartedCount_eq : notStartedCount = 3  := by decide
theorem totalEntries_eq    : totalEntries    = 85 := by decide

/-! ## Byte-code counts

    Counts opcode *bytes* (not registry entries), expanding the
    parameterized families. Each `OpcodeEntry` whose `name` matches one
    of the families below contributes its width; everything else
    contributes 1. -/

def entryByteCount (e : OpcodeEntry) : Nat :=
  match e.name with
  | "PUSH2..32" => 31
  | "DUP1..16"  => 16
  | "SWAP1..16" => 16
  | "LOG0..4"   => 5
  | _           => 1

def byteCountTier (t : ProofTier) : Nat :=
  (registry.filter (fun e => e.tier == t)).foldl
    (fun acc e => acc + entryByteCount e) 0

def provenBytes     : Nat := byteCountTier .proven
def partialBytes    : Nat := byteCountTier .partly
def execSpecBytes   : Nat := byteCountTier .execSpec
def notStartedBytes : Nat := byteCountTier .notStarted
def totalBytes      : Nat := provenBytes + partialBytes + execSpecBytes + notStartedBytes

theorem provenBytes_eq     : provenBytes     = 71  := by decide
theorem partialBytes_eq    : partialBytes    = 39  := by decide
theorem execSpecBytes_eq   : execSpecBytes   = 36  := by decide
theorem notStartedBytes_eq : notStartedBytes = 3   := by decide
theorem totalBytes_eq      : totalBytes      = 149 := by decide

/-! ## Witness `abbrev`s

    Each `.proven` and `.partly` entry above names a theorem; the
    abbrev below forces its definition to exist. If a theorem is
    renamed or deleted, this file fails to elaborate. Update both
    the registry entry and this section when refactoring.

    Convention: name the abbrev `_<lower>_witness`; mark it
    `private noncomputable` to avoid polluting the namespace. -/

private noncomputable abbrev _add_witness        := @EvmAsm.Evm64.evm_add_stack_spec_within
private noncomputable abbrev _mul_witness        := @EvmAsm.Evm64.evm_mul_stack_spec_within
private noncomputable abbrev _sub_witness        := @EvmAsm.Evm64.evm_sub_stack_spec_within
private noncomputable abbrev _div_witness        := @EvmAsm.Evm64.evm_div_stack_spec
private noncomputable abbrev _sdiv_witness       :=
  @EvmAsm.Evm64.evm_sdiv_exact_callable_return_stack_spec_within
private noncomputable abbrev _mod_witness        := @EvmAsm.Evm64.evm_mod_stack_spec
private noncomputable abbrev _addmod_witness     := @EvmAsm.Evm64.evm_addmod_b0_n0_spec_within
private noncomputable abbrev _signextend_witness := @EvmAsm.Evm64.evm_signextend_stack_spec_within
private noncomputable abbrev _lt_witness         := @EvmAsm.Evm64.evm_lt_stack_spec_within
private noncomputable abbrev _gt_witness         := @EvmAsm.Evm64.evm_gt_stack_spec_within
private noncomputable abbrev _slt_witness        := @EvmAsm.Evm64.evm_slt_stack_spec_within
private noncomputable abbrev _sgt_witness        := @EvmAsm.Evm64.evm_sgt_stack_spec_within
private noncomputable abbrev _eq_witness         := @EvmAsm.Evm64.evm_eq_stack_spec_within
private noncomputable abbrev _iszero_witness     := @EvmAsm.Evm64.evm_iszero_stack_spec_within
private noncomputable abbrev _and_witness        := @EvmAsm.Evm64.evm_and_stack_spec_within
private noncomputable abbrev _or_witness         := @EvmAsm.Evm64.evm_or_stack_spec_within
private noncomputable abbrev _xor_witness        := @EvmAsm.Evm64.evm_xor_stack_spec_within
private noncomputable abbrev _not_witness        := @EvmAsm.Evm64.evm_not_stack_spec_within
private noncomputable abbrev _byte_witness       := @EvmAsm.Evm64.evm_byte_stack_spec_within
private noncomputable abbrev _shl_witness        := @EvmAsm.Evm64.evm_shl_stack_spec_within
private noncomputable abbrev _shr_witness        := @EvmAsm.Evm64.evm_shr_stack_spec_within
private noncomputable abbrev _sar_witness        := @EvmAsm.Evm64.evm_sar_stack_spec_within
private noncomputable abbrev _address_witness    := @EvmAsm.Evm64.Env.evm_address_stack_spec_within
private noncomputable abbrev _origin_witness     := @EvmAsm.Evm64.Env.evm_origin_stack_spec_within
private noncomputable abbrev _caller_witness     := @EvmAsm.Evm64.Env.evm_caller_stack_spec_within
private noncomputable abbrev _callvalue_witness  := @EvmAsm.Evm64.Env.evm_callvalue_stack_spec_within
private noncomputable abbrev _gasprice_witness   := @EvmAsm.Evm64.Env.evm_gasprice_stack_spec_within
private noncomputable abbrev _coinbase_witness   := @EvmAsm.Evm64.Env.evm_coinbase_stack_spec_within
private noncomputable abbrev _timestamp_witness  := @EvmAsm.Evm64.Env.evm_timestamp_stack_spec_within
private noncomputable abbrev _number_witness     := @EvmAsm.Evm64.Env.evm_number_stack_spec_within
private noncomputable abbrev _prevrandao_witness := @EvmAsm.Evm64.Env.evm_prevrandao_stack_spec_within
private noncomputable abbrev _gaslimit_witness   := @EvmAsm.Evm64.Env.evm_gaslimit_stack_spec_within
private noncomputable abbrev _chainid_witness    := @EvmAsm.Evm64.Env.evm_chainid_stack_spec_within
private noncomputable abbrev _selfbalance_witness := @EvmAsm.Evm64.Env.evm_selfbalance_stack_spec_within
private noncomputable abbrev _basefee_witness    := @EvmAsm.Evm64.Env.evm_basefee_stack_spec_within
private noncomputable abbrev _calldatasize_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatasize_stack_spec_within
private noncomputable abbrev _calldatacopy_witness :=
  @EvmAsm.Evm64.Calldata.evm_calldatacopy_preamble_stack_spec_within
private noncomputable abbrev _pop_witness        := @EvmAsm.Evm64.evm_pop_stack_spec_within
private noncomputable abbrev _mload_witness      := @EvmAsm.Evm64.evm_mload_stack_spec_within
private noncomputable abbrev _mstore_witness     := @EvmAsm.Evm64.evm_mstore_stack_spec_within
private noncomputable abbrev _mstore8_witness    := @EvmAsm.Evm64.evm_mstore8_stack_spec_within
private noncomputable abbrev _msize_witness      := @EvmAsm.Evm64.evm_msize_stack_spec_within
private noncomputable abbrev _push0_witness      := @EvmAsm.Evm64.evm_push0_stack_spec_within
private noncomputable abbrev _push1_witness      := @EvmAsm.Evm64.evm_push1_stack_spec_within
private noncomputable abbrev _push_zero_witness  := @EvmAsm.Evm64.evm_push_zero_slot_full_stack_spec_within
private noncomputable abbrev _dup_witness        := @EvmAsm.Evm64.evm_dup_stack_spec_within
private noncomputable abbrev _swap_witness       := @EvmAsm.Evm64.evm_swap_stack_spec_within

end EvmAsm.Progress
