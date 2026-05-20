/-
  EvmAsm.Stateless.MemoryLayout

  Single source of truth for the address-space layout used by the
  stateless-guest port of `run_stateless_guest`
  (`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`).

  All RISC-V modules under `EvmAsm/Stateless/` agree on the constants
  declared here. Treat this file as the contract: any new module must
  document, in its file header, which regions it reads, writes, and
  leaves untouched, plus which exit ECALLs it can take. Mirrors the
  "memory layout + side effects" convention already used by
  `EvmAsm/Evm64/DivMod/AddrNorm.lean` and the Keccak ECALL bridge.

  ## Top-level map (RV64IM, ZisK host-IO compatible)

  Authoritative ziskemu addresses (see `EvmAsm/Codegen/Driver.lean:68-82`
  for the linker flags and `EvmAsm/Codegen/Programs.lean` for the
  `INPUT_ADDR`/`OUTPUT_ADDR` constants):

  ```
  0x00000020 .. 0x78000000   verified `isValidMemAddr` range
                             (see `EvmAsm/Rv64/Basic.lean:244,247`)
  0x40000000 .. 0x40002000   INPUT_ADDR  (8 KiB, host-supplied SSZ input)
                               [+ 0..8]   ZisK metadata (zero)
                               [+ 8..16]  LE u64 length of first record
                               [+16..]    SSZ-encoded SszStatelessInput
  0x80000000 .. 0xa0000000   .text + .rodata + .bss (ELF `-Ttext=0x80000000`)
  0xa0000000 .. 0xa0010000   .data (`-Tdata=0xa0000000`; small operand
                             seeds for existing build units)
  0xa0010000 .. 0xa0020000   OUTPUT_ADDR (64 KiB, public output)
                               [+ 0..N]   SSZ-encoded
                                          SszStatelessValidationResult
  0xa0020000 .. 0xc0000000   working RAM (decoded structures, DBs,
                             frames) -- the Stateless guest claims this
                             tail of ziskemu's RAM region.
  ```

  `INPUT_ADDR`, `INPUT_DATA_OFFSET`, and `OUTPUT_ADDR` mirror the
  constants in `EvmAsm/Codegen/Programs.lean`; do not duplicate the
  numeric values here -- the working-RAM sub-region anchors below are
  the new contribution.

  Note: the verified-side `isValidMemAddr` range
  (`0x20..0x78000000`) does **not** cover ziskemu's RAM at
  `0xa0000000..0xc0000000`. This is the same gap that the existing
  `evm_add` build unit already lives with (it writes `.data` at
  `0xa0000000` and `OUTPUT_ADDR` at `0xa0010000`, both outside
  `isValidMemAddr`). Future proof PRs will have to relax the
  verified memory predicate or introduce a second memory region;
  out of scope for the Stateless guest scaffold.

  ## Working-RAM sub-regions (0xa0020000 .. 0xc0000000)

  Each anchor is the start of a region whose size is sized at codegen
  time. Sizes will be tightened as modules land; for now we reserve
  generous slabs so successive PRs do not have to reflow addresses.
  Total reserved through `SHA256_SCRATCH` end is ~28 MiB; ziskemu's
  RAM region carries ~512 MiB of headroom past `0xa0020000`.

  | Anchor                       | Address          | Size budget |
  |------------------------------|------------------|-------------|
  | `STATELESS_WORK_BASE`        | `0xa0020000`     | base ref    |
  | `SSZ_INPUT_DECODED`          | `0xa0020000`     | 64 KiB      |
  | `EXECUTION_WITNESS_AREA`     | `0xa0030000`     | 1 MiB       |
  | `NODE_DB_BUCKETS`            | `0xa0130000`     | 4 MiB       |
  | `CODE_DB_BUCKETS`            | `0xa0530000`     | 1 MiB       |
  | `STATE_TRACKER_AREA`         | `0xa0630000`     | 4 MiB       |
  | `EVM_FRAME_STACK`            | `0xa0a30000`     | 256 KiB     |
  | `EVM_VALUE_STACK`            | `0xa0a70000`     | 1 MiB       |
  | `EVM_MEMORY_AREA`            | `0xa0b70000`     | 16 MiB      |
  | `KECCAK_SCRATCH`             | `0xa1b70000`     | 64 KiB      |
  | `ECRECOVER_SCRATCH`          | `0xa1b80000`     | 64 KiB      |
  | `SHA256_SCRATCH`             | `0xa1b90000`     | 64 KiB      |

  (`EVM_MEMORY_AREA` budget is per-frame nominal; with max call depth
  1024 the precise per-frame slicing is tracked in `Stateless/VM/`.)

  ## Calling convention (non-leaf stateless code)

  The existing opcode handlers are leaf functions. The stateless guest
  is deeply nested, so non-leaf code in `EvmAsm/Stateless/` follows a
  standard RV64 ABI:

  - `x1 (ra)`           : return address
  - `x2 (sp)`           : RV64 call stack pointer (distinct from EVM
                          value-stack `x12`)
  - `x10..x17 (a0..a7)` : args / returns
  - `x12`               : EVM value-stack pointer (preserved across
                          opcode handler calls, saved/restored at
                          message-frame boundaries)
  - `x18..x27 (s2..s11)`: callee-saved
  - Each non-leaf entry sets up an explicit `sp` adjust; the per-module
    frame size is documented at the top of that module's `Program.lean`.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Working-RAM anchors (see table above). -/

def STATELESS_WORK_BASE     : Word := 0xa0020000
def SSZ_INPUT_DECODED       : Word := 0xa0020000
def EXECUTION_WITNESS_AREA  : Word := 0xa0030000
def NODE_DB_BUCKETS         : Word := 0xa0130000
def CODE_DB_BUCKETS         : Word := 0xa0530000
def STATE_TRACKER_AREA      : Word := 0xa0630000
def EVM_FRAME_STACK         : Word := 0xa0a30000
def EVM_VALUE_STACK         : Word := 0xa0a70000
def EVM_MEMORY_AREA         : Word := 0xa0b70000
def KECCAK_SCRATCH          : Word := 0xa1b70000
def ECRECOVER_SCRATCH       : Word := 0xa1b80000
def SHA256_SCRATCH          : Word := 0xa1b90000

end EvmAsm.Stateless
