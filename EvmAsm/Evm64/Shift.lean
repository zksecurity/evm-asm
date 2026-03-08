/-
  EvmAsm.Evm64.Shift

  256-bit EVM SHR (logical shift right) as a 64-bit RISC-V program.
  SHR(shift, value) pops shift and value, pushes value >> shift.
  If shift >= 256, the result is 0.

  The 256-bit value is stored as 4 little-endian 64-bit limbs.
  A shift by s bits decomposes into:
    limb_shift = s / 64  (skip whole limbs, 0-3)
    bit_shift  = s % 64  (shift within/across limbs, 0-63)

  For output limb i:
    result[i] = (value[i + limb_shift] >>> bit_shift) |
                ((value[i + limb_shift + 1] <<< (64 - bit_shift)) &&& mask)
  where mask = 0xFFFFFFFFFFFFFFFF if bit_shift > 0, else 0.

  Register allocation:
    x12 = EVM stack pointer
    x6  = bit_shift (0-63), preserved during limb processing
    x7  = anti_shift = 64 - bit_shift, preserved
    x11 = mask (0 or 0xFFFFFFFFFFFFFFFF), preserved
    x5  = temp: current limb during processing, limb_shift during dispatch
    x10 = temp: next limb during processing

  Program layout (90 instructions = 360 bytes):
    Phase A (9 instrs):  Check shift >= 256
    Phase B (7 instrs):  Extract bit_shift, limb_shift, mask, anti_shift
    Phase C (5 instrs):  Cascade dispatch on limb_shift (0-3)
    Phase D (64 instrs): 4 shift bodies (ls3 through ls0)
    Phase E (5 instrs):  Zero path (shift >= 256)
    Exit point: offset 360
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

-- ============================================================================
-- Sub-program definitions
-- ============================================================================

/-- Phase A: Check shift >= 256 (9 instructions).
    OR-reduce shift limbs 1-3. BNE to zero_path if nonzero.
    Then check limb 0 < 256. BEQ to zero_path if not. -/
def shr_phase_a : Program :=
  LD .x5  .x12 8  ;;                          -- x5  = shift[1]
  LD .x10 .x12 16 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[2]
  LD .x10 .x12 24 ;; single (.OR .x5 .x5 .x10) ;; -- x5 |= shift[3]
  single (.BNE .x5 .x0 320) ;;               -- high limbs nonzero → zero_path (340-20=320)
  LD .x5  .x12 0  ;;                          -- x5 = shift[0]
  single (.SLTIU .x10 .x5 256) ;;             -- x10 = (shift[0] < 256)
  single (.BEQ .x10 .x0 308)                  -- shift[0] >= 256 → zero_path (340-32=308)

/-- Phase B: Extract parameters (7 instructions). -/
def shr_phase_b : Program :=
  single (.ANDI .x6 .x5 63) ;;               -- x6 = bit_shift
  single (.SRLI .x5 .x5 6)  ;;               -- x5 = limb_shift
  single (.SLTU .x11 .x0 .x6) ;;            -- x11 = (bit_shift > 0)
  single (.SUB .x11 .x0 .x11) ;;            -- x11 = mask
  LI .x7 64 ;;                               -- x7 = 64
  single (.SUB .x7 .x7 .x6) ;;              -- x7 = anti_shift
  ADDI .x12 .x12 32                          -- pop shift word

/-- Phase C: Cascade dispatch (5 instructions). -/
def shr_phase_c : Program :=
  single (.BEQ .x5 .x0 176) ;;              -- ls0 (240-64=176)
  ADDI .x10 .x0 1 ;;
  single (.BEQ .x5 .x10 92) ;;              -- ls1 (164-72=92)
  ADDI .x10 .x0 2 ;;
  single (.BEQ .x5 .x10 32)                 -- ls2 (112-80=32)

/-- Helper: 7-instruction merge block for one middle limb (64-bit).
    LD x5, src_off(x12); SRL x5,x5,x6; LD x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SD x12,x5,dst_off -/
def shr_merge_limb (src_off next_off dst_off : BitVec 12) : Program :=
  LD .x5 .x12 src_off ;;
  single (.SRL .x5 .x5 .x6) ;;
  LD .x10 .x12 next_off ;;
  single (.SLL .x10 .x10 .x7) ;;
  single (.AND .x10 .x10 .x11) ;;
  single (.OR .x5 .x5 .x10) ;;
  SD .x12 .x5 dst_off

/-- Helper: 3-instruction last-limb block (64-bit).
    LD x5, 24(x12); SRL x5,x5,x6; SD x12,x5,dst_off -/
def shr_last_limb (dst_off : BitVec 12) : Program :=
  LD .x5 .x12 24 ;;
  single (.SRL .x5 .x5 .x6) ;;
  SD .x12 .x5 dst_off

/-- ls3: limb_shift=3 (7 instructions) -/
def shr_body_3 : Program :=
  shr_last_limb 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  single (.JAL .x0 252)                      -- exit (360-108=252)

/-- ls2: limb_shift=2 (13 instructions) -/
def shr_body_2 : Program :=
  shr_merge_limb 16 24 0 ;;                  -- i=0: value[2],value[3]→result[0]
  shr_last_limb 8 ;;                         -- i=1: value[3]→result[1]
  SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  single (.JAL .x0 200)                      -- exit (360-160=200)

/-- ls1: limb_shift=1 (19 instructions) -/
def shr_body_1 : Program :=
  shr_merge_limb 8 16 0 ;;                   -- i=0: value[1],value[2]→result[0]
  shr_merge_limb 16 24 8 ;;                  -- i=1: value[2],value[3]→result[1]
  shr_last_limb 16 ;;                        -- i=2: value[3]→result[2]
  SD .x12 .x0 24 ;;
  single (.JAL .x0 124)                      -- exit (360-236=124)

/-- ls0: limb_shift=0 (25 instructions) -/
def shr_body_0 : Program :=
  shr_merge_limb 0 8 0 ;;                    -- i=0: value[0],value[1]→result[0]
  shr_merge_limb 8 16 8 ;;                   -- i=1: value[1],value[2]→result[1]
  shr_merge_limb 16 24 16 ;;                 -- i=2: value[2],value[3]→result[2]
  shr_last_limb 24 ;;                        -- i=3: value[3]→result[3]
  single (.JAL .x0 24)                       -- exit (360-336=24)

/-- Phase E: Zero path (5 instructions). -/
def shr_zero_path : Program :=
  ADDI .x12 .x12 32 ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- Full program
-- ============================================================================

/-- 256-bit EVM SHR: binary (pop 2, push 1, sp += 32).
    SHR(shift, value) = value >> shift. 90 instructions total. -/
def evm_shr : Program :=
  shr_phase_a ;;
  shr_phase_b ;;
  shr_phase_c ;;
  shr_body_3 ;; shr_body_2 ;; shr_body_1 ;; shr_body_0 ;;
  shr_zero_path
  -- Exit: offset 360 (instruction 90)

-- ============================================================================
-- Instruction count verification
-- ============================================================================

/-- evm_shr has exactly 90 instructions. -/
example : evm_shr.length = 90 := by native_decide

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- Create a test state for SHR with 4 shift limbs and 4 value limbs.
    Memory layout: sp → [s0..s3, v0..v3] (8 doublewords). -/
def mkShrTestState (sp : Word)
    (s0 s1 s2 s3 : Word)   -- shift limbs (LE)
    (v0 v1 v2 v3 : Word)   -- value limbs (LE)
    : MachineState where
  regs := fun r =>
    match r with
    | .x12 => sp
    | _    => 0
  mem := fun a =>
    if a == sp      then s0
    else if a == sp + 8  then s1
    else if a == sp + 16 then s2
    else if a == sp + 24 then s3
    else if a == sp + 32 then v0
    else if a == sp + 40 then v1
    else if a == sp + 48 then v2
    else if a == sp + 56 then v3
    else 0
  code := loadProgram 0 evm_shr
  pc := 0

/-- Run evm_shr and check the final PC and x12 register. -/
def runShrCheck (sp : Word)
    (s0 s1 s2 s3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (Word × Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' => some (s'.pc, s'.getReg .x12)
  | none => none

/-- Run evm_shr and extract 4 result limbs. -/
def runShrResult (sp : Word)
    (s0 s1 s2 s3 : Word)
    (v0 v1 v2 v3 : Word)
    (steps : Nat) : Option (List Word) :=
  let s := mkShrTestState sp s0 s1 s2 s3 v0 v1 v2 v3
  match stepN steps s with
  | some s' =>
    let rsp := s'.getReg .x12
    some [s'.getMem rsp, s'.getMem (rsp + 8), s'.getMem (rsp + 16), s'.getMem (rsp + 24)]
  | none => none

-- ============================================================================
-- Concrete tests via native_decide
-- ============================================================================

-- Step counts by path:
-- ls0 (shift 0-63):  9+7+1+25 = 42 steps
-- ls1 (shift 64-127): 9+7+3+19 = 38
-- ls2 (shift 128-191): 9+7+5+13 = 34
-- ls3 (shift 192-255): 9+7+5+7 = 28
-- zero_path (high limbs nonzero): 6+5 = 11
-- zero_path (limb0 >= 256): 9+5 = 14

-- Test 1: SHR(0, value) = value (no shift, ls0 path, 42 steps)
/-- SHR by 0: result equals input value. -/
example : runShrResult 1024 0 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some [0xDEADBEEFCAFE0000, 0, 0, 1] := by native_decide

-- Test 2: SHR(1, value) (ls0 path, 42 steps)
-- result[0] = (0xDEADBEEFCAFE0000 >>> 1) | (0 <<< 63) = 0x6F56DF77E57F0000
-- result[2] = (0 >>> 1) | ((1 <<< 63) & mask) = 0x8000000000000000
-- result[3] = 1 >>> 1 = 0
/-- SHR by 1 bit. -/
example : runShrResult 1024 1 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some [0x6F56DF77E57F0000, 0, 0x8000000000000000, 0] := by native_decide

-- Test 3: SHR(64, value) (ls1 path, 38 steps)
-- limb_shift=1, bit_shift=0
-- result[i] = value[i+1] for i=0..2, result[3]=0
/-- SHR by 64 bits (one full limb). -/
example : runShrResult 1024 64 0 0 0  0xDEADBEEFCAFE0000 0 0 1  38 =
    some [0, 0, 1, 0] := by native_decide

-- Test 4: SHR(255, value) (ls3 path, 28 steps)
-- limb_shift=3, bit_shift=63
-- result[0] = value[3] >>> 63 = 1 >>> 63 = 0
/-- SHR by 255 bits. -/
example : runShrResult 1024 255 0 0 0  0xDEADBEEFCAFE0000 0 0 1  28 =
    some [0, 0, 0, 0] := by native_decide

-- Test 5: SHR(256, value) = 0 (zero path via limb0, 14 steps)
/-- SHR by 256: result is all zeros. -/
example : runShrResult 1024 256 0 0 0  0xDEADBEEFCAFE0000 0 0 1  14 =
    some [0, 0, 0, 0] := by native_decide

-- Test 6: SHR with nonzero high shift limb (zero path via BNE, 11 steps)
/-- SHR with shift having nonzero high limbs: result is all zeros. -/
example : runShrResult 1024 0 1 0 0  0xDEADBEEFCAFE0000 0 0 1  11 =
    some [0, 0, 0, 0] := by native_decide

-- Test 7: SHR(4, 0xFF) = 0x0F (ls0 path)
/-- SHR(4, 0xFF) = 0x0F. -/
example : runShrResult 1024 4 0 0 0  0xFF 0 0 0  42 =
    some [0x0F, 0, 0, 0] := by native_decide

-- Test 8: SHR(65, all-F value) (ls1 path, 38 steps)
-- limb_shift=1, bit_shift=1
-- result[0] = (allF >>> 1) | ((allF <<< 63) & mask) = allF
-- result[1] = (allF >>> 1) | ((allF <<< 63) & mask) = allF
-- result[2] = allF >>> 1 = 0x7FFFFFFFFFFFFFFF
-- result[3] = 0
/-- SHR(65, all-F value): shift by 1 limb + 1 bit. -/
example : runShrResult 1024 65 0 0 0
    0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF  38 =
    some [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0] := by native_decide

-- Test 9: SHR(192, ...) with v3 = 0xABCD1234 (ls3 path, 28 steps)
-- limb_shift=3, bit_shift=0
-- result[0] = value[3] >>> 0 = 0xABCD1234
/-- SHR by 192 bits (3 full limbs). -/
example : runShrResult 1024 192 0 0 0  1 2 3 0xABCD1234  28 =
    some [0xABCD1234, 0, 0, 0] := by native_decide

-- Test 10: Verify PC and sp are correct after execution
/-- After SHR(0, ...), PC = 360 and x12 = sp + 32. -/
example : runShrCheck 1024 0 0 0 0  0xDEADBEEFCAFE0000 0 0 1  42 =
    some (360, 1056) := by native_decide

/-- After SHR(256, ...), PC = 360 and x12 = sp + 32. -/
example : runShrCheck 1024 256 0 0 0  0xDEADBEEFCAFE0000 0 0 1  14 =
    some (360, 1056) := by native_decide

end EvmAsm.Rv64
