/-
  RiscVMacroAsm.Examples.EvmIsZero

  EVM ISZERO opcode implemented and verified as a RISC-V program.

  Source: ethereum/execution-specs Amsterdam fork
    src/ethereum/forks/amsterdam/vm/instructions/comparison.py:154-177
    ```python
    def is_zero(evm: Evm) -> None:
        x = pop(evm.stack)
        result = U256(x == 0)
        push(evm.stack, result)
        evm.pc += Uint(1)
    ```

  Scope: 32-bit word size (one RISC-V word per stack slot).

  Register conventions:
  - x12: stack pointer (preserved)
  - x7: temporary register (clobbered)
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SyscallSpecs

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Section 1: EVM Stack Abstraction
-- ============================================================================

/-- EVM stack: consecutive words at sp, sp+4, sp+8, ...
    The first element is the top of stack. -/
def evmStackIs (sp : Addr) (values : List Word) : Assertion :=
  memBufferIs sp values

theorem pcFree_evmStackIs (sp : Addr) (values : List Word) :
    (evmStackIs sp values).pcFree :=
  pcFree_memBufferIs sp values

-- ============================================================================
-- Section 2: Reference Semantics
-- ============================================================================

/-- ISZERO result: 1 if x == 0, else 0 (matches Python `U256(x == 0)`). -/
def evm_iszero_result (x : Word) : Word :=
  if x == 0 then 1 else 0

-- ============================================================================
-- Section 3: RISC-V Program
-- ============================================================================

/-- ISZERO as a 3-instruction RISC-V program.
    LW  x7, 0(x12)      -- load top of stack into temp
    SLTIU x7, x7, 1     -- x7 := (x7 <u 1) ? 1 : 0  (i.e., x7 == 0 ? 1 : 0)
    SW  x12, x7, 0       -- store result back to top of stack -/
def evm_iszero : Program :=
  LW .x7 .x12 0 ;;
  single (.SLTIU .x7 .x7 1) ;;
  SW .x12 .x7 0

-- ============================================================================
-- Section 4: Concrete Execution Tests
-- ============================================================================

private def test_state : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32  -- stack pointer in valid memory (SP1 range)
    | _ => 0
  mem := fun _ => 0  -- top of stack = 0
  pc := 0

/-- Concrete test: ISZERO(0) = 1 -/
example : (stepN 3 (loadProgram 0 evm_iszero) test_state).bind
    (fun s => some (s.getMem 0x1000#32)) = some 1 := by native_decide

private def test_state_nonzero : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32
    | _ => 0
  mem := fun a => if a == 0x1000#32 then 42 else 0
  pc := 0

/-- Concrete test: ISZERO(42) = 0 -/
example : (stepN 3 (loadProgram 0 evm_iszero) test_state_nonzero).bind
    (fun s => some (s.getMem 0x1000#32)) = some 0 := by native_decide

-- ============================================================================
-- Section 5: Semantic Equivalence
-- ============================================================================

/-- SLTIU x, x, 1 computes the same result as evm_iszero_result:
    (v <u sext(1)) ? 1 : 0  =  (v == 0) ? 1 : 0

    Because sext(1 : BitVec 12) = 1 : Word, and v <u 1 ↔ v = 0. -/
theorem sltiu_1_eq_iszero (v : Word) :
    (if BitVec.ult v (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0) =
    evm_iszero_result v := by
  unfold evm_iszero_result signExtend12; bv_decide

-- ============================================================================
-- Section 6: Low-Level CPS Specification
-- ============================================================================

/-- Low-level CPS spec for evm_iszero: given fetch hypotheses for 3 instructions,
    transforms (x12 ↦ sp, x7 ↦ v_tmp, sp ↦ v) into
    (x12 ↦ sp, x7 ↦ iszero(v), sp ↦ iszero(v)). -/
theorem evm_iszero_spec (code : CodeMem) (v sp v_tmp : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.SLTIU .x7 .x7 1))
    (hfetch2 : code (base + 8) = some (Instr.SW .x12 .x7 0))
    (hvalid : isValidMemAccess sp = true) :
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v_tmp) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_iszero_result v) ** (sp ↦ₘ evm_iszero_result v)) := by
  -- Address arithmetic
  have h48 : base + 4 + 4 = base + 8 := by grind
  have h812 : base + 8 + 4 = base + 12 := by grind
  -- signExtend12 0 = 0, so sp + signExtend12 0 = sp
  have hsext0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hsp_eq : sp + signExtend12 (0 : BitVec 12) = sp := by
    rw [hsext0]; simp
  -- Phase 1: LW x7, 0(x12) — base → base+4
  have s1 : cpsTriple code base (base + 4)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v_tmp) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v) ** (sp ↦ₘ v)) := by
    have hlw := lw_spec_gen code .x7 .x12 sp v_tmp v (0 : BitVec 12) base
      (by decide) hfetch0 (by rw [hsp_eq]; exact hvalid)
    rw [hsp_eq] at hlw; exact hlw
  -- Phase 2: SLTIU x7, x7, 1 — base+4 → base+8
  have s2core : cpsTriple code (base + 4) (base + 8)
      (.x7 ↦ᵣ v)
      (.x7 ↦ᵣ (if BitVec.ult v (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0)) := by
    have := sltiu_spec_gen_same code .x7 v 1 (base + 4) (by decide) hfetch1
    simp only [h48] at this; exact this
  -- Rewrite the SLTIU result to evm_iszero_result
  have s2core' : cpsTriple code (base + 4) (base + 8)
      (.x7 ↦ᵣ v) (.x7 ↦ᵣ evm_iszero_result v) :=
    cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ h => h)
      (fun h hp => by rw [regIs] at hp ⊢; rw [sltiu_1_eq_iszero] at hp; exact hp)
      s2core
  -- Frame x12 and memory around SLTIU
  have s2 : cpsTriple code (base + 4) (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_iszero_result v) ** (sp ↦ₘ v)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ (.x12 ↦ᵣ sp) (pcFree_regIs .x12 sp)
      (cpsTriple_frame_left code (base + 4) (base + 8) _ _ (sp ↦ₘ v) (pcFree_memIs sp v) s2core')
  -- Phase 3: SW x12, x7, 0 — base+8 → base+12
  have s3 : cpsTriple code (base + 8) (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_iszero_result v) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_iszero_result v) ** (sp ↦ₘ evm_iszero_result v)) := by
    have hsw := sw_spec_gen code .x12 .x7 sp (evm_iszero_result v) v (0 : BitVec 12)
      (base + 8) hfetch2 (by rw [hsp_eq]; exact hvalid)
    rw [hsp_eq] at hsw; simp only [h812] at hsw; exact hsw
  -- Compose all three phases
  exact cpsTriple_seq code base (base + 8) (base + 12) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1 s2) s3

-- ============================================================================
-- Section 7: Stack-Level CPS Specification
-- ============================================================================

/-- Stack-level spec: ISZERO replaces the top element of the EVM stack
    with its boolean negation. x7 is clobbered, x12 (sp) is preserved. -/
theorem evm_iszero_stack_spec (code : CodeMem) (v sp : Word) (rest : List Word)
    (v_tmp : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.SLTIU .x7 .x7 1))
    (hfetch2 : code (base + 8) = some (Instr.SW .x12 .x7 0))
    (hvalid : isValidMemAccess sp = true) :
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v_tmp) ** evmStackIs sp (v :: rest))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_iszero_result v) **
       evmStackIs sp (evm_iszero_result v :: rest)) := by
  -- Unfold evmStackIs/memBufferIs to expose (sp ↦ₘ v) ** memBufferIs (sp+4) rest
  simp only [evmStackIs, memBufferIs]
  -- Goal after simp:
  --   cpsTriple code base (base+12)
  --     (x12 ** x7_tmp ** ((sp ↦ₘ v) ** memBufferIs (sp+4) rest))
  --     (x12 ** x7_iz ** ((sp ↦ₘ iz(v)) ** memBufferIs (sp+4) rest))
  --
  -- The low-level spec has:
  --   cpsTriple code base (base+12) (x12 ** x7_tmp ** (sp ↦ₘ v)) (x12 ** x7_iz ** (sp ↦ₘ iz(v)))
  -- Frame it with memBufferIs (sp+4) rest to get:
  --   cpsTriple ... ((x12 ** x7 ** (sp ↦ₘ v)) ** memBuf) ((x12 ** x7' ** (sp ↦ₘ iz)) ** memBuf)
  -- Then use cpsTriple_consequence to reassociate.
  have hlow := evm_iszero_spec code v sp v_tmp base hfetch0 hfetch1 hfetch2 hvalid
  let A := (.x12 ↦ᵣ sp)
  let B := (.x7 ↦ᵣ v_tmp)
  let B' := (.x7 ↦ᵣ evm_iszero_result v)
  let C := (sp ↦ₘ v)
  let C' := (sp ↦ₘ evm_iszero_result v)
  let D := memBufferIs (sp + 4) rest
  -- Reassociate: A ** (B ** (C ** D)) ↔ (A ** (B ** C)) ** D
  -- Pre:  (A ** (B ** (C ** D))) → ((A ** (B ** C)) ** D)
  -- Post: ((A ** (B' ** C')) ** D) → (A ** (B' ** (C' ** D)))
  exact cpsTriple_consequence code base (base + 12) _ _ _ _
    (fun h hp =>
      (sepConj_assoc A (B ** C) D h).mpr
        (sepConj_mono_right (fun h' hp' => (sepConj_assoc B C D h').mpr hp') h hp))
    (fun h hp =>
      sepConj_mono_right (fun h' hp' => (sepConj_assoc B' C' D h').mp hp') h
        ((sepConj_assoc A (B' ** C') D h).mp hp))
    (cpsTriple_frame_left code base (base + 12) _ _ D (pcFree_memBufferIs (sp + 4) rest) hlow)

end RiscVMacroAsm.Examples
