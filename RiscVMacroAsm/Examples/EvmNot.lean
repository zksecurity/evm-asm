/-
  RiscVMacroAsm.Examples.EvmNot

  EVM NOT opcode implemented and verified as a RISC-V program.

  Source: ethereum/execution-specs Amsterdam fork
    src/ethereum/forks/amsterdam/vm/instructions/bitwise.py
    ```python
    def bitwise_not(evm: Evm) -> None:
        x = pop(evm.stack)
        push(evm.stack, ~x)
        evm.pc += Uint(1)
    ```

  Scope: 32-bit word size (one RISC-V word per stack slot).

  Register conventions:
  - x12: stack pointer (preserved)
  - x7: temporary register (clobbered)
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SyscallSpecs
import RiscVMacroAsm.Examples.EvmIsZero

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Section 1: Reference Semantics
-- ============================================================================

/-- NOT result: bitwise complement (matches Python `~x`). -/
def evm_not_result (x : Word) : Word := ~~~x

-- ============================================================================
-- Section 2: RISC-V Program
-- ============================================================================

/-- NOT as a 3-instruction RISC-V program.
    LW   x7, 0(x12)      -- load top of stack into temp
    XORI x7, x7, 0xFFF   -- x7 := x7 ^^^ sext(0xFFF) = x7 ^^^ 0xFFFFFFFF = ~~~x7
    SW   x12, x7, 0      -- store result back to top of stack -/
def evm_not : Program :=
  LW .x7 .x12 0 ;;
  single (.XORI .x7 .x7 0xFFF) ;;
  SW .x12 .x7 0

-- ============================================================================
-- Section 3: Concrete Execution Tests
-- ============================================================================

private def test_state_ff : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32
    | _ => 0
  mem := fun a => if a == 0x1000#32 then 0xFF else 0
  pc := 0

/-- Concrete test: NOT(0xFF) = 0xFFFFFF00 -/
example : (stepN 3 (loadProgram 0 evm_not) test_state_ff).bind
    (fun s => some (s.getMem 0x1000#32)) = some 0xFFFFFF00#32 := by native_decide

private def test_state_zero : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32
    | _ => 0
  mem := fun _ => 0
  pc := 0

/-- Concrete test: NOT(0x00000000) = 0xFFFFFFFF -/
example : (stepN 3 (loadProgram 0 evm_not) test_state_zero).bind
    (fun s => some (s.getMem 0x1000#32)) = some 0xFFFFFFFF#32 := by native_decide

-- ============================================================================
-- Section 4: Semantic Equivalence
-- ============================================================================

/-- XORI x, x, 0xFFF computes bitwise NOT:
    v ^^^ sext(0xFFF : BitVec 12) = ~~~v

    Because sext(0xFFF : BitVec 12) = 0xFFFFFFFF : Word (all ones),
    and XOR with all ones is complement. -/
theorem xori_neg1_eq_not (v : Word) :
    (v ^^^ signExtend12 (0xFFF : BitVec 12)) = ~~~v := by
  unfold signExtend12; bv_decide

-- ============================================================================
-- Section 5: Low-Level CPS Specification
-- ============================================================================

/-- Low-level CPS spec for evm_not: given fetch hypotheses for 3 instructions,
    transforms (x12 ↦ sp, x7 ↦ v_tmp, sp ↦ v) into
    (x12 ↦ sp, x7 ↦ ~~~v, sp ↦ ~~~v). -/
theorem evm_not_spec (code : CodeMem) (v sp v_tmp : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.XORI .x7 .x7 0xFFF))
    (hfetch2 : code (base + 8) = some (Instr.SW .x12 .x7 0))
    (hvalid : isValidMemAccess sp = true) :
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v_tmp) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_not_result v) ** (sp ↦ₘ evm_not_result v)) := by
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
  -- Phase 2: XORI x7, x7, 0xFFF — base+4 → base+8
  have s2core : cpsTriple code (base + 4) (base + 8)
      (.x7 ↦ᵣ v)
      (.x7 ↦ᵣ (v ^^^ signExtend12 (0xFFF : BitVec 12))) := by
    have := xori_spec_gen_same code .x7 v 0xFFF (base + 4) (by decide) hfetch1
    simp only [h48] at this; exact this
  -- Rewrite the XORI result to evm_not_result
  have s2core' : cpsTriple code (base + 4) (base + 8)
      (.x7 ↦ᵣ v) (.x7 ↦ᵣ evm_not_result v) :=
    cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ h => h)
      (fun h hp => by rw [regIs] at hp ⊢; rw [xori_neg1_eq_not] at hp; exact hp)
      s2core
  -- Frame x12 and memory around XORI
  have s2 : cpsTriple code (base + 4) (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_not_result v) ** (sp ↦ₘ v)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ (.x12 ↦ᵣ sp) (pcFree_regIs .x12 sp)
      (cpsTriple_frame_left code (base + 4) (base + 8) _ _ (sp ↦ₘ v) (pcFree_memIs sp v) s2core')
  -- Phase 3: SW x12, x7, 0 — base+8 → base+12
  have s3 : cpsTriple code (base + 8) (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_not_result v) ** (sp ↦ₘ v))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_not_result v) ** (sp ↦ₘ evm_not_result v)) := by
    have hsw := sw_spec_gen code .x12 .x7 sp (evm_not_result v) v (0 : BitVec 12)
      (base + 8) hfetch2 (by rw [hsp_eq]; exact hvalid)
    rw [hsp_eq] at hsw; simp only [h812] at hsw; exact hsw
  -- Compose all three phases
  exact cpsTriple_seq code base (base + 8) (base + 12) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1 s2) s3

-- ============================================================================
-- Section 6: Stack-Level CPS Specification
-- ============================================================================

/-- Stack-level spec: NOT replaces the top element of the EVM stack
    with its bitwise complement. x7 is clobbered, x12 (sp) is preserved. -/
theorem evm_not_stack_spec (code : CodeMem) (v sp : Word) (rest : List Word)
    (v_tmp : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.XORI .x7 .x7 0xFFF))
    (hfetch2 : code (base + 8) = some (Instr.SW .x12 .x7 0))
    (hvalid : isValidMemAccess sp = true) :
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v_tmp) ** evmStackIs sp (v :: rest))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ evm_not_result v) **
       evmStackIs sp (evm_not_result v :: rest)) := by
  simp only [evmStackIs, memBufferIs]
  have hlow := evm_not_spec code v sp v_tmp base hfetch0 hfetch1 hfetch2 hvalid
  let A := (.x12 ↦ᵣ sp)
  let B := (.x7 ↦ᵣ v_tmp)
  let B' := (.x7 ↦ᵣ evm_not_result v)
  let C := (sp ↦ₘ v)
  let C' := (sp ↦ₘ evm_not_result v)
  let D := memBufferIs (sp + 4) rest
  exact cpsTriple_consequence code base (base + 12) _ _ _ _
    (fun h hp =>
      (sepConj_assoc A (B ** C) D h).mpr
        (sepConj_mono_right (fun h' hp' => (sepConj_assoc B C D h').mpr hp') h hp))
    (fun h hp =>
      sepConj_mono_right (fun h' hp' => (sepConj_assoc B' C' D h').mp hp') h
        ((sepConj_assoc A (B' ** C') D h).mp hp))
    (cpsTriple_frame_left code base (base + 12) _ _ D (pcFree_memBufferIs (sp + 4) rest) hlow)

end RiscVMacroAsm.Examples
