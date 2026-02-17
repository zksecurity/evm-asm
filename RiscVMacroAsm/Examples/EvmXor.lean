/-
  RiscVMacroAsm.Examples.EvmXor

  EVM XOR opcode implemented and verified as a RISC-V program.

  Source: ethereum/execution-specs Amsterdam fork
    src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:71-93
    ```python
    def bitwise_xor(evm: Evm) -> None:
        x = pop(evm.stack)
        y = pop(evm.stack)
        push(evm.stack, x ^ y)
        evm.pc += Uint(1)
    ```

  Scope: 32-bit word size (one RISC-V word per stack slot).
  Pops 2 values, pushes 1, so the stack shrinks by 1 slot (sp increases by 4).

  Register conventions:
  - x12: stack pointer (modified: sp → sp+4)
  - x7: temporary register (clobbered)
  - x6: temporary register (clobbered)
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SyscallSpecs
import RiscVMacroAsm.Examples.EvmIsZero

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Section 1: Reference Semantics
-- ============================================================================

/-- XOR result: bitwise XOR (matches Python `x ^ y`). -/
def evm_xor_result (x y : Word) : Word := x ^^^ y

-- ============================================================================
-- Section 2: RISC-V Program
-- ============================================================================

/-- XOR as a 5-instruction RISC-V program.
    LW   x7,  0(x12)     -- load first operand (top of stack)
    LW   x6,  4(x12)     -- load second operand
    XOR  x7, x7, x6      -- compute x7 := a ^^^ b
    ADDI x12, x12, 4     -- pop one slot (sp += 4)
    SW   x12, x7, 0      -- store result at new top of stack -/
def evm_xor : Program :=
  LW .x7 .x12 0 ;;
  LW .x6 .x12 4 ;;
  single (.XOR .x7 .x7 .x6) ;;
  single (.ADDI .x12 .x12 4) ;;
  SW .x12 .x7 0

-- ============================================================================
-- Section 3: Concrete Execution Tests
-- ============================================================================

private def test_state_xor : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32  -- stack pointer
    | _ => 0
  mem := fun a =>
    if a == 0x1000#32 then 0xFF#32       -- top of stack = 0xFF
    else if a == 0x1004#32 then 0x0F#32  -- second element = 0x0F
    else 0
  pc := 0

/-- Concrete test: XOR(0xFF, 0x0F) = 0xF0 -/
example : (stepN 5 (loadProgram 0 evm_xor) test_state_xor).bind
    (fun s => some (s.getMem 0x1004#32)) = some 0xF0#32 := by native_decide

/-- Concrete test: sp moves from 0x1000 to 0x1004 after XOR -/
example : (stepN 5 (loadProgram 0 evm_xor) test_state_xor).bind
    (fun s => some (s.getReg .x12)) = some 0x1004#32 := by native_decide

private def test_state_xor_self : MachineState where
  regs := fun r => match r with
    | .x12 => 0x1000#32
    | _ => 0
  mem := fun a =>
    if a == 0x1000#32 then 0xABCD1234#32
    else if a == 0x1004#32 then 0xABCD1234#32  -- same value
    else 0
  pc := 0

/-- Concrete test: XOR(x, x) = 0 (self-XOR) -/
example : (stepN 5 (loadProgram 0 evm_xor) test_state_xor_self).bind
    (fun s => some (s.getMem 0x1004#32)) = some 0x00000000#32 := by native_decide

-- ============================================================================
-- Section 4: Low-Level CPS Specification
-- ============================================================================

/-- Low-level CPS spec for evm_xor: given fetch hypotheses for 5 instructions,
    transforms
      (x12 ↦ sp, x7 ↦ v7, x6 ↦ v6, sp ↦ₘ a, (sp+4) ↦ₘ b)
    into
      (x12 ↦ sp+4, x7 ↦ a^^^b, x6 ↦ b, sp ↦ₘ a, (sp+4) ↦ₘ a^^^b). -/
theorem evm_xor_spec (code : CodeMem) (a b sp v7 v6 : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.LW .x6 .x12 4))
    (hfetch2 : code (base + 8) = some (Instr.XOR .x7 .x7 .x6))
    (hfetch3 : code (base + 12) = some (Instr.ADDI .x12 .x12 4))
    (hfetch4 : code (base + 16) = some (Instr.SW .x12 .x7 0))
    (hvalid_sp : isValidMemAccess sp = true)
    (hvalid_sp4 : isValidMemAccess (sp + 4) = true) :
    cpsTriple code base (base + 20)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ (a ^^^ b))) := by
  -- Address arithmetic
  have h48 : base + 4 + 4 = base + 8 := by grind
  have h812 : base + 8 + 4 = base + 12 := by grind
  have h1216 : base + 12 + 4 = base + 16 := by grind
  have h1620 : base + 16 + 4 = base + 20 := by grind
  -- signExtend12 facts
  have hsext0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hsext4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by decide
  have hsp0 : sp + signExtend12 (0 : BitVec 12) = sp := by rw [hsext0]; simp
  have hsp4_eq : sp + signExtend12 (4 : BitVec 12) = sp + 4 := by rw [hsext4]
  have hsp4_0 : (sp + 4) + signExtend12 (0 : BitVec 12) = sp + 4 := by rw [hsext0]; simp
  -- Phase 1: LW x7, 0(x12) — base → base+4
  have s1core : cpsTriple code base (base + 4)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (sp ↦ₘ a))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (sp ↦ₘ a)) := by
    have hlw := lw_spec_gen code .x7 .x12 sp v7 a (0 : BitVec 12) base
      (by decide) hfetch0 (by rw [hsp0]; exact hvalid_sp)
    rw [hsp0] at hlw; exact hlw
  have s1 : cpsTriple code base (base + 4)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ v6) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b)) := by
    have s1f := cpsTriple_frame_left code base (base + 4) _ _
      ((.x6 ↦ᵣ v6) ** ((sp + 4) ↦ₘ b))
      (pcFree_sepConj (pcFree_regIs .x6 v6) (pcFree_memIs (sp + 4) b)) s1core
    exact cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun h hp => by
        simp only [sepConj_assoc', sepConj_left_comm' (.x6 ↦ᵣ v6) (sp ↦ₘ a)] at hp ⊢
        exact hp)
      (fun h hp => by
        simp only [sepConj_assoc', sepConj_left_comm' (.x6 ↦ᵣ v6) (sp ↦ₘ a)] at hp ⊢
        exact hp)
      s1f
  -- Phase 2: LW x6, 4(x12) — base+4 → base+8
  have s2core : cpsTriple code (base + 4) (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b) ** ((sp + 4) ↦ₘ b)) := by
    have hlw := lw_spec_gen code .x6 .x12 sp v6 b (4 : BitVec 12) (base + 4)
      (by decide) hfetch1 (by rw [hsp4_eq]; exact hvalid_sp4)
    rw [hsp4_eq] at hlw; simp only [h48] at hlw; exact hlw
  have s2 : cpsTriple code (base + 4) (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ v6) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b)) := by
    have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
      ((.x7 ↦ᵣ a) ** (sp ↦ₘ a))
      (pcFree_sepConj (pcFree_regIs .x7 a) (pcFree_memIs sp a)) s2core
    exact cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun h hp => by
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hp => by
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      s2f
  -- Phase 3: XOR x7, x7, x6 — base+8 → base+12
  have s3core : cpsTriple code (base + 8) (base + 12)
      ((.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b))
      ((.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b)) := by
    have := xor_spec_gen_rd_eq_rs1 code .x7 .x6 a b (base + 8) (by decide) (by decide) hfetch2
    simp only [h812] at this; exact this
  have s3 : cpsTriple code (base + 8) (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b)) := by
    have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
      ((.x12 ↦ᵣ sp) ** ((sp ↦ₘ a) ** ((sp + 4) ↦ₘ b)))
      (pcFree_sepConj (pcFree_regIs .x12 sp)
        (pcFree_sepConj (pcFree_memIs sp a) (pcFree_memIs (sp + 4) b))) s3core
    exact cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun h hp => by
        simp only [sepConj_assoc',
                    sepConj_left_comm' (.x12 ↦ᵣ sp) (.x7 ↦ᵣ a),
                    sepConj_left_comm' (.x12 ↦ᵣ sp) (.x6 ↦ᵣ b)] at hp ⊢
        exact hp)
      (fun h hp => by
        simp only [sepConj_assoc',
                    sepConj_left_comm' (.x12 ↦ᵣ sp) (.x7 ↦ᵣ (a ^^^ b)),
                    sepConj_left_comm' (.x12 ↦ᵣ sp) (.x6 ↦ᵣ b)] at hp ⊢
        exact hp)
      s3f
  -- Phase 4: ADDI x12, x12, 4 — base+12 → base+16
  have s4core : cpsTriple code (base + 12) (base + 16)
      (.x12 ↦ᵣ sp) (.x12 ↦ᵣ (sp + 4)) := by
    have haddi := addi_spec_gen_same code .x12 sp 4 (base + 12) (by decide) hfetch3
    simp only [h1216, hsext4] at haddi; exact haddi
  have s4 : cpsTriple code (base + 12) (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b)) :=
    cpsTriple_frame_left code (base + 12) (base + 16) _ _ _
      (pcFree_sepConj (pcFree_regIs .x7 (a ^^^ b))
        (pcFree_sepConj (pcFree_regIs .x6 b)
          (pcFree_sepConj (pcFree_memIs sp a) (pcFree_memIs (sp + 4) b)))) s4core
  -- Phase 5: SW x12, x7, 0 — base+16 → base+20
  have s5core : cpsTriple code (base + 16) (base + 20)
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** ((sp + 4) ↦ₘ (a ^^^ b))) := by
    have hsw := sw_spec_gen code .x12 .x7 (sp + 4) (a ^^^ b) b (0 : BitVec 12)
      (base + 16) hfetch4 (by rw [hsp4_0]; exact hvalid_sp4)
    rw [hsp4_0] at hsw; simp only [h1620] at hsw; exact hsw
  have s5 : cpsTriple code (base + 16) (base + 20)
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ b))
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) ** (sp ↦ₘ a) ** ((sp + 4) ↦ₘ (a ^^^ b))) := by
    have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
      ((.x6 ↦ᵣ b) ** (sp ↦ₘ a))
      (pcFree_sepConj (pcFree_regIs .x6 b) (pcFree_memIs sp a)) s5core
    exact cpsTriple_consequence code (base + 16) (base + 20) _ _ _ _
      (fun h hp => by
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hp => by
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      s5f
  -- Compose all five phases
  exact cpsTriple_seq code base (base + 16) (base + 20) _ _ _
    (cpsTriple_seq code base (base + 12) (base + 16) _ _ _
      (cpsTriple_seq code base (base + 8) (base + 12) _ _ _
        (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1 s2) s3) s4) s5

-- ============================================================================
-- Section 5: Stack-Level CPS Specification
-- ============================================================================

/-- Stack-level spec: XOR pops two elements, pushes their bitwise XOR.
    x7 and x6 are clobbered, x12 (sp) moves from sp to sp+4.
    The popped slot (sp ↦ₘ a) is returned as leftover memory. -/
theorem evm_xor_stack_spec (code : CodeMem) (a b sp : Word) (rest : List Word)
    (v7 v6 : Word) (base : Addr)
    (hfetch0 : code base = some (Instr.LW .x7 .x12 0))
    (hfetch1 : code (base + 4) = some (Instr.LW .x6 .x12 4))
    (hfetch2 : code (base + 8) = some (Instr.XOR .x7 .x7 .x6))
    (hfetch3 : code (base + 12) = some (Instr.ADDI .x12 .x12 4))
    (hfetch4 : code (base + 16) = some (Instr.SW .x12 .x7 0))
    (hvalid_sp : isValidMemAccess sp = true)
    (hvalid_sp4 : isValidMemAccess (sp + 4) = true) :
    cpsTriple code base (base + 20)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** evmStackIs sp (a :: b :: rest))
      ((.x12 ↦ᵣ (sp + 4)) ** (.x7 ↦ᵣ (a ^^^ b)) ** (.x6 ↦ᵣ b) **
       (sp ↦ₘ a) ** evmStackIs (sp + 4) ((a ^^^ b) :: rest)) := by
  simp only [evmStackIs, memBufferIs]
  have hlow := evm_xor_spec code a b sp v7 v6 base
    hfetch0 hfetch1 hfetch2 hfetch3 hfetch4 hvalid_sp hvalid_sp4
  have hframed := cpsTriple_frame_left code base (base + 20) _ _
    (memBufferIs (sp + 4 + 4) rest) (pcFree_memBufferIs (sp + 4 + 4) rest) hlow
  exact cpsTriple_consequence code base (base + 20) _ _ _ _
    (fun h hp => by simp only [sepConj_assoc'] at hp ⊢; exact hp)
    (fun h hp => by simp only [sepConj_assoc'] at hp ⊢; exact hp)
    hframed

end RiscVMacroAsm.Examples
