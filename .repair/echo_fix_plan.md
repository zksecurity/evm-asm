# Echo.lean Repair Plan

## Problem
All step proofs use `refine ⟨1, _, ?_, ?_, ?_⟩` which creates unsynthesizable metavariables.

## Solution
Change pattern from:
```lean
refine ⟨1, _, ?_, ?_, ?_⟩
· rw [stepN_one, hs]
· simp [MachineState.setPC]
· refine ⟨?_, ?_, ?_⟩
```

To:
```lean
let s' := ((s.setReg .xN val).setPC (s.pc + 4))
refine ⟨1, s', ?_, ?_, ?_⟩
· rw [stepN_one, hs]
· simp [MachineState.setPC]
· constructor
  · simp [MachineState.getReg, MachineState.setReg]
  · simp [other_props]
```

## Steps to fix
1. Remove unused li_spec and cpsTriple_frame (lines 79-104)
2. Fix step0_spec through step10_spec (12 total)
3. Fix step3_spec (ECALL HINT_READ) - more complex
4. Fix step8_spec (ECALL WRITE) - more complex

## Key insight
Provide explicit `s'` witness for the existential, don't use `_`.
