# evm-asm Separation Logic Tactics

User guide for the frame automation tactics in `EvmAsm/Tactics/`.

## Overview

| Tactic | File | Purpose |
|--------|------|---------|
| `runBlock` | `RunBlock.lean` | Verify a multi-instruction block (main workhorse) |
| `seqFrame` | `SeqFrame.lean` | Compose two `cpsTriple` specs with automatic framing |
| `xcancel` | `XCancel.lean` | Match/cancel separation logic atoms, compute frame |
| `xperm` | `XPerm.lean` | Prove `P = Q` for AC-permutations of `sepConj` chains |
| `@[spec_gen]` | `SpecDb.lean` | Register instruction specs for auto-resolution |
| `#spec_db` | `SpecDb.lean` | Print all registered instruction specs |

**For closing arithmetic / address equality goals**, see the grindsets
documented in [`GRIND.md`](GRIND.md):

| Grindset | File | Closes |
|----------|------|--------|
| `rv64_addr`   | `Rv64/AddrNorm.lean`           | Rv64-wide address arithmetic (signExtend12/13/21 + assoc + `BitVec 6.toNat` + `BitVec.ofNat 64 (4*k)`); subsumes `bv_addr` |
| `divmod_addr` | `Evm64/DivMod/AddrNorm.lean`   | DivMod address arithmetic (re-tags `rv64_addr` atoms + DivMod-specific Phase-1/Phase-2 offsets) |
| `exp_addr`    | `Evm64/Exp/AddrNorm.lean`      | EXP opcode-local atoms (skeleton — attribute reserved; populate atoms + add a `by exp_addr` macro once Exp Compose emits concrete address arithmetic) |
| `reg_ops`     | `Rv64/RegOps.lean`             | `MachineState` projection chains (`pc_set<F>`, `getReg_setPC`, etc.) |
| `byte_alg`    | `Rv64/ByteAlg.lean`            | `extractByte` / `replaceByte` algebra on `Word` |

Each grindset exposes a `by <name>` tactic (`by rv64_addr`, `by divmod_addr`,
`by exp_addr`, …) that tries `grind` first and falls back to a per-domain
`simp only [...]` closer. New atomic facts are added as one-line
`@[<set>, grind =]` lemmas in the set's file; consumers pick them up
automatically.

### Adding a new opcode-specific address grindset

Each opcode subtree opts into the family by shipping an `AddrNormAttr.lean`
+ `AddrNorm.lean` pair. The canonical shape is `EvmAsm/Evm64/Exp/`:

- `Exp/AddrNormAttr.lean` — single-line `register_simp_attr exp_addr`. Lean
  forbids using a freshly-registered simp attribute in the same file that
  declares it, so this *must* be its own module.
- `Exp/AddrNorm.lean` — atomic equalities tagged
  `@[exp_addr, grind =]` (and typically `@[rv64_addr, grind =]` so the
  universal `by rv64_addr` tactic can also close them). Add the new file
  *after* `AddrNormAttr.lean` in the umbrella import list (`Evm64/Exp.lean`)
  so the attribute exists when the consumer is elaborated.

Use `by rv64_addr` everywhere by default — it covers `signExtend12 N` and
`<<<` over numeric literals universally. Reach for `by divmod_addr` /
`by exp_addr` only when the goal mentions an opcode-specific atom (an
offset constant defined in that subtree, an opcode-specific scratch-cell
identity, etc.). See `EvmAsm/Evm64/OPCODE_TEMPLATE.md` §2.5 for the
requirement to ship this pair on the first commit introducing a non-trivial
address computation.

## runBlock

The primary tactic for verifying basic blocks. Composes instruction specs
with automatic framing, address normalization, and postcondition permutation.

### Auto mode (preferred)

When called with no arguments, `runBlock` resolves specs from the `@[spec_gen]`
database by inspecting the goal's precondition:

```lean
theorem add_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 sum carry : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 20)
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
       ((base + 16) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (...) := by
  runBlock  -- verifies all 5 instructions automatically
```

### Manual mode

Pass spec hypotheses when auto-resolution can't handle composite specs:

```lean
theorem add_limb_carry_spec ... := by
  have s1 := add_limb_carry_spec_phase1 ...
  have s2 := add_limb_carry_spec_phase2 ...
  runBlock s1 s2
```

### Requirements

- Goal must be a `cpsTriple entry exit pre post`
- **Auto mode**: precondition must contain `instrAt` (`↦ᵢ`) atoms with concrete
  instruction constructors (e.g., `.ADD .x7 .x7 .x6`)
- **Manual mode**: each argument must be a `cpsTriple` proof

### Debugging

Enable trace output to see what `runBlock` is doing:

```lean
set_option trace.runBlock true in
theorem my_spec ... := by runBlock
```

This shows:
- Number of instructions and state atoms detected
- Which specs are being tried for each instruction
- Which spec was selected
- Composition progress

### Common failure modes

| Symptom | Cause | Fix |
|---------|-------|-----|
| "no @[spec_gen] specs registered for ..." | Instruction not in database | Add `@[spec_gen]` to a spec, or use manual mode |
| "cannot solve proof obligation: ..." | Missing hypothesis (e.g., `isValidMemAccess`) | Add hypothesis to theorem statement |
| "no spec could be instantiated" | Register/memory state doesn't match any spec variant | Check spec variants with `#spec_db`; may need a new spec |
| "h2's precondition atom not found..." | Specs don't chain (postcondition mismatch) | Check spec ordering and intermediate state |

## seqFrame

Composes two `cpsTriple` specs with automatic frame computation:

```lean
have s1 : cpsTriple base mid P Q1 := ...
have s2 : cpsTriple mid exit_ P2 Q2 := ...
seqFrame s1 s2
-- Produces: cpsTriple base exit_ P (Q2 ** Frame)
-- where Frame = Q1 atoms not consumed by P2
```

If the goal is a `cpsTriple`, `seqFrame` tries to close it (with postcondition
permutation). Otherwise, the result is introduced as a hypothesis named `s1s2`.

## xcancel

Cancellation tactic for separation logic assertions:

```lean
-- h : (A ** B ** C ** D) s
-- Goal: (A ** C ** ?Frame) s
xcancel h
-- Closes goal, unifying ?Frame with (B ** D)
```

## xperm

Proves equality between AC-permutations of `sepConj` chains:

```lean
example : (A ** B ** C) = (C ** A ** B) := by xperm
```

Used internally by all other tactics. Also available as `xperm_hyp` (in
`XSimp.lean`) for rewriting hypotheses.

## extract_pure

Drains pure (`⌜P⌝`) atoms out of a separation-logic hypothesis so they
can be obtained directly. Replaces the long `obtain ⟨_, _, _, _, _, h⟩ := h`
chain that was previously needed to walk past every resource atom to reach
a buried pure assertion.

```lean
example (s : PartialState) (R : Assertion) (P Q : Prop)
    (h : (R ** ⌜P⌝ ** ⌜Q⌝) s) : P ∧ Q := by
  extract_pure h
  exact ⟨h.1, h.2.1⟩
```

After `extract_pure h`, `h` has type `P₁ ∧ … ∧ Pₖ ∧ (resourceTail s)` —
the pure atoms are exposed as the leading conjuncts. Defined in
`EvmAsm/Rv64/Tactics/ExtractPure.lean`. Implemented as a `simp only`
macro using left-associativity normalisation plus the
`sepConj_pure_left/right/mid_*` iff lemmas.

## drop_pure

Sibling of `extract_pure` that *discards* the pure atoms instead of
exposing them, rebinding the hypothesis to the bare resource tail.
Useful when the goal has no pure atoms (so neither `extract_pure` +
`obtain` nor `xperm_pure` compose cleanly): after `drop_pure h`, a
follow-up `xperm_hyp h` works directly with no destructuring.

```lean
example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂) s) : (R₂ ** R₁) s := by
  drop_pure h
  xperm_hyp h
```

Defined in `EvmAsm/Rv64/Tactics/DropPure.lean`. Reuses
`extract_pure`'s normalisation lemmas plus a small projection loop
that peels `.2` off `h` until no `And` remains.

## @[spec_gen] and #spec_db

### Registering specs

Tag single-instruction specs with `@[spec_gen]`:

```lean
@[spec_gen]
theorem lw_spec_gen (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) **
       ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) **
       ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := ...
```

Requirements:
- Must be `cpsTriple`, `cpsBranch`, or `cpsHaltTriple`
- Precondition must contain an `instrAt` (`↦ᵢ`) atom
- The instruction must be a concrete constructor application
- Multiple specs per instruction are allowed (tried in registration order)

### Inspecting the database

```lean
#spec_db  -- prints all registered specs grouped by instruction constructor
```

### Auto-resolution algorithm

For each instruction in the precondition, `runBlock` (auto mode):
1. Extracts the instruction constructor name (e.g., `EvmAsm.Instr.LW`)
2. Looks up all `@[spec_gen]` entries for that constructor
3. For each candidate spec:
   a. Creates metavariables for all universally quantified parameters
   b. Unifies the spec's `instrAt`, `regIs`, and `memIs` atoms against the state
   c. Solves proof obligations: `mkDecideProof` for `rd ≠ .x0`/`rd ≠ rs`,
      local context search for other hypotheses, `bv_omega` as fallback
4. Returns the first successfully instantiated spec

## Architecture

```
xperm (AC permutation proofs)
  └── xcancel (cancellation with frame computation)
        └── seqFrame (two-spec composition with framing)
              └── runBlock (multi-spec composition)
                    └── SpecDb (@[spec_gen] registry for auto-resolution)
```

Each layer builds on the one below. All tactics work at the `MetaM` level,
constructing proof terms directly rather than using tactic combinators.


## Scratchpad layout (parameterizing internal scratch cells)

Routines with `sp`-relative internal scratch cells must take their layout as
a parameter rather than baking `sp + signExtend12 N` literals into the spec.
The convention lives in `AGENTS.md` (section "Scratchpad Layout (#334)") and
the design rationale + migration plan in
`docs/scratchpad-layout-design.md`.

Canonical instances:

- `EvmAsm/Evm64/Multiply/Layout.lean` — empty-layout pilot (Multiply has no
  internal scratch; struct defined to fix the naming convention).
- DivMod / Byte / Shift layouts will follow the same shape under #334
  slice 4 (beads `evm-asm-vst1`).

When writing a new spec that touches scratchpad cells, prefer
`L.fieldName` over `sp + signExtend12 N` and add `(L : XxxScratchpadLayout)
(hL : L.Valid)` parameters from day one.
