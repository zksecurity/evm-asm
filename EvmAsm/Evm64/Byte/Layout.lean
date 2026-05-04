/-
  EvmAsm.Evm64.Byte.Layout

  Empty-layout pilot for the scratchpad-layout abstraction (GH #334,
  beads evm-asm-dl02 — slice of evm-asm-vst1).

  Mirrors `EvmAsm.Evm64.Multiply.Layout` (PR #1645 / evm-asm-1d1o).

  Per `docs/scratchpad-layout-design.md` §3.2, the BYTE opcode does NOT
  use any `sp + signExtend12 N` *internal* scratch cells: the
  `sp + 0/8/16/24/32/40/48/56` cells touched by `evm_byte`'s bytecode
  are part of the EVM stack frame supplied by the caller, not part of
  the routine's internal scratchpad. They are described directly by the
  precondition of `evm_byte_stack_spec_within`
  (`evmWordIs sp idx ** evmWordIs (sp + 32) val`).

  Consequently the BYTE layout is **empty**. This file still defines
  `ByteScratchpadLayout`, `ByteScratchpadLayout.Valid`,
  `canonicalByteScratchpadLayout`, and a thin layout-parameterized
  restatement of `evm_byte_stack_spec_within` so that:

  1. The naming + file convention is established
     (`Byte/Layout.lean`, `XxxScratchpadLayout`,
     `XxxScratchpadLayout.Valid`, `canonicalXxxScratchpadLayout`,
     `canonicalXxxScratchpadLayout_valid`).
  2. Slice 4 (DivMod / Shift, evm-asm-vst1) has another working
     template to copy alongside Multiply.
  3. Downstream consumers — including any future caller that wants to
     compose BYTE with a routine that DOES carry an internal scratchpad
     — can already write `(L : ByteScratchpadLayout) (hL : L.Valid)`
     parameters in their own preconditions without churn if BYTE ever
     gains real scratch later.

  No code change to existing BYTE specs in this PR — the layout
  abstraction is purely additive. See §7 of the design doc.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Byte.Spec

namespace EvmAsm.Evm64

/-- Layout of the BYTE routine's `sp`-relative internal scratch cells.

    BYTE has none — see file-level doc-comment. The struct is empty
    (one constructor with zero fields) and exists to fix the naming /
    parameter-passing convention shared with `MultiplyScratchpadLayout`,
    `DivModScratchpadLayout`, etc. -/
structure ByteScratchpadLayout : Type where
  deriving Repr

/-- Validity bundle for `ByteScratchpadLayout`.

    With zero fields the layout has nothing to constrain; `Valid` is
    trivially derivable. Slice 4's `DivModScratchpadLayout.Valid` will
    carry alignment / disjointness / algebraic-relationship obligations
    in this same shape. -/
structure ByteScratchpadLayout.Valid (_L : ByteScratchpadLayout) : Prop where

/-- The canonical BYTE scratchpad layout.

    Trivial: there is nothing to choose, so canonical = the unique value. -/
def canonicalByteScratchpadLayout : ByteScratchpadLayout := {}

/-- The canonical BYTE scratchpad layout is `Valid`. -/
theorem canonicalByteScratchpadLayout_valid :
    canonicalByteScratchpadLayout.Valid := {}

-- ============================================================================
-- Layout-parameterized variant of evm_byte_stack_spec_within
-- ============================================================================

open EvmAsm.Rv64

/-- Layout-parameterized restatement of `evm_byte_stack_spec_within`.

    Identical contract — BYTE's stack pre/post depend only on the
    caller-supplied stack frame, not on any internal scratchpad. The `L`
    and `hL` parameters are placeholders that establish the convention
    shared with `MultiplyScratchpadLayout`, `DivModScratchpadLayout`,
    etc. (slice 4); a future caller composing BYTE with a routine that
    DOES use an internal scratchpad can already pass an `L` through
    without conditioning on whether BYTE itself uses it.

    Reduces to `evm_byte_stack_spec_within` by `exact`; the
    canonical-shim pattern from §4 of the design doc is therefore
    degenerate here. -/
theorem evm_byte_stack_spec_within_layout
    (_L : ByteScratchpadLayout) (_hL : _L.Valid)
    (sp base : Word) (idx val : EvmWord) (v5 v6 v10 : Word) :
    cpsTripleWithin 29 base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) val)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
       (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) (EvmWord.byte idx val)) :=
  evm_byte_stack_spec_within sp base idx val v5 v6 v10

end EvmAsm.Evm64
