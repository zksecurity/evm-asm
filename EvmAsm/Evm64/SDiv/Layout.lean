/-
  EvmAsm.Evm64.SDiv.Layout

  Empty-layout placeholder for the SDIV routine's scratchpad-layout
  abstraction (GH #334 / parent `evm-asm-4mka`, slice `evm-asm-k2czq`).

  Per `AGENTS.md` ("Scratchpad Layout (#334)") and `EvmAsm/Evm64/OPCODE_TEMPLATE.md`,
  any new opcode subtree that will carry internal `sp`-relative scratch
  cells should define a `XxxScratchpadLayout` structure from day one —
  even if it starts empty — to avoid the retrofit tax once the routine
  gains real scratch later. The canonical empty-layout pilots are
  `EvmAsm/Evm64/Multiply/Layout.lean` (slice 3, beads `evm-asm-1d1o`) and
  `EvmAsm/Evm64/Exp/Layout.lean` (`evm-asm-i6oz6`); this file is the SDIV
  analog.

  SDIV today reuses `evm_div` via the LP64 calling convention plus a
  caller-side sign-extraction / sign-fixup wrapper. Any internal
  scratchpad introduced for sign-handling temporaries (e.g. the absolute
  values of operands, or the sign-XOR of the operands carried across the
  inner call) will live here once the per-iteration / full-routine specs
  for `evm_sdiv` migrate to the layout abstraction. No code change to
  existing SDIV specs in this PR — the layout abstraction is purely
  additive. See §7 of `docs/scratchpad-layout-design.md`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

namespace EvmAsm.Evm64

/-- Layout of the SDIV routine's `sp`-relative internal scratch cells.

    Empty placeholder — see file-level doc-comment. The struct has zero
    fields and exists to fix the naming / parameter-passing convention
    shared with `MultiplyScratchpadLayout`, `ExpScratchpadLayout`, the
    future `DivModScratchpadLayout`, and so on.

    Mirrors `ExpScratchpadLayout` exactly, with the rename
    `Exp → SDiv`. -/
structure SDivScratchpadLayout : Type where
  deriving Repr

/-- Validity bundle for `SDivScratchpadLayout`.

    With zero fields the layout has nothing to constrain; `Valid` is
    trivially derivable. Once SDIV gains real scratch, this will carry
    alignment / disjointness / algebraic-relationship obligations on
    the sign-handling temporary cells. -/
structure SDivScratchpadLayout.Valid (_L : SDivScratchpadLayout) : Prop where

/-- The canonical SDIV scratchpad layout.

    Trivial: there is nothing to choose, so canonical = the unique value.
    Once SDIV gains real scratch, this will be the placement matching
    today's hardcoded sign-handling cells (if any are introduced). -/
def canonicalSDivScratchpadLayout : SDivScratchpadLayout := {}

/-- The canonical SDIV scratchpad layout is `Valid`. Trivially discharged
    because the layout struct is empty. -/
theorem canonicalSDivScratchpadLayout_valid :
    canonicalSDivScratchpadLayout.Valid := {}

end EvmAsm.Evm64
