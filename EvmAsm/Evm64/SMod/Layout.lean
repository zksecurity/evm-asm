/-
  EvmAsm.Evm64.SMod.Layout

  Empty-layout placeholder for the SMOD routine's scratchpad-layout
  abstraction (GH #334 / parent `evm-asm-4mka`, slice `evm-asm-k2czq`).

  Per `AGENTS.md` ("Scratchpad Layout (#334)") and `EvmAsm/Evm64/OPCODE_TEMPLATE.md`,
  any new opcode subtree that will carry internal `sp`-relative scratch
  cells should define a `XxxScratchpadLayout` structure from day one —
  even if it starts empty — to avoid the retrofit tax once the routine
  gains real scratch later. The canonical empty-layout pilots are
  `EvmAsm/Evm64/Multiply/Layout.lean` (slice 3, beads `evm-asm-1d1o`) and
  `EvmAsm/Evm64/Exp/Layout.lean` (`evm-asm-i6oz6`); this file is the SMOD
  analog.

  SMOD today reuses `evm_mod` via the LP64 calling convention plus a
  caller-side sign-of-dividend wrapper. Any internal scratchpad
  introduced for sign-handling temporaries (e.g. the absolute value of
  the dividend or the recorded sign carried across the inner call) will
  live here once the per-iteration / full-routine specs for `evm_smod`
  migrate to the layout abstraction. No code change to existing SMOD
  specs in this PR — the layout abstraction is purely additive. See §7
  of `docs/scratchpad-layout-design.md`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

namespace EvmAsm.Evm64

/-- Layout of the SMOD routine's `sp`-relative internal scratch cells.

    Empty placeholder — see file-level doc-comment. The struct has zero
    fields and exists to fix the naming / parameter-passing convention
    shared with `MultiplyScratchpadLayout`, `ExpScratchpadLayout`,
    `SDivScratchpadLayout`, the future `DivModScratchpadLayout`, and so
    on.

    Mirrors `SDivScratchpadLayout` exactly, with the rename
    `SDiv → SMod`. -/
structure SModScratchpadLayout : Type where
  deriving Repr

/-- Validity bundle for `SModScratchpadLayout`.

    With zero fields the layout has nothing to constrain; `Valid` is
    trivially derivable. Once SMOD gains real scratch, this will carry
    alignment / disjointness / algebraic-relationship obligations on
    the sign-handling temporary cells. -/
structure SModScratchpadLayout.Valid (_L : SModScratchpadLayout) : Prop where

/-- The canonical SMOD scratchpad layout.

    Trivial: there is nothing to choose, so canonical = the unique value.
    Once SMOD gains real scratch, this will be the placement matching
    today's hardcoded sign-handling cells (if any are introduced). -/
def canonicalSModScratchpadLayout : SModScratchpadLayout := {}

/-- The canonical SMOD scratchpad layout is `Valid`. Trivially discharged
    because the layout struct is empty. -/
theorem canonicalSModScratchpadLayout_valid :
    canonicalSModScratchpadLayout.Valid := {}

end EvmAsm.Evm64
