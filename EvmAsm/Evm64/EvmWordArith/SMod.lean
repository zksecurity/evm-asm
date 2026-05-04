/-
  EvmAsm.Evm64.EvmWordArith.SMod

  EVM SMOD semantics: signed two's-complement remainder of 256-bit words.
  The EVM spec (`execution-specs/src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py`,
  function `smod`, lines 208–235) reads:

  ```
  if y == 0:  remainder = 0
  else:       remainder = sign(x) * (|x| % |y|)
  ```

  Sign of result follows the dividend (truncating-toward-zero modulo), which
  matches `Int.tmod`. The corresponding `BitVec` primitive is `BitVec.srem`,
  not `BitVec.smod` (which is *floored* — sign follows the divisor — and so
  does NOT match EVM SMOD). Concretely:

  * `BitVec.toInt_srem` : `(a.srem b).toInt = a.toInt.tmod b.toInt`        ✓ EVM
  * `BitVec.toInt_smod` : `(a.smod b).toInt = a.toInt.fmod b.toInt`        ✗ EVM

  Like SDIV, the EVM `b = 0 ⇒ 0` short-circuit must be added explicitly:
  `BitVec.srem_zero` returns `x`, not `0`.

  Slice 5a of evm-asm-34sg (#90 SDIV / SMOD opcodes), beads `evm-asm-pc8g6`.
  Mirrors `EvmAsm/Evm64/EvmWordArith/SDiv.lean` (slice 3, `evm-asm-kvs4`).
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EVM SMOD semantics
-- ============================================================================

/-- EVM SMOD: signed two's-complement remainder on 256-bit words.

    Defined as `BitVec.srem` (truncating-toward-zero remainder, sign of
    result follows the dividend) gated by an explicit `b = 0 → 0`
    short-circuit, matching the executable spec.

    Note: We intentionally use `BitVec.srem` rather than `BitVec.smod` —
    the latter implements *floored* (Euclidean) modulo, where the sign of
    the result follows the divisor. EVM SMOD follows the dividend's sign,
    matching `Int.tmod` semantics. -/
def smod (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.srem a b

-- ============================================================================
-- Edge-case lemmas
-- ============================================================================

@[simp]
theorem smod_zero_right {a : EvmWord} : smod a 0 = 0 := by
  simp [smod]

@[simp]
theorem zero_smod_left {b : EvmWord} : smod 0 b = 0 := by
  unfold smod
  split
  · rfl
  · exact BitVec.zero_srem

-- ============================================================================
-- Correctness vs `Int.tmod` (the spec formula)
-- ============================================================================

/-- When the divisor is non-zero, `EvmWord.smod` agrees with the
    executable-spec formula: the truncating-toward-zero integer remainder
    of the signed interpretations of the operands.

    `BitVec.toInt_srem` is the underlying lemma; this just relabels it
    through the `EvmWord.smod` wrapper and discharges the `b = 0` branch
    of `smod`'s definition. The `b = 0 ⇒ 0` short-circuit is captured by
    `smod_zero_right`. -/
theorem smod_correct (a b : EvmWord) (hbnz : b ≠ 0) :
    (smod a b).toInt = a.toInt.tmod b.toInt := by
  simp only [smod, if_neg hbnz]
  exact BitVec.toInt_srem a b

end EvmWord

end EvmAsm.Evm64
