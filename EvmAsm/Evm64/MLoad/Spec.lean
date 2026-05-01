/-
  EvmAsm.Evm64.MLoad.Spec

  Stack-level bridge lemmas for the MLOAD result word.  The instruction
  composition proves four packed 64-bit output limbs; this file packages
  those limbs as a single `EvmWord` and folds the four destination cells into
  `evmWordIs`.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Evm64.MLoad.LimbSpecEight

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The 256-bit value assembled by MLOAD from four little-endian output limbs. -/
def mloadLoadedWord (l0 l1 l2 l3 : Word) : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => l0
    | 1 => l1
    | 2 => l2
    | 3 => l3

theorem getLimbN_mloadLoadedWord_0 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 0 = l0 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_1 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 1 = l1 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_2 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 2 = l2 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_3 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 3 = l3 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

/-- Fold the four MLOAD destination limbs into a single `evmWordIs` assertion. -/
theorem mloadLoadedWord_evmWordIs_fold (sp l0 l1 l2 l3 : Word) :
    ((sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
     ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3)) =
    evmWordIs sp (mloadLoadedWord l0 l1 l2 l3) := by
  rw [evmWordIs_sp_unfold]
  rw [getLimbN_mloadLoadedWord_0, getLimbN_mloadLoadedWord_1,
    getLimbN_mloadLoadedWord_2, getLimbN_mloadLoadedWord_3]

end EvmAsm.Evm64
