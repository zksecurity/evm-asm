/-
  EvmAsm.Evm64.DivMod.Compose.Dispatcher

  Dispatcher-level scaffold for the bounded DIV/MOD limb specs.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Full
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Dispatcher-facing DIV code requirement. Kept as a named alias so future
    dispatcher proofs can depend on a stable surface instead of unfolding
    `divCode` at every call site. -/
abbrev divDispatcherCode (base : Word) : CodeReq :=
  divCode base

/-- Dispatcher-facing MOD code requirement. -/
abbrev modDispatcherCode (base : Word) : CodeReq :=
  modCode base

theorem divDispatcherCode_sub_divCode {base : Word} :
    ∀ a i, (divDispatcherCode base) a = some i → (divCode base) a = some i := by
  intro a i h
  exact h

theorem modDispatcherCode_sub_modCode {base : Word} :
    ∀ a i, (modDispatcherCode base) a = some i → (modCode base) a = some i := by
  intro a i h
  exact h

theorem sharedDivModCode_sub_divDispatcherCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (divDispatcherCode base) a = some i :=
  sharedDivModCode_sub_divCode

theorem sharedDivModCode_sub_modDispatcherCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (modDispatcherCode base) a = some i :=
  sharedDivModCode_sub_modCode

abbrev evm_div_spec_within_bzero := evm_div_bzero_spec_within
abbrev evm_div_spec_within_n1Full := evm_div_n1_full_unified_spec
abbrev evm_div_spec_within_n2Full := evm_div_n2_full_bundled_spec
abbrev evm_div_spec_within_n3Full := evm_div_n3_full_unified_spec
abbrev evm_div_spec_within_n4MaxSkip := evm_div_n4_full_max_skip_spec
abbrev evm_div_spec_within_n4CallSkip := evm_div_n4_full_call_skip_spec
abbrev evm_div_spec_within_n4MaxAddbackBeq := evm_div_n4_full_max_addback_beq_spec
abbrev evm_div_spec_within_n4CallAddbackBeq := evm_div_n4_full_call_addback_beq_spec
abbrev evm_div_spec_within_n4Shift0CallSkip := evm_div_n4_full_shift0_call_skip_spec
abbrev evm_div_spec_within_n4Shift0CallAddbackBeq :=
  evm_div_n4_full_shift0_call_addback_beq_spec

abbrev evm_mod_spec_within_bzero := evm_mod_bzero_spec_within
abbrev evm_mod_spec_within_n1Full := evm_mod_n1_full_unified_spec
abbrev evm_mod_spec_within_n2Full := evm_mod_n2_full_unified_spec
abbrev evm_mod_spec_within_n3Full := evm_mod_n3_full_unified_spec
abbrev evm_mod_spec_within_n4MaxSkip := evm_mod_n4_full_max_skip_spec_within
abbrev evm_mod_spec_within_n4CallSkip := evm_mod_n4_full_call_skip_spec_within
abbrev evm_mod_spec_within_n4CallAddbackBeq := evm_mod_n4_full_call_addback_beq_spec_within
abbrev evm_mod_spec_within_n4Shift0CallSkip := evm_mod_n4_full_shift0_call_skip_spec
abbrev evm_mod_spec_within_n4Shift0CallAddbackBeq :=
  evm_mod_n4_full_shift0_call_addback_beq_spec

inductive DivDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4MaxSkip
  | n4CallSkip
  | n4MaxAddbackBeq
  | n4CallAddbackBeq
  | n4Shift0CallSkip
  | n4Shift0CallAddbackBeq
  deriving DecidableEq, Repr

inductive ModDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4MaxSkip
  | n4CallSkip
  | n4CallAddbackBeq
  | n4Shift0CallSkip
  | n4Shift0CallAddbackBeq
  deriving DecidableEq, Repr

def DivDispatchBranch.bound : DivDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => 946
  | .n2Full => 744
  | .n3Full => 542
  | .n4MaxSkip => 214
  | .n4CallSkip => 264
  | .n4MaxAddbackBeq => 290
  | .n4CallAddbackBeq => 340
  | .n4Shift0CallSkip => 208
  | .n4Shift0CallAddbackBeq => 284

def ModDispatchBranch.bound : ModDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => 946
  | .n2Full => 744
  | .n3Full => 542
  | .n4MaxSkip => 214
  | .n4CallSkip => 264
  | .n4CallAddbackBeq => 340
  | .n4Shift0CallSkip => 208
  | .n4Shift0CallAddbackBeq => 284

/-- Dispatcher registry for bounded limb-level DIV paths. The proof surface is
    the corresponding path theorem named in each branch comment below. -/
def evm_div_spec_within : List (DivDispatchBranch × Nat) :=
  [(.bzero, DivDispatchBranch.bound .bzero),                         -- evm_div_bzero_spec_within
   (.n1Full, DivDispatchBranch.bound .n1Full),                       -- evm_div_n1_full_unified_spec
   (.n2Full, DivDispatchBranch.bound .n2Full),                       -- evm_div_n2_full_bundled_spec
   (.n3Full, DivDispatchBranch.bound .n3Full),                       -- evm_div_n3_full_unified_spec
   (.n4MaxSkip, DivDispatchBranch.bound .n4MaxSkip),                 -- evm_div_n4_full_max_skip_spec
   (.n4CallSkip, DivDispatchBranch.bound .n4CallSkip),               -- evm_div_n4_full_call_skip_spec
   (.n4MaxAddbackBeq, DivDispatchBranch.bound .n4MaxAddbackBeq),     -- evm_div_n4_full_max_addback_beq_spec
   (.n4CallAddbackBeq, DivDispatchBranch.bound .n4CallAddbackBeq),   -- evm_div_n4_full_call_addback_beq_spec
   (.n4Shift0CallSkip, DivDispatchBranch.bound .n4Shift0CallSkip),   -- evm_div_n4_full_shift0_call_skip_spec
   (.n4Shift0CallAddbackBeq, DivDispatchBranch.bound .n4Shift0CallAddbackBeq)]
                                                                        -- evm_div_n4_full_shift0_call_addback_beq_spec

/-- Dispatcher registry for bounded limb-level MOD paths. -/
def evm_mod_spec_within : List (ModDispatchBranch × Nat) :=
  [(.bzero, ModDispatchBranch.bound .bzero),                         -- evm_mod_bzero_spec_within
   (.n1Full, ModDispatchBranch.bound .n1Full),                       -- evm_mod_n1_full_unified_spec
   (.n2Full, ModDispatchBranch.bound .n2Full),                       -- evm_mod_n2_full_unified_spec
   (.n3Full, ModDispatchBranch.bound .n3Full),                       -- evm_mod_n3_full_unified_spec
   (.n4MaxSkip, ModDispatchBranch.bound .n4MaxSkip),                 -- evm_mod_n4_full_max_skip_spec_within
   (.n4CallSkip, ModDispatchBranch.bound .n4CallSkip),               -- evm_mod_n4_full_call_skip_spec_within
   (.n4CallAddbackBeq, ModDispatchBranch.bound .n4CallAddbackBeq),   -- evm_mod_n4_full_call_addback_beq_spec_within
   (.n4Shift0CallSkip, ModDispatchBranch.bound .n4Shift0CallSkip),   -- evm_mod_n4_full_shift0_call_skip_spec
   (.n4Shift0CallAddbackBeq, ModDispatchBranch.bound .n4Shift0CallAddbackBeq)]
                                                                        -- evm_mod_n4_full_shift0_call_addback_beq_spec

end EvmAsm.Evm64
