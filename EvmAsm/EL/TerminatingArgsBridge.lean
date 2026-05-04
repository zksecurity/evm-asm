/-
  EvmAsm.EL.TerminatingArgsBridge

  Bridge from EVM RETURN/REVERT stack arguments to EL message-call results
  (GH #113).

  Mirrors the shape of `EvmAsm.EL.LogArgsBridge` and
  `EvmAsm.EL.CallArgsBridge`: a tiny pure layer that takes the loaded data
  byte slice, the post-execution `WorldState`, and the remaining gas, and
  produces a `CallResult` with the appropriate `CallStatus` (`.success` for
  RETURN, `.revert` for REVERT). The actual memory-load / state-update work
  belongs to the eventual handler specs — this bridge just packages the
  result.
-/

import EvmAsm.EL.MessageCall
import EvmAsm.Evm64.TerminatingArgs

namespace EvmAsm.EL

namespace TerminatingArgsBridge

abbrev MemoryRange := EvmAsm.Evm64.TerminatingArgs.MemoryRange
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind

/-- Memory range projected from the terminating-args record. -/
def dataRange (args : TerminatingArgs) : MemoryRange :=
  EvmAsm.Evm64.TerminatingArgs.dataRange args

/-- RETURN packages the loaded data slice as a successful call result. -/
def mkReturnResult
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (_args : TerminatingArgs) : CallResult :=
  { status := .success, state := state, output := data, gasRemaining := gasRemaining }

/-- REVERT packages the loaded data slice as a reverted call result. The
    state passed in should already be the pre-revert snapshot — this layer
    does not roll back. -/
def mkRevertResult
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (_args : TerminatingArgs) : CallResult :=
  { status := .revert, state := state, output := data, gasRemaining := gasRemaining }

theorem mkReturnResult_status
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkReturnResult state data gasRemaining args).status = .success := rfl

theorem mkReturnResult_state
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkReturnResult state data gasRemaining args).state = state := rfl

theorem mkReturnResult_output
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkReturnResult state data gasRemaining args).output = data := rfl

theorem mkReturnResult_gasRemaining
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkReturnResult state data gasRemaining args).gasRemaining = gasRemaining := rfl

theorem mkRevertResult_status
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkRevertResult state data gasRemaining args).status = .revert := rfl

theorem mkRevertResult_state
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkRevertResult state data gasRemaining args).state = state := rfl

theorem mkRevertResult_output
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkRevertResult state data gasRemaining args).output = data := rfl

theorem mkRevertResult_gasRemaining
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkRevertResult state data gasRemaining args).gasRemaining = gasRemaining := rfl

theorem mkReturnResult_succeeded
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkReturnResult state data gasRemaining args).succeeded :=
  CallResult.succeeded_mk_success state data gasRemaining

theorem mkRevertResult_reverted
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkRevertResult state data gasRemaining args).reverted :=
  CallResult.reverted_mk_revert state data gasRemaining

end TerminatingArgsBridge

end EvmAsm.EL
