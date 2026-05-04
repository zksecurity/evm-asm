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

/-- STOP packages an empty data slice as a successful call result. The
    `_data` argument keeps the signature uniform across the Kind-keyed
    dispatcher; STOP itself has no return data. -/
def mkStopResult
    (state : WorldState) (_data : List Byte) (gasRemaining : Nat)
    (_args : TerminatingArgs) : CallResult :=
  { status := .success, state := state, output := [], gasRemaining := gasRemaining }

/-- INVALID (and any other failure-class termination) packages an empty
    data slice as a failed call result. The frame status is `.failure`,
    distinct from `.revert`: INVALID consumes all gas and rolls back, but
    that gas/state accounting belongs to the handler layer. -/
def mkFailureResult
    (state : WorldState) (_data : List Byte) (gasRemaining : Nat)
    (_args : TerminatingArgs) : CallResult :=
  { status := .failure, state := state, output := [], gasRemaining := gasRemaining }

/-- Kind-driven dispatcher selecting the appropriate result builder per
    terminating opcode. Mirrors `TerminatingGas.terminatingDynamicCost`'s
    kind-keyed shape so handler call sites can share a single entry
    point. -/
def mkResultFromArgs
    (kind : TerminatingKind) (state : WorldState) (data : List Byte)
    (gasRemaining : Nat) (args : TerminatingArgs) : CallResult :=
  match kind with
  | .stop => mkStopResult state data gasRemaining args
  | .return_ => mkReturnResult state data gasRemaining args
  | .revert => mkRevertResult state data gasRemaining args
  | .invalid => mkFailureResult state data gasRemaining args
  | .selfdestruct => mkStopResult state data gasRemaining args

theorem mkStopResult_status
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkStopResult state data gasRemaining args).status = .success := rfl

theorem mkStopResult_state
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkStopResult state data gasRemaining args).state = state := rfl

theorem mkStopResult_output
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkStopResult state data gasRemaining args).output = [] := rfl

theorem mkStopResult_gasRemaining
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkStopResult state data gasRemaining args).gasRemaining = gasRemaining := rfl

theorem mkStopResult_succeeded
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkStopResult state data gasRemaining args).succeeded :=
  CallResult.succeeded_mk_success state [] gasRemaining

theorem mkFailureResult_status
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkFailureResult state data gasRemaining args).status = .failure := rfl

theorem mkFailureResult_state
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkFailureResult state data gasRemaining args).state = state := rfl

theorem mkFailureResult_output
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkFailureResult state data gasRemaining args).output = [] := rfl

theorem mkFailureResult_gasRemaining
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    (mkFailureResult state data gasRemaining args).gasRemaining = gasRemaining := rfl

theorem mkFailureResult_not_succeeded
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    ¬ (mkFailureResult state data gasRemaining args).succeeded :=
  CallResult.not_succeeded_mk_failure state [] gasRemaining

theorem mkResultFromArgs_stop
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    mkResultFromArgs .stop state data gasRemaining args
      = mkStopResult state data gasRemaining args := rfl

theorem mkResultFromArgs_return
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    mkResultFromArgs .return_ state data gasRemaining args
      = mkReturnResult state data gasRemaining args := rfl

theorem mkResultFromArgs_revert
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    mkResultFromArgs .revert state data gasRemaining args
      = mkRevertResult state data gasRemaining args := rfl

theorem mkResultFromArgs_invalid
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    mkResultFromArgs .invalid state data gasRemaining args
      = mkFailureResult state data gasRemaining args := rfl

theorem mkResultFromArgs_selfdestruct
    (state : WorldState) (data : List Byte) (gasRemaining : Nat)
    (args : TerminatingArgs) :
    mkResultFromArgs .selfdestruct state data gasRemaining args
      = mkStopResult state data gasRemaining args := rfl

end TerminatingArgsBridge

end EvmAsm.EL
