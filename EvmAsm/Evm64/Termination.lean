/-
  EvmAsm.Evm64.Termination

  Pure terminating-status helpers for GH #113.
-/

import EvmAsm.Evm64.EvmState

namespace EvmAsm.Evm64
namespace EvmState

/-- STOP terminates without returndata. -/
def stop (state : EvmState) : EvmState :=
  state.withStatus .stopped

/-- RETURN terminates successfully with returndata bytes. -/
def returnWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.returned data)

/-- REVERT terminates with revert data. -/
def revertWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.reverted data)

/-- INVALID terminates with an error status. -/
def invalid (state : EvmState) : EvmState :=
  state.withStatus .error

@[simp] theorem stop_status (state : EvmState) :
    state.stop.status = .stopped := rfl

@[simp] theorem returnWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status = .returned data := rfl

@[simp] theorem revertWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status = .reverted data := rfl

@[simp] theorem invalid_status (state : EvmState) :
    state.invalid.status = .error := rfl

theorem stop_status_tag (state : EvmState) :
    state.stop.status.tag = 1 := rfl

theorem returnWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status.tag = 2 := rfl

theorem revertWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status.tag = 3 := rfl

theorem invalid_status_tag (state : EvmState) :
    state.invalid.status.tag = 4 := rfl

@[simp] theorem stop_pc (state : EvmState) :
    state.stop.pc = state.pc := rfl

@[simp] theorem returnWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).pc = state.pc := rfl

@[simp] theorem revertWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).pc = state.pc := rfl

@[simp] theorem invalid_pc (state : EvmState) :
    state.invalid.pc = state.pc := rfl

@[simp] theorem stop_stack (state : EvmState) :
    state.stop.stack = state.stack := rfl

@[simp] theorem returnWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).stack = state.stack := rfl

@[simp] theorem revertWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).stack = state.stack := rfl

@[simp] theorem invalid_stack (state : EvmState) :
    state.invalid.stack = state.stack := rfl

end EvmState
end EvmAsm.Evm64
