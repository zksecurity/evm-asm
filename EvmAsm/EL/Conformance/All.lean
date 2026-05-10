/-
  EvmAsm.EL.Conformance.All

  Aggregate Lean-side conformance batch for GH #125.
-/

import EvmAsm.EL.Conformance.Call
import EvmAsm.EL.Conformance.Calldata
import EvmAsm.EL.Conformance.Code
import EvmAsm.EL.Conformance.CreateStackExecution
import EvmAsm.EL.Conformance.ExpGas
import EvmAsm.EL.Conformance.ExpStackExecution
import EvmAsm.EL.Conformance.KeccakStackExecution
import EvmAsm.EL.Conformance.Log
import EvmAsm.EL.Conformance.LogStackExecution
import EvmAsm.EL.Conformance.RLP
import EvmAsm.EL.Conformance.ReturnData
import EvmAsm.EL.Conformance.SignedArithmeticStackExecution
import EvmAsm.EL.Conformance.StorageStackExecution
import EvmAsm.EL.Conformance.TerminatingStackExecution

namespace EvmAsm.EL
namespace Conformance

/-- Aggregate checked conformance results across the current EL vector modules.
    Distinctive token: allConformanceVectors #125. -/
def allConformanceVectors : List CheckResult :=
  Call.callOutputConformanceVectors ++
  Calldata.calldataConformanceVectors ++
  Code.codeConformanceVectors ++
  CreateStackExecution.createStackConformanceVectors ++
  ExpGas.expGasConformanceVectors ++
  ExpStackExecution.expStackConformanceVectors ++
  KeccakStackExecution.keccakStackConformanceVectors ++
  Log.logDataConformanceVectors ++
  LogStackExecution.logStackConformanceVectors ++
  RLP.rlpConformanceVectors ++
  ReturnData.returnDataConformanceVectors ++
  SignedArithmeticStackExecution.signedArithmeticConformanceVectors ++
  StorageStackExecution.storageStackConformanceVectors ++
  TerminatingStackExecution.terminatingStackConformanceVectors

def allConformanceVectorCount : Nat :=
  allConformanceVectors.length

theorem allConformanceVectors_length :
    allConformanceVectors.length = 53 := by
  native_decide

theorem allConformanceVectorCount_eq :
    allConformanceVectorCount = 53 := by
  native_decide

def unexpectedConformanceFailures : List CheckResult :=
  allConformanceVectors.filter
    (fun result =>
      match result with
      | .failed _ => true
      | _ => false)

def allConformanceNoUnexpectedFailures : Bool :=
  unexpectedConformanceFailures.isEmpty

def unexpectedConformanceFailureCount : Nat :=
  unexpectedConformanceFailures.length

def expectedConformanceErrors : List CheckResult :=
  allConformanceVectors.filter
    (fun result =>
      match result with
      | .errored _ _ => true
      | _ => false)

def expectedConformanceErrorCount : Nat :=
  expectedConformanceErrors.length

def successfulConformanceResults : List CheckResult :=
  allConformanceVectors.filter
    (fun result =>
      match result with
      | .passed => true
      | _ => false)

def successfulConformanceResultCount : Nat :=
  successfulConformanceResults.length

theorem unexpectedConformanceFailures_empty :
    unexpectedConformanceFailures = [] := by
  simp [unexpectedConformanceFailures, allConformanceVectors,
    Call.callOutputConformanceVectors_passed,
    Calldata.calldataConformanceVectors_passed,
    Code.codeConformanceVectors_passed,
    CreateStackExecution.createStackConformanceVectors_passed,
    ExpGas.expGasConformanceVectors_passed,
    ExpStackExecution.expStackConformanceVectors_passed,
    KeccakStackExecution.keccakStackConformanceVectors_passed,
    Log.logDataConformanceVectors_passed,
    LogStackExecution.logStackConformanceVectors_passed,
    RLP.rlpConformanceVectors_passed,
    ReturnData.returnDataConformanceVectors_passed,
    SignedArithmeticStackExecution.signedArithmeticConformanceVectors_passed,
    StorageStackExecution.storageStackConformanceVectors_passed,
    TerminatingStackExecution.terminatingStackConformanceVectors_passed]

theorem allConformanceNoUnexpectedFailures_eq_true :
    allConformanceNoUnexpectedFailures = true := by
  simp [allConformanceNoUnexpectedFailures, unexpectedConformanceFailures_empty]

theorem unexpectedConformanceFailureCount_eq_zero :
    unexpectedConformanceFailureCount = 0 := by
  simp [unexpectedConformanceFailureCount, unexpectedConformanceFailures_empty]

theorem expectedConformanceErrorCount_eq :
    expectedConformanceErrorCount = 10 := by
  native_decide

theorem successfulConformanceResultCount_eq :
    successfulConformanceResultCount = 43 := by
  native_decide

end Conformance
end EvmAsm.EL
