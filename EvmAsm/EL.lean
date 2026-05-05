/-
  EvmAsm.EL

  Root import file for the Execution Layer (EL) specifications.
-/
import EvmAsm.EL.RLP
import EvmAsm.EL.Create
import EvmAsm.EL.CreateAddress
import EvmAsm.EL.CreateAddressExecutableBridge
import EvmAsm.EL.CreateArgsBridge
import EvmAsm.EL.CreateInitcodeBridge
import EvmAsm.EL.CreateEffects
import EvmAsm.EL.CreateResultBridge
import EvmAsm.EL.Logs
import EvmAsm.EL.LogArgsBridge
import EvmAsm.EL.LogDataBridge
import EvmAsm.EL.LogCallEffects
import EvmAsm.EL.LogExecutionBridge
import EvmAsm.EL.KeccakInputBridge
import EvmAsm.EL.KeccakEcallBridge
import EvmAsm.EL.KeccakResultBridge
import EvmAsm.EL.KeccakExecutionBridge
import EvmAsm.EL.Conformance
import EvmAsm.EL.Conformance.Call
import EvmAsm.EL.Conformance.Calldata
import EvmAsm.EL.Conformance.ExpGas
import EvmAsm.EL.Conformance.RLP
import EvmAsm.EL.WorldState
import EvmAsm.EL.WorldStateAccount
import EvmAsm.EL.Storage
import EvmAsm.EL.StorageAccessBridge
import EvmAsm.EL.StorageStackBridge
import EvmAsm.EL.StorageEcallBridge
import EvmAsm.EL.Transaction
import EvmAsm.EL.MessageCall
import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.CallArgsBridge
import EvmAsm.EL.CallInputBridge
import EvmAsm.EL.CallOutputBridge
import EvmAsm.EL.CallOutputMemory
import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.SelfdestructEffects
import EvmAsm.EL.TerminatingArgsBridge
import EvmAsm.EL.TerminatingCallOutput
import EvmAsm.EL.TerminatingCallerVisible
import EvmAsm.EL.TerminatingDataMemory
import EvmAsm.EL.TransactionCall
import EvmAsm.EL.TransactionExecution
import EvmAsm.EL.Block
