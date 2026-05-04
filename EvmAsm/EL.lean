/-
  EvmAsm.EL

  Root import file for the Execution Layer (EL) specifications.
-/
import EvmAsm.EL.RLP
import EvmAsm.EL.Create
import EvmAsm.EL.CreateAddress
import EvmAsm.EL.CreateArgsBridge
import EvmAsm.EL.CreateEffects
import EvmAsm.EL.Logs
import EvmAsm.EL.LogArgsBridge
import EvmAsm.EL.LogCallEffects
import EvmAsm.EL.Conformance
import EvmAsm.EL.WorldState
import EvmAsm.EL.WorldStateAccount
import EvmAsm.EL.Storage
import EvmAsm.EL.Transaction
import EvmAsm.EL.MessageCall
import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.CallArgsBridge
import EvmAsm.EL.CallOutputBridge
import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.SelfdestructEffects
import EvmAsm.EL.TerminatingArgsBridge
import EvmAsm.EL.TerminatingCallOutput
import EvmAsm.EL.TransactionCall
import EvmAsm.EL.TransactionExecution
import EvmAsm.EL.Block
