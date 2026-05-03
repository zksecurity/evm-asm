/-
  EvmAsm.EL.LogArgsBridge

  Bridge from EVM LOG stack arguments to EL log entries (GH #112).
-/

import EvmAsm.EL.Logs
import EvmAsm.Evm64.LogArgs

namespace EvmAsm.EL

namespace LogArgsBridge

abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind

def topic (word : EvmAsm.Evm64.EvmWord) : LogTopic :=
  word

def topics (args : LogArgs) : List LogTopic :=
  args.topics

/-- Build the EL log entry once the memory slice has been loaded into bytes. -/
def mkLogEntry (emitter : Address) (data : List Byte) (args : LogArgs) : LogEntry :=
  LogEntry.mkChecked emitter (topics args) data

theorem mkLogEntryEmitter (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).emitter = emitter := rfl

theorem mkLogEntryData (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).data = data := rfl

theorem mkLogEntryTopics (emitter : Address) (data : List Byte) (args : LogArgs) :
    (mkLogEntry emitter data args).topics = topics args := rfl

theorem topicCountOk_of_logArgs
    (kind : LogKind) (emitter : Address) (data : List Byte) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    (mkLogEntry emitter data args).topicCountOk := by
  cases kind
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    simp [h_topics]
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega
  · simp [mkLogEntry, topics, LogEntry.mkChecked, LogEntry.topicCountOk,
      EvmAsm.Evm64.LogArgs.topicCountOk, EvmAsm.Evm64.LogArgs.topicCount] at h_topics ⊢
    omega

theorem topicCountOk_log0 (emitter : Address) (data : List Byte)
    (range : EvmAsm.Evm64.LogArgs.MemoryRange) :
    (mkLogEntry emitter data { data := range, topics := [] }).topicCountOk := by
  exact topicCountOk_of_logArgs .log0 emitter data { data := range, topics := [] } rfl

theorem topicCountOk_log4
    (emitter : Address) (data : List Byte) (range : EvmAsm.Evm64.LogArgs.MemoryRange)
    (topic0 topic1 topic2 topic3 : EvmAsm.Evm64.EvmWord) :
    (mkLogEntry emitter data
        { data := range, topics := [topic0, topic1, topic2, topic3] }).topicCountOk := by
  exact topicCountOk_of_logArgs .log4 emitter data
    { data := range, topics := [topic0, topic1, topic2, topic3] } rfl

end LogArgsBridge

end EvmAsm.EL
