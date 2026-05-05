/-
  EvmAsm.Evm64.LogArgsStackDecode

  Pure top-of-stack decoders for LOG0 through LOG4 arguments (GH #112).
-/

import EvmAsm.Evm64.LogArgs

namespace EvmAsm.Evm64

namespace LogArgsStackDecode

open LogArgs

def mkArgs (offset size : EvmWord) (topics : List EvmWord) : Args :=
  { data := { offset := offset, size := size }, topics := topics }

/--
Decode LOG-family stack arguments from the top-of-stack list order:
`offset, size, topic0, topic1, ...`.

Distinctive token: LogArgsStackDecode.decodeLogStack? #112.
-/
def decodeLogStack? : Kind → List EvmWord → Option Args
  | .log0, offset :: size :: _ =>
      some (mkArgs offset size [])
  | .log1, offset :: size :: topic0 :: _ =>
      some (mkArgs offset size [topic0])
  | .log2, offset :: size :: topic0 :: topic1 :: _ =>
      some (mkArgs offset size [topic0, topic1])
  | .log3, offset :: size :: topic0 :: topic1 :: topic2 :: _ =>
      some (mkArgs offset size [topic0, topic1, topic2])
  | .log4, offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: _ =>
      some (mkArgs offset size [topic0, topic1, topic2, topic3])
  | _, _ => none

theorem decodeLogStack?_log0
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log0 (offset :: size :: rest) =
      some (mkArgs offset size []) := rfl

theorem decodeLogStack?_log1
    (offset size topic0 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log1 (offset :: size :: topic0 :: rest) =
      some (mkArgs offset size [topic0]) := rfl

theorem decodeLogStack?_log2
    (offset size topic0 topic1 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log2 (offset :: size :: topic0 :: topic1 :: rest) =
      some (mkArgs offset size [topic0, topic1]) := rfl

theorem decodeLogStack?_log3
    (offset size topic0 topic1 topic2 : EvmWord) (rest : List EvmWord) :
    decodeLogStack? .log3
      (offset :: size :: topic0 :: topic1 :: topic2 :: rest) =
      some (mkArgs offset size [topic0, topic1, topic2]) := rfl

theorem decodeLogStack?_log4
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (rest : List EvmWord) :
    decodeLogStack? .log4
      (offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest) =
      some (mkArgs offset size [topic0, topic1, topic2, topic3]) := rfl

theorem decodeLogStack?_log0_topicCountOk
    (offset size : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log0 (mkArgs offset size []) := rfl

theorem decodeLogStack?_log1_topicCountOk
    (offset size topic0 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log1 (mkArgs offset size [topic0]) := rfl

theorem decodeLogStack?_log2_topicCountOk
    (offset size topic0 topic1 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log2 (mkArgs offset size [topic0, topic1]) := rfl

theorem decodeLogStack?_log3_topicCountOk
    (offset size topic0 topic1 topic2 : EvmWord) (_rest : List EvmWord) :
    topicCountOk .log3 (mkArgs offset size [topic0, topic1, topic2]) := rfl

theorem decodeLogStack?_log4_topicCountOk
    (offset size topic0 topic1 topic2 topic3 : EvmWord)
    (_rest : List EvmWord) :
    topicCountOk .log4
      (mkArgs offset size [topic0, topic1, topic2, topic3]) := rfl

end LogArgsStackDecode

end EvmAsm.Evm64
