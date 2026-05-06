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

theorem decodeLogStack?_log0_eq_some_iff
    (stack : List EvmWord) (args : Args) :
    decodeLogStack? .log0 stack = some args ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          args = mkArgs offset size [] := by
  cases stack with
  | nil =>
      simp [decodeLogStack?]
  | cons offset stack =>
      cases stack with
      | nil =>
          simp [decodeLogStack?]
      | cons size rest =>
          constructor
          · intro h_some
            injection h_some with h_args
            subst args
            exact ⟨offset, size, rest, rfl, rfl⟩
          · rintro ⟨_, _, _, h_stack, h_args⟩
            injection h_stack with h_offset h_tail
            injection h_tail with h_size h_rest
            subst_vars
            simp [decodeLogStack?]

theorem decodeLogStack?_log1_eq_some_iff
    (stack : List EvmWord) (args : Args) :
    decodeLogStack? .log1 stack = some args ↔
      ∃ offset size topic0 rest,
        stack = offset :: size :: topic0 :: rest ∧
          args = mkArgs offset size [topic0] := by
  cases stack with
  | nil =>
      simp [decodeLogStack?]
  | cons offset stack =>
      cases stack with
      | nil =>
          simp [decodeLogStack?]
      | cons size stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?]
          | cons topic0 rest =>
              constructor
              · intro h_some
                injection h_some with h_args
                subst args
                exact ⟨offset, size, topic0, rest, rfl, rfl⟩
              · rintro ⟨_, _, _, _, h_stack, h_args⟩
                injection h_stack with h_offset h_tail
                injection h_tail with h_size h_tail'
                injection h_tail' with h_topic0 h_rest
                subst_vars
                simp [decodeLogStack?]

theorem decodeLogStack?_log2_eq_some_iff
    (stack : List EvmWord) (args : Args) :
    decodeLogStack? .log2 stack = some args ↔
      ∃ offset size topic0 topic1 rest,
        stack = offset :: size :: topic0 :: topic1 :: rest ∧
          args = mkArgs offset size [topic0, topic1] := by
  cases stack with
  | nil =>
      simp [decodeLogStack?]
  | cons offset stack =>
      cases stack with
      | nil =>
          simp [decodeLogStack?]
      | cons size stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?]
          | cons topic0 stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?]
              | cons topic1 rest =>
                  constructor
                  · intro h_some
                    injection h_some with h_args
                    subst args
                    exact ⟨offset, size, topic0, topic1, rest, rfl, rfl⟩
                  · rintro ⟨_, _, _, _, _, h_stack, h_args⟩
                    injection h_stack with h_offset h_tail
                    injection h_tail with h_size h_tail'
                    injection h_tail' with h_topic0 h_tail''
                    injection h_tail'' with h_topic1 h_rest
                    subst_vars
                    simp [decodeLogStack?]

theorem decodeLogStack?_log3_eq_some_iff
    (stack : List EvmWord) (args : Args) :
    decodeLogStack? .log3 stack = some args ↔
      ∃ offset size topic0 topic1 topic2 rest,
        stack = offset :: size :: topic0 :: topic1 :: topic2 :: rest ∧
          args = mkArgs offset size [topic0, topic1, topic2] := by
  cases stack with
  | nil =>
      simp [decodeLogStack?]
  | cons offset stack =>
      cases stack with
      | nil =>
          simp [decodeLogStack?]
      | cons size stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?]
          | cons topic0 stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?]
              | cons topic1 stack =>
                  cases stack with
                  | nil =>
                      simp [decodeLogStack?]
                  | cons topic2 rest =>
                      constructor
                      · intro h_some
                        injection h_some with h_args
                        subst args
                        exact ⟨offset, size, topic0, topic1, topic2, rest, rfl, rfl⟩
                      · rintro ⟨_, _, _, _, _, _, h_stack, h_args⟩
                        injection h_stack with h_offset h_tail
                        injection h_tail with h_size h_tail'
                        injection h_tail' with h_topic0 h_tail''
                        injection h_tail'' with h_topic1 h_tail'''
                        injection h_tail''' with h_topic2 h_rest
                        subst_vars
                        simp [decodeLogStack?]

theorem decodeLogStack?_log4_eq_some_iff
    (stack : List EvmWord) (args : Args) :
    decodeLogStack? .log4 stack = some args ↔
      ∃ offset size topic0 topic1 topic2 topic3 rest,
        stack = offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: rest ∧
          args = mkArgs offset size [topic0, topic1, topic2, topic3] := by
  cases stack with
  | nil =>
      simp [decodeLogStack?]
  | cons offset stack =>
      cases stack with
      | nil =>
          simp [decodeLogStack?]
      | cons size stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?]
          | cons topic0 stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?]
              | cons topic1 stack =>
                  cases stack with
                  | nil =>
                      simp [decodeLogStack?]
                  | cons topic2 stack =>
                      cases stack with
                      | nil =>
                          simp [decodeLogStack?]
                      | cons topic3 rest =>
                          constructor
                          · intro h_some
                            injection h_some with h_args
                            subst args
                            exact ⟨offset, size, topic0, topic1, topic2, topic3, rest, rfl, rfl⟩
                          · rintro ⟨_, _, _, _, _, _, _, h_stack, h_args⟩
                            injection h_stack with h_offset h_tail
                            injection h_tail with h_size h_tail'
                            injection h_tail' with h_topic0 h_tail''
                            injection h_tail'' with h_topic1 h_tail'''
                            injection h_tail''' with h_topic2 h_tail''''
                            injection h_tail'''' with h_topic3 h_rest
                            subst_vars
                            simp [decodeLogStack?]

theorem decodeLogStack?_eq_none_iff
    (kind : Kind) (stack : List EvmWord) :
    decodeLogStack? kind stack = none ↔
      stack.length < stackArgumentCount kind := by
  cases kind with
  | log0 =>
      cases stack with
      | nil =>
          simp [decodeLogStack?, stackArgumentCount, topicCount]
      | cons offset stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
          | cons size rest =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
  | log1 =>
      cases stack with
      | nil =>
          simp [decodeLogStack?, stackArgumentCount, topicCount]
      | cons offset stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
          | cons size stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?, stackArgumentCount, topicCount]
              | cons topic0 rest =>
                  simp [decodeLogStack?, stackArgumentCount, topicCount]
  | log2 =>
      cases stack with
      | nil =>
          simp [decodeLogStack?, stackArgumentCount, topicCount]
      | cons offset stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
          | cons size stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?, stackArgumentCount, topicCount]
              | cons topic0 stack =>
                  cases stack with
                  | nil =>
                      simp [decodeLogStack?, stackArgumentCount, topicCount]
                  | cons topic1 rest =>
                      simp [decodeLogStack?, stackArgumentCount, topicCount]
  | log3 =>
      cases stack with
      | nil =>
          simp [decodeLogStack?, stackArgumentCount, topicCount]
      | cons offset stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
          | cons size stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?, stackArgumentCount, topicCount]
              | cons topic0 stack =>
                  cases stack with
                  | nil =>
                      simp [decodeLogStack?, stackArgumentCount, topicCount]
                  | cons topic1 stack =>
                      cases stack with
                      | nil =>
                          simp [decodeLogStack?, stackArgumentCount, topicCount]
                      | cons topic2 rest =>
                          simp [decodeLogStack?, stackArgumentCount, topicCount]
  | log4 =>
      cases stack with
      | nil =>
          simp [decodeLogStack?, stackArgumentCount, topicCount]
      | cons offset stack =>
          cases stack with
          | nil =>
              simp [decodeLogStack?, stackArgumentCount, topicCount]
          | cons size stack =>
              cases stack with
              | nil =>
                  simp [decodeLogStack?, stackArgumentCount, topicCount]
              | cons topic0 stack =>
                  cases stack with
                  | nil =>
                      simp [decodeLogStack?, stackArgumentCount, topicCount]
                  | cons topic1 stack =>
                      cases stack with
                      | nil =>
                          simp [decodeLogStack?, stackArgumentCount, topicCount]
                      | cons topic2 stack =>
                          cases stack with
                          | nil =>
                              simp [decodeLogStack?, stackArgumentCount, topicCount]
                          | cons topic3 rest =>
                              simp [decodeLogStack?, stackArgumentCount, topicCount]

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
