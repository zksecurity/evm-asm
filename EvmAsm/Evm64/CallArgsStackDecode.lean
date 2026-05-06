/-
  EvmAsm.Evm64.CallArgsStackDecode

  Pure top-of-stack decoders for CALL-family argument records (GH #114).
-/

import EvmAsm.Evm64.CallArgs

namespace EvmAsm.Evm64

namespace CallArgsStackDecode

open CallArgs

/--
Decode CALL stack arguments from the top-of-stack list order:
`gas, to, value, input_offset, input_size, output_offset, output_size`.

Distinctive token: CallArgsStackDecode.decodeCallStack? #114.
-/
def decodeCallStack? : List EvmWord → Option Call
  | gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
      outputSize :: _ =>
      some
        { gas := gas
          to := to
          value := value
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } }
  | _ => none

/--
Decode STATICCALL stack arguments from the top-of-stack list order:
`gas, to, input_offset, input_size, output_offset, output_size`.
-/
def decodeStaticCallStack? : List EvmWord → Option StaticCall
  | gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: _ =>
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } }
  | _ => none

/--
Decode DELEGATECALL stack arguments from the top-of-stack list order:
`gas, to, input_offset, input_size, output_offset, output_size`.
-/
def decodeDelegateCallStack? : List EvmWord → Option DelegateCall
  | gas :: to :: inputOffset :: inputSize :: outputOffset :: outputSize :: _ =>
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } }
  | _ => none

theorem decodeCallStack?_cons
    (gas to value inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeCallStack?
      (gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          value := value
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeStaticCallStack?_cons
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeStaticCallStack?
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeDelegateCallStack?_cons
    (gas to inputOffset inputSize outputOffset outputSize : EvmWord)
    (rest : List EvmWord) :
    decodeDelegateCallStack?
      (gas :: to :: inputOffset :: inputSize :: outputOffset ::
        outputSize :: rest) =
      some
        { gas := gas
          to := to
          input := { offset := inputOffset, size := inputSize }
          output := { offset := outputOffset, size := outputSize } } := rfl

theorem decodeCallStack?_eq_some_iff {stack : List EvmWord} {args : Call} :
    decodeCallStack? stack = some args ↔
      ∃ gas to value inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: value :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            value := value
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeCallStack?]
        | cons value s3 =>
          cases s3 with
          | nil => simp [decodeCallStack?]
          | cons inputOffset s4 =>
            cases s4 with
            | nil => simp [decodeCallStack?]
            | cons inputSize s5 =>
              cases s5 with
              | nil => simp [decodeCallStack?]
              | cons outputOffset s6 =>
                cases s6 with
                | nil => simp [decodeCallStack?]
                | cons outputSize rest =>
                  intro h
                  injection h with h_args
                  subst h_args
                  exact ⟨gas, to, value, inputOffset, inputSize, outputOffset,
                    outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, value, inputOffset, inputSize, outputOffset, outputSize,
      rest, rfl, rfl⟩
    rfl

theorem decodeStaticCallStack?_eq_some_iff
    {stack : List EvmWord} {args : StaticCall} :
    decodeStaticCallStack? stack = some args ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeStaticCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeStaticCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeStaticCallStack?]
        | cons inputOffset s3 =>
          cases s3 with
          | nil => simp [decodeStaticCallStack?]
          | cons inputSize s4 =>
            cases s4 with
            | nil => simp [decodeStaticCallStack?]
            | cons outputOffset s5 =>
              cases s5 with
              | nil => simp [decodeStaticCallStack?]
              | cons outputSize rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨gas, to, inputOffset, inputSize, outputOffset,
                  outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeDelegateCallStack?_eq_some_iff
    {stack : List EvmWord} {args : DelegateCall} :
    decodeDelegateCallStack? stack = some args ↔
      ∃ gas to inputOffset inputSize outputOffset outputSize rest,
        stack =
          gas :: to :: inputOffset :: inputSize :: outputOffset ::
            outputSize :: rest ∧
        args =
          { gas := gas
            to := to
            input := { offset := inputOffset, size := inputSize }
            output := { offset := outputOffset, size := outputSize } } := by
  constructor
  · cases stack with
    | nil => simp [decodeDelegateCallStack?]
    | cons gas s1 =>
      cases s1 with
      | nil => simp [decodeDelegateCallStack?]
      | cons to s2 =>
        cases s2 with
        | nil => simp [decodeDelegateCallStack?]
        | cons inputOffset s3 =>
          cases s3 with
          | nil => simp [decodeDelegateCallStack?]
          | cons inputSize s4 =>
            cases s4 with
            | nil => simp [decodeDelegateCallStack?]
            | cons outputOffset s5 =>
              cases s5 with
              | nil => simp [decodeDelegateCallStack?]
              | cons outputSize rest =>
                intro h
                injection h with h_args
                subst h_args
                exact ⟨gas, to, inputOffset, inputSize, outputOffset,
                  outputSize, rest, rfl, rfl⟩
  · rintro ⟨gas, to, inputOffset, inputSize, outputOffset, outputSize, rest,
      rfl, rfl⟩
    rfl

theorem decodeCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeCallStack? stack = none ↔ stack.length < 7 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeStaticCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeStaticCallStack? stack = none ↔ stack.length < 6 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeStaticCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeDelegateCallStack?_eq_none_iff (stack : List EvmWord) :
    decodeDelegateCallStack? stack = none ↔ stack.length < 6 := by
  constructor
  · intro h_decode
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [decodeDelegateCallStack?] at h_decode
  · intro h_len
    rcases stack with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp at h_len
      omega

theorem decodeCallStack?_none_of_empty :
    decodeCallStack? [] = none := rfl

theorem decodeCallStack?_none_of_one
    (gas : EvmWord) :
    decodeCallStack? [gas] = none := rfl

theorem decodeCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeCallStack? [gas, to] = none := rfl

theorem decodeCallStack?_none_of_three
    (gas to value : EvmWord) :
    decodeCallStack? [gas, to, value] = none := rfl

theorem decodeCallStack?_none_of_four
    (gas to value inputOffset : EvmWord) :
    decodeCallStack? [gas, to, value, inputOffset] = none := rfl

theorem decodeCallStack?_none_of_five
    (gas to value inputOffset inputSize : EvmWord) :
    decodeCallStack? [gas, to, value, inputOffset, inputSize] = none := rfl

theorem decodeCallStack?_none_of_six
    (gas to value inputOffset inputSize outputOffset : EvmWord) :
    decodeCallStack?
      [gas, to, value, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeStaticCallStack?_none_of_empty :
    decodeStaticCallStack? [] = none := rfl

theorem decodeStaticCallStack?_none_of_one
    (gas : EvmWord) :
    decodeStaticCallStack? [gas] = none := rfl

theorem decodeStaticCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeStaticCallStack? [gas, to] = none := rfl

theorem decodeStaticCallStack?_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeStaticCallStack? [gas, to, inputOffset] = none := rfl

theorem decodeStaticCallStack?_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeStaticCallStack? [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeStaticCallStack?_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeStaticCallStack?
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

theorem decodeDelegateCallStack?_none_of_empty :
    decodeDelegateCallStack? [] = none := rfl

theorem decodeDelegateCallStack?_none_of_one
    (gas : EvmWord) :
    decodeDelegateCallStack? [gas] = none := rfl

theorem decodeDelegateCallStack?_none_of_two
    (gas to : EvmWord) :
    decodeDelegateCallStack? [gas, to] = none := rfl

theorem decodeDelegateCallStack?_none_of_three
    (gas to inputOffset : EvmWord) :
    decodeDelegateCallStack? [gas, to, inputOffset] = none := rfl

theorem decodeDelegateCallStack?_none_of_four
    (gas to inputOffset inputSize : EvmWord) :
    decodeDelegateCallStack? [gas, to, inputOffset, inputSize] = none := rfl

theorem decodeDelegateCallStack?_none_of_five
    (gas to inputOffset inputSize outputOffset : EvmWord) :
    decodeDelegateCallStack?
      [gas, to, inputOffset, inputSize, outputOffset] = none := rfl

end CallArgsStackDecode

end EvmAsm.Evm64
