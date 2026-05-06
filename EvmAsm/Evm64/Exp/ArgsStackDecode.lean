/-
  EvmAsm.Evm64.Exp.ArgsStackDecode

  Pure top-of-stack decoder for EXP executable-spec bridges (GH #92).
-/

import EvmAsm.Evm64.Exp.Args

namespace EvmAsm.Evm64

namespace ExpArgsStackDecode

/--
Decode EXP stack arguments from the top-of-stack list order:
`base, exponent`.

Distinctive token: ExpArgsStackDecode.decodeExpStack? #92.
-/
def decodeExpStack? : List EvmWord → Option ExpArgs.Args
  | base :: exponent :: _ => some (ExpArgs.expArgs base exponent)
  | _ => none

theorem decodeExpStack?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    decodeExpStack? (base :: exponent :: rest) =
      some (ExpArgs.expArgs base exponent) := rfl

theorem decodeExpStack?_eq_some_iff
    {stack : List EvmWord} {args : ExpArgs.Args} :
    decodeExpStack? stack = some args ↔
      ∃ base exponent rest,
        stack = base :: exponent :: rest ∧
          args = ExpArgs.expArgs base exponent := by
  constructor
  · cases stack with
    | nil => simp [decodeExpStack?]
    | cons base s1 =>
      cases s1 with
      | nil => simp [decodeExpStack?]
      | cons exponent rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨base, exponent, rest, rfl, rfl⟩
  · rintro ⟨base, exponent, rest, rfl, rfl⟩
    rfl

theorem decodeExpStack?_base
    (base exponent : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.base)
      (decodeExpStack? (base :: exponent :: rest)) =
      some base := rfl

theorem decodeExpStack?_exponent
    (base exponent : EvmWord) (rest : List EvmWord) :
    Option.map (fun args => args.exponent)
      (decodeExpStack? (base :: exponent :: rest)) =
      some exponent := rfl

end ExpArgsStackDecode

end EvmAsm.Evm64
