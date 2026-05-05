/-
  EvmAsm.Evm64.CreateArgsStackDecode

  Pure top-of-stack decoders for CREATE and CREATE2 arguments (GH #115).
-/

import EvmAsm.Evm64.CreateArgs

namespace EvmAsm.Evm64

namespace CreateArgsStackDecode

open CreateArgs

inductive Decoded where
  | create (args : Create)
  | create2 (args : Create2)
  deriving Repr

def mkCreate (value offset size : EvmWord) : Create :=
  { value := value, initcode := { offset := offset, size := size } }

def mkCreate2 (value offset size salt : EvmWord) : Create2 :=
  { value := value, initcode := { offset := offset, size := size }, salt := salt }

def decodedKind : Decoded → Kind
  | .create _ => .create
  | .create2 _ => .create2

def decodedInitcode : Decoded → InitcodeRange
  | .create args => args.initcode
  | .create2 args => args.initcode

def decodedUsesSalt (decoded : Decoded) : Bool :=
  usesSalt (decodedKind decoded)

def decodedArgumentCount (decoded : Decoded) : Nat :=
  argumentCount (decodedKind decoded)

/--
Decode CREATE-family stack arguments from the top-of-stack list order:
`value, offset, size` for CREATE and `value, offset, size, salt` for CREATE2.

Distinctive token: CreateArgsStackDecode.decodeCreateStack? #115.
-/
def decodeCreateStack? : Kind → List EvmWord → Option Decoded
  | .create, value :: offset :: size :: _ =>
      some (.create (mkCreate value offset size))
  | .create2, value :: offset :: size :: salt :: _ =>
      some (.create2 (mkCreate2 value offset size salt))
  | _, _ => none

theorem decodeCreateStack?_create
    (value offset size : EvmWord) (rest : List EvmWord) :
    decodeCreateStack? .create (value :: offset :: size :: rest) =
      some (.create (mkCreate value offset size)) := rfl

theorem decodeCreateStack?_create2
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    decodeCreateStack? .create2 (value :: offset :: size :: salt :: rest) =
      some (.create2 (mkCreate2 value offset size salt)) := rfl

theorem decodedKind_create (value offset size : EvmWord) :
    decodedKind (.create (mkCreate value offset size)) = .create := rfl

theorem decodedKind_create2 (value offset size salt : EvmWord) :
    decodedKind (.create2 (mkCreate2 value offset size salt)) = .create2 := rfl

theorem decodedInitcode_create (value offset size : EvmWord) :
    decodedInitcode (.create (mkCreate value offset size)) =
      { offset := offset, size := size } := rfl

theorem decodedInitcode_create2 (value offset size salt : EvmWord) :
    decodedInitcode (.create2 (mkCreate2 value offset size salt)) =
      { offset := offset, size := size } := rfl

theorem decodedUsesSalt_create (value offset size : EvmWord) :
    decodedUsesSalt (.create (mkCreate value offset size)) = false := rfl

theorem decodedUsesSalt_create2 (value offset size salt : EvmWord) :
    decodedUsesSalt (.create2 (mkCreate2 value offset size salt)) = true := rfl

theorem decodedArgumentCount_create (value offset size : EvmWord) :
    decodedArgumentCount (.create (mkCreate value offset size)) = 3 := rfl

theorem decodedArgumentCount_create2 (value offset size salt : EvmWord) :
    decodedArgumentCount (.create2 (mkCreate2 value offset size salt)) = 4 := rfl

end CreateArgsStackDecode

end EvmAsm.Evm64
