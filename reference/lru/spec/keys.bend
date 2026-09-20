import Base
import ../types/model.bend as T

# Independent key equalities for the built-in key types. They are structural
# and never mention a codec; proofs/key_equality.bend shows that each decides
# propositional equality and agrees with String equality of the encodings.
def nat_equal(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n: True{}
    case 0n 1n+q: False{}
    case 1n+p 0n: False{}
    case 1n+p 1n+q: nat_equal(p, q)

def integer_equal(a: T.Integer, b: T.Integer) -> Bool:
  match a b:
    case T.Positive{x} T.Positive{y}: nat_equal(x, y)
    case T.Negative{x} T.Negative{y}: nat_equal(x, y)
    case T.Positive{x} T.Negative{y}: False{}
    case T.Negative{x} T.Positive{y}: False{}

def integer_same(a: T.Integer) -> T.Integer -> Bool:
  b => integer_equal(a, b)

def bit_equal(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}: True{}
    case True{} False{}: False{}
    case False{} True{}: False{}
    case False{} False{}: True{}

def bits_equal(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n: True{}
    case 1n+p:
      match a:
        case WCon{x, ra}:
          match b:
            case WCon{y, rb}: Bool.and(bit_equal(x, y), bits_equal(p, ra, rb))

def word64_same(a: Word(64n)) -> Word(64n) -> Bool:
  b => bits_equal(64n, a, b)
