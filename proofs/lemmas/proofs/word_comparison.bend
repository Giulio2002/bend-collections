import Base
import ../spec/numeric.bend as S
import ./numeric.bend as N

# Base compares high bits first. Mathematical interpretation preserves that
# exact comparison, including equality, at every width.
def digits(a: Nat, b: Nat, x: Bool, y: Bool) -> {Nat.cmp(Nat.add(S.bit_value(x), Nat.double(a)), Nat.add(S.bit_value(y), Nat.double(b))) == Word.cmp.fin(x, y, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      match x y:
        case False{} False{}: {==}
        case False{} True{}: {==}
        case True{} False{}: {==}
        case True{} True{}: {==}
    case 0n 1n+p:
      match x y:
        case False{} False{}: {==}
        case False{} True{}: {==}
        case True{} False{}: {==}
        case True{} True{}: {==}
    case 1n+p 0n:
      match x y:
        case False{} False{}: {==}
        case False{} True{}: {==}
        case True{} False{}: {==}
        case True{} True{}: {==}
    case 1n+p 1n+q:
      match x y:
        case False{} False{}: digits(p, q, False{}, False{})
        case False{} True{}: digits(p, q, False{}, True{})
        case True{} False{}: digits(p, q, True{}, False{})
        case True{} True{}: digits(p, q, True{}, True{})

def refines(+n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(S.unsigned(n, a), S.unsigned(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(x, y, Word.cmp(p, at, bt)), Word.cmp.fin(x, y, Nat.cmp(S.unsigned(p, at), S.unsigned(p, bt))), Nat.cmp(Nat.add(S.bit_value(x), Nat.double(S.unsigned(p, at))), Nat.add(S.bit_value(y), Nat.double(S.unsigned(p, bt)))), Equal.cong(Cmp, Cmp, c => Word.cmp.fin(x, y, c), Word.cmp(p, at, bt), Nat.cmp(S.unsigned(p, at), S.unsigned(p, bt)), refines(p, at, bt)), Equal.sym(Cmp, Nat.cmp(Nat.add(S.bit_value(x), Nat.double(S.unsigned(p, at))), Nat.add(S.bit_value(y), Nat.double(S.unsigned(p, bt)))), Word.cmp.fin(x, y, Nat.cmp(S.unsigned(p, at), S.unsigned(p, bt))), digits(S.unsigned(p, at), S.unsigned(p, bt), x, y)))

def u32_refines(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Nat, Word.to_nat(32n, x), S.unsigned(32n, x), N.primitive_word_interpretation(32n, x)) : {U32.cmp(U32{x}, U32{y}) == Nat.cmp(_, Word.to_nat(32n, y)) : Cmp}
      %Equal.sym(Nat, Word.to_nat(32n, y), S.unsigned(32n, y), N.primitive_word_interpretation(32n, y)) : {U32.cmp(U32{x}, U32{y}) == Nat.cmp(S.unsigned(32n, x), _) : Cmp}
      refines(32n, x, y)

def u32_ge(+a: U32, +b: U32) -> {U32.is_ge(a, b) == Nat.is_ge(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, Cmp.is_ge, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_refines(a, b))

def u32_lt(+a: U32, +b: U32) -> {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, Cmp.is_lt, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), u32_refines(a, b))
