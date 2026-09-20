import Base
import ../spec/keys.bend as Keys
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./recency_unique.bend as Unique
import ./lookup_refinement.bend as L
import ./map_routing.bend as Routing

# Each built-in specification key equality is sound and reflexive, hence it
# decides equality; with codec injectivity it therefore coincides with String
# equality of the encoded keys (the `agree` premise of rename_spec.bend).
def nat_sound(a: Nat, b: Nat, e: {Keys.nat_equal(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+q: Empty.absurd({0n == 1n+q : Nat}, Routing.false_true(e))
    case 1n+p 0n: Empty.absurd({1n+p == 0n : Nat}, Routing.false_true(e))
    case 1n+p 1n+q: Equal.cong(Nat, Nat, n => 1n+n, p, q, nat_sound(p, q, e))

def nat_reflexive(a: Nat) -> {Keys.nat_equal(a, a) == True{} : Bool}:
  match a:
    case 0n: {==}
    case 1n+p: nat_reflexive(p)

def integer_sound(a: T.Integer, b: T.Integer, e: {Keys.integer_equal(a, b) == True{} : Bool}) -> {a == b : T.Integer}:
  match a b:
    case T.Positive{x} T.Positive{y}: Equal.cong(Nat, T.Integer, n => T.Positive{n}, x, y, nat_sound(x, y, e))
    case T.Negative{x} T.Negative{y}: Equal.cong(Nat, T.Integer, n => T.Negative{n}, x, y, nat_sound(x, y, e))
    case T.Positive{x} T.Negative{y}: Empty.absurd({T.Positive{x} == T.Negative{y} : T.Integer}, Routing.false_true(e))
    case T.Negative{x} T.Positive{y}: Empty.absurd({T.Negative{x} == T.Positive{y} : T.Integer}, Routing.false_true(e))

def integer_reflexive(a: T.Integer) -> {Keys.integer_equal(a, a) == True{} : Bool}:
  match a:
    case T.Positive{x}: nat_reflexive(x)
    case T.Negative{x}: nat_reflexive(x)

def bit_sound(a: Bool, b: Bool, e: {Keys.bit_equal(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}: {==}
    case True{} False{}: Empty.absurd({True{} == False{} : Bool}, Routing.false_true(e))
    case False{} True{}: Empty.absurd({False{} == True{} : Bool}, Routing.false_true(e))
    case False{} False{}: {==}

def bit_reflexive(a: Bool) -> {Keys.bit_equal(a, a) == True{} : Bool}:
  match a:
    case True{}: {==}
    case False{}: {==}

def bits_cons(+p: Nat, +x: Bool, +y: Bool, +ra: Word(p), +rb: Word(p), ex: {x == y : Bool}, er: {ra == rb : Word(p)}) -> {WCon{x, ra} == WCon{y, rb} : Word(1n+p)}:
  %ex : {WCon{x, ra} == WCon{_, rb} : Word(1n+p)}
  %er : {WCon{x, ra} == WCon{x, _} : Word(1n+p)}
  {==}

def bits_sound(n: Nat, a: Word(n), b: Word(n), +e: {Keys.bits_equal(n, a, b) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          match b:
            case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{+x, +ra}:
          match b:
            case WCon{+y, +rb}: bits_cons(p, x, y, ra, rb, bit_sound(x, y, Routing.and_left(Keys.bit_equal(x, y), Keys.bits_equal(p, ra, rb), e)), bits_sound(p, ra, rb, Routing.and_right(Keys.bit_equal(x, y), Keys.bits_equal(p, ra, rb), e)))

def bits_reflexive(n: Nat, a: Word(n)) -> {Keys.bits_equal(n, a, a) == True{} : Bool}:
  match n:
    case 0n:
      match a:
        case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{+x, +ra}:
          %Equal.sym(Bool, Keys.bit_equal(x, x), True{}, bit_reflexive(x)) : {Bool.and(_, Keys.bits_equal(p, ra, ra)) == True{} : Bool}
          bits_reflexive(p, ra)

def truth_clash(x: Bool, yes: {x == True{} : Bool}, no: {x == False{} : Bool}) -> Empty:
  Routing.false_true(Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, no), yes))

# Decision: String equality of the codes and the key equality take the same
# value; the two mixed cases contradict injectivity or reflexivity.
def integer_decide(+a: T.Integer, +b: T.Integer, x: Bool, ex: {String.eq(Codec.integer_encode(a), Codec.integer_encode(b)) == x : Bool}, y: Bool, ey: {Keys.integer_equal(a, b) == y : Bool}) -> {String.eq(Codec.integer_encode(a), Codec.integer_encode(b)) == Keys.integer_equal(a, b) : Bool}:
  match x y:
    case True{} True{}: Equal.trans(Bool, String.eq(Codec.integer_encode(a), Codec.integer_encode(b)), True{}, Keys.integer_equal(a, b), ex, Equal.sym(Bool, Keys.integer_equal(a, b), True{}, ey))
    case False{} False{}: Equal.trans(Bool, String.eq(Codec.integer_encode(a), Codec.integer_encode(b)), False{}, Keys.integer_equal(a, b), ex, Equal.sym(Bool, Keys.integer_equal(a, b), False{}, ey))
    case True{} False{}:
      +same = Codec.integer_injective(a, b, Unique.equal_boolean(Codec.integer_encode(a), Codec.integer_encode(b), ex))
      Empty.absurd({String.eq(Codec.integer_encode(a), Codec.integer_encode(b)) == Keys.integer_equal(a, b) : Bool}, truth_clash(Keys.integer_equal(a, b), Equal.trans(Bool, Keys.integer_equal(a, b), Keys.integer_equal(b, b), True{}, Equal.cong(T.Integer, Bool, k => Keys.integer_equal(k, b), a, b, same), integer_reflexive(b)), ey))
    case False{} True{}:
      +same = integer_sound(a, b, ey)
      Empty.absurd({String.eq(Codec.integer_encode(a), Codec.integer_encode(b)) == Keys.integer_equal(a, b) : Bool}, truth_clash(String.eq(Codec.integer_encode(a), Codec.integer_encode(b)), Equal.trans(Bool, String.eq(Codec.integer_encode(a), Codec.integer_encode(b)), String.eq(Codec.integer_encode(a), Codec.integer_encode(a)), True{}, Equal.cong(T.Integer, Bool, k => String.eq(Codec.integer_encode(a), Codec.integer_encode(k)), b, a, Equal.sym(T.Integer, a, b, same)), L.string_reflexive(Codec.integer_encode(a))), ex))

def integer_agree(+a: T.Integer, +b: T.Integer) -> {String.eq(Codec.integer_encode(a), Codec.integer_encode(b)) == Keys.integer_same(a)(b) : Bool}:
  integer_decide(a, b, String.eq(Codec.integer_encode(a), Codec.integer_encode(b)), {==}, Keys.integer_equal(a, b), {==})

def word64_decide(+a: Word(64n), +b: Word(64n), x: Bool, ex: {String.eq(Codec.word64_encode(a), Codec.word64_encode(b)) == x : Bool}, y: Bool, ey: {Keys.bits_equal(64n, a, b) == y : Bool}) -> {String.eq(Codec.word64_encode(a), Codec.word64_encode(b)) == Keys.bits_equal(64n, a, b) : Bool}:
  match x y:
    case True{} True{}: Equal.trans(Bool, String.eq(Codec.word64_encode(a), Codec.word64_encode(b)), True{}, Keys.bits_equal(64n, a, b), ex, Equal.sym(Bool, Keys.bits_equal(64n, a, b), True{}, ey))
    case False{} False{}: Equal.trans(Bool, String.eq(Codec.word64_encode(a), Codec.word64_encode(b)), False{}, Keys.bits_equal(64n, a, b), ex, Equal.sym(Bool, Keys.bits_equal(64n, a, b), False{}, ey))
    case True{} False{}:
      +same = Codec.word64_injective(a, b, Unique.equal_boolean(Codec.word64_encode(a), Codec.word64_encode(b), ex))
      Empty.absurd({String.eq(Codec.word64_encode(a), Codec.word64_encode(b)) == Keys.bits_equal(64n, a, b) : Bool}, truth_clash(Keys.bits_equal(64n, a, b), Equal.trans(Bool, Keys.bits_equal(64n, a, b), Keys.bits_equal(64n, b, b), True{}, Equal.cong(Word(64n), Bool, k => Keys.bits_equal(64n, k, b), a, b, same), bits_reflexive(64n, b)), ey))
    case False{} True{}:
      +same = bits_sound(64n, a, b, ey)
      Empty.absurd({String.eq(Codec.word64_encode(a), Codec.word64_encode(b)) == Keys.bits_equal(64n, a, b) : Bool}, truth_clash(String.eq(Codec.word64_encode(a), Codec.word64_encode(b)), Equal.trans(Bool, String.eq(Codec.word64_encode(a), Codec.word64_encode(b)), String.eq(Codec.word64_encode(a), Codec.word64_encode(a)), True{}, Equal.cong(Word(64n), Bool, k => String.eq(Codec.word64_encode(a), Codec.word64_encode(k)), b, a, Equal.sym(Word(64n), a, b, same)), L.string_reflexive(Codec.word64_encode(a))), ex))

def word64_agree(+a: Word(64n), +b: Word(64n)) -> {String.eq(Codec.word64_encode(a), Codec.word64_encode(b)) == Keys.word64_same(a)(b) : Bool}:
  word64_decide(a, b, String.eq(Codec.word64_encode(a), Codec.word64_encode(b)), {==}, Keys.bits_equal(64n, a, b), {==})
