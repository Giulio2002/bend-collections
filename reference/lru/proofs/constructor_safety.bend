import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/wide.bend as W
import ../types/model.bend as T
import ../spec/numeric.bend as S
import ./public_phase_safety.bend as Phase
import ./numeric.bend as Numeric
import ./cache_key_identity.bend as Key
import ./map_routing.bend as Logic

def double_positive(n: Nat) -> {Nat.is_gt(Nat.double(n), 0n) == Nat.is_gt(n, 0n) : Bool}:
  match n:
    case 0n: {==}
    case 1n+p: {==}

def word_positive(+n: Nat, word: Word(n)) -> {Nat.is_gt(S.unsigned(n, word), 0n) == Bool.not(W.is_zero(n, word)) : Bool}:
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+ +p:
      match word:
        case WCon{False{}, +tail}:
          Equal.trans(Bool, Nat.is_gt(Nat.double(S.unsigned(p, tail)), 0n), Nat.is_gt(S.unsigned(p, tail), 0n), Bool.not(W.is_zero(p, tail)), double_positive(S.unsigned(p, tail)), word_positive(p, tail))
        case WCon{True{}, tail}: {==}

def capacity_positive(cap: U32) -> {Nat.is_gt(U32.to_nat(cap), 0n) == Bool.not(U32.is_eq(cap, 0)) : Bool}:
  U32{+bits} = cap
  %Equal.sym(Nat, Word.to_nat(32n, bits), S.unsigned(32n, bits), Numeric.primitive_word_interpretation(32n, bits)) : {Nat.is_gt(_, 0n) == Bool.not(U32.is_eq(U32{bits}, 0)) : Bool}
  Equal.trans(Bool, Nat.is_gt(S.unsigned(32n, bits), 0n), Bool.not(W.is_zero(32n, bits)), Bool.not(U32.is_eq(U32{bits}, 0)), word_positive(32n, bits), Equal.cong(Bool, Bool, Bool.not, W.is_zero(32n, bits), U32.is_eq(U32{bits}, 0), Equal.sym(Bool, U32.is_eq(U32{bits}, 0), W.is_zero(32n, bits), Numeric.zero_comparison_correspondence(32n, bits))))

def positive_init(~K: Data, ~encode: K -> String, -V: Data, n: Nat, positive: {Nat.is_gt(n, 0n) == True{} : Bool}) -> Phase.safe_cache(~K, ~encode, V, C.init(K, V, n)):
  match n:
    case 0n:
      Empty.absurd(Phase.safe_cache(~K, ~encode, V, C.init(K, V, 0n)), Logic.false_true(positive))
    case 1n+p:
      Phase.initialized(~K, ~encode, V, p)

# Native constructor rejection remains a failure; this predicate asserts safety
# only of actual successful results, not success for every capacity/size input.
def safe_result(~K: Data, ~encode: K -> String, -V: Data, result: Result<&2, &2, String, C.Cache<K, V>>) -> Type:
  match result:
    case Fail{error}: Unit
    case Done{c}: Phase.safe_cache(~K, ~encode, V, c)

def construct(~K: Data, ~encode: K -> String, -V: Data, +cap: U32, size: U32, zero: Bool, reserved: Bool, small: Bool, checked: {U32.is_eq(cap, 0) == zero : Bool}) -> safe_result(~K, ~encode, V, C.construct(K, V, cap, size, zero, reserved, small)):
  match zero reserved small:
    case True{} a b: Unit{}
    case False{} True{} b: Unit{}
    case False{} False{} True{}: Unit{}
    case False{} False{} False{}:
      positive_init(~K, ~encode, V, U32.to_nat(cap), Equal.trans(Bool, Nat.is_gt(U32.to_nat(cap), 0n), Bool.not(U32.is_eq(cap, 0)), True{}, capacity_positive(cap), Equal.cong(Bool, Bool, Bool.not, U32.is_eq(cap, 0), False{}, checked)))

def new_with_size(~K: Data, ~encode: K -> String, -V: Data, +cap: U32, +size: U32) -> safe_result(~K, ~encode, V, C.new_with_size(K, V, cap, size)):
  construct(~K, ~encode, V, cap, size, U32.is_eq(cap, 0), U32.is_eq(size, 4294967295), U32.is_lt(size, cap), {==})

def string_new(-V: Data, cap: U32, size: U32) -> safe_result(~String, ~Codec.string_encode, V, C.new_with_size(String, V, cap, size)):
  new_with_size(~String, ~Codec.string_encode, V, cap, size)

def integer_new(-V: Data, cap: U32, size: U32) -> safe_result(~T.Integer, ~Codec.integer_encode, V, C.new_with_size(T.Integer, V, cap, size)):
  new_with_size(~T.Integer, ~Codec.integer_encode, V, cap, size)

def word64_new(-V: Data, cap: U32, size: U32) -> safe_result(~Word(64n), ~Key.word64_encode, V, C.new_with_size(Word(64n), V, cap, size)):
  new_with_size(~Word(64n), ~Key.word64_encode, V, cap, size)
