import Base
# Ported from reference/lru/proofs/division_quotient.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_unsigned_division.bend as Spec
import ../../../src/lru/wide.bend as W
import ../../../spec/lru_numeric.bend as S
import ./division_value.bend as Value
import ./division_invariant.bend as Inv
import ./word_comparison.bend as Compare
import ../../../reference/lru/proofs/natural_division.bend as Division
import ../../../reference/lru/proofs/map_routing.bend as Logic
import ./modular_addition.bend as Modular
import ./counter.bend as Counter
import ../../../reference/lru/proofs/map_difference_order.bend as Order

def below_successor(r: Nat, p: Nat) -> {Nat.is_lt(r, 1n+p) == Nat.is_le(r, p) : Bool}:
  match r p:
    case 0n 0n: {==}
    case 0n 1n+k: {==}
    case 1n+0n 0n: {==}
    case 1n+1n+j 0n: {==}
    case 1n+k 1n+j: below_successor(k, j)

def identify(+q: Nat, d: Nat, +r: Nat, bound: {Nat.is_lt(r, d) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(q, d), r), d) == q : Nat}:
  match d:
    case 0n:
      match r:
        case 0n: Empty.absurd({Nat.div(Nat.add(Nat.mul(q, 0n), 0n), 0n) == q : Nat}, Logic.false_true(bound))
        case 1n+p: Empty.absurd({Nat.div(Nat.add(Nat.mul(q, 0n), 1n+p), 0n) == q : Nat}, Logic.false_true(bound))
    case 1n+ +p:
      Division.quotient(q, p, r, Equal.trans(Bool, Nat.is_le(r, p), Nat.is_lt(r, 1n+p), True{}, Equal.sym(Bool, Nat.is_lt(r, 1n+p), Nat.is_le(r, p), below_successor(r, p)), bound))

def quotient(-n: Nat, result: W.Division<n>) -> Word(n):
  W.Div{q, r} = result
  q

def recognizes(+n: Nat, result: W.Division<n>, +d: U32, bound: {U32.is_lt(Inv.remainder(n, result), d) == True{} : Bool}) -> {Nat.div(Value.value(n, result, d), U32.to_nat(d)) == S.unsigned(n, quotient(n, result)) : Nat}:
  match result:
    case W.Div{q, +r}:
      identify(S.unsigned(n, q), U32.to_nat(d), U32.to_nat(r), Equal.trans(Bool, Nat.is_lt(U32.to_nat(r), U32.to_nat(d)), U32.is_lt(r, d), True{}, Equal.sym(Bool, U32.is_lt(r, d), Nat.is_lt(U32.to_nat(r), U32.to_nat(d)), Compare.u32_lt(r, d)), bound))

def natural_quotient(+n: Nat, +word: Word(n), +d: U32, +same: {d == 1000000 : U32}) -> {Nat.div(S.unsigned(n, word), U32.to_nat(d)) == S.unsigned(n, quotient(n, W.div_million(n, word))) : Nat}:
  bound = Equal.trans(Bool, U32.is_lt(Inv.remainder(n, W.div_million(n, word)), d), U32.is_lt(Inv.remainder(n, W.div_million(n, word)), 1000000), True{}, Equal.cong(U32, Bool, x => U32.is_lt(Inv.remainder(n, W.div_million(n, word)), x), d, 1000000, same), Inv.bounded(n, word))
  Equal.trans(Nat, Nat.div(S.unsigned(n, word), U32.to_nat(d)), Nat.div(Value.value(n, W.div_million(n, word), d), U32.to_nat(d)), S.unsigned(n, quotient(n, W.div_million(n, word))), Equal.cong(Nat, Nat, x => Nat.div(x, U32.to_nat(d)), S.unsigned(n, word), Value.value(n, W.div_million(n, word), d), Equal.sym(Nat, Value.value(n, W.div_million(n, word), d), S.unsigned(n, word), Value.conservation(n, word, d, same))), recognizes(n, W.div_million(n, word), d, bound))

def reconstruct(+n: Nat, +word: Word(n)) -> {S.from_nat(n, S.unsigned(n, word)) == word : Word(n)}:
  Equal.trans(Word(n), S.from_nat(n, S.unsigned(n, word)), S.from_nat(n, Nat.add(S.unsigned(n, word), S.scale_binary(n, 0n))), word, Equal.cong(Nat, Word(n), x => S.from_nat(n, x), S.unsigned(n, word), Nat.add(S.unsigned(n, word), S.scale_binary(n, 0n)), Equal.trans(Nat, S.unsigned(n, word), Nat.add(S.unsigned(n, word), 0n), Nat.add(S.unsigned(n, word), S.scale_binary(n, 0n)), Equal.sym(Nat, Nat.add(S.unsigned(n, word), 0n), S.unsigned(n, word), Order.add_zero(S.unsigned(n, word))), Equal.cong(Nat, Nat, x => Nat.add(S.unsigned(n, word), x), 0n, S.scale_binary(n, 0n), Equal.sym(Nat, S.scale_binary(n, 0n), 0n, Counter.scale_zero(n))))), Modular.reconstruct(n, word, 0n))

def word_quotient(+n: Nat, +word: Word(n), +d: U32, same: {d == 1000000 : U32}) -> {quotient(n, W.div_million(n, word)) == S.from_nat(n, Nat.div(S.unsigned(n, word), U32.to_nat(d))) : Word(n)}:
  Equal.trans(Word(n), quotient(n, W.div_million(n, word)), S.from_nat(n, S.unsigned(n, quotient(n, W.div_million(n, word)))), S.from_nat(n, Nat.div(S.unsigned(n, word), U32.to_nat(d))), Equal.sym(Word(n), S.from_nat(n, S.unsigned(n, quotient(n, W.div_million(n, word)))), quotient(n, W.div_million(n, word)), reconstruct(n, quotient(n, W.div_million(n, word)))), Equal.cong(Nat, Word(n), x => S.from_nat(n, x), S.unsigned(n, quotient(n, W.div_million(n, word))), Nat.div(S.unsigned(n, word), U32.to_nat(d)), Equal.sym(Nat, Nat.div(S.unsigned(n, word), U32.to_nat(d)), S.unsigned(n, quotient(n, W.div_million(n, word))), natural_quotient(n, word, d, same))))

def specification_equation(+n: Nat, word: Word(n), +d: U32) -> {Spec.quotient(n, word, d) == S.from_nat(n, Nat.div(S.unsigned(n, word), U32.to_nat(d))) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match word:
        case WCon{bit, tail}: {==}

def guarded(+n: Nat, +word: Word(n), +d: U32, same: {d == 1000000 : U32}) -> {quotient(n, W.div_million(n, word)) == Spec.quotient(n, word, d) : Word(n)}:
  Equal.trans(Word(n), quotient(n, W.div_million(n, word)), S.from_nat(n, Nat.div(S.unsigned(n, word), U32.to_nat(d))), Spec.quotient(n, word, d), word_quotient(n, word, d, same), Equal.sym(Word(n), Spec.quotient(n, word, d), S.from_nat(n, Nat.div(S.unsigned(n, word), U32.to_nat(d))), specification_equation(n, word, d)))

def actual(+n: Nat, word: Word(n)) -> {quotient(n, W.div_million(n, word)) == Spec.quotient(n, word, 1000000) : Word(n)}:
  guarded(n, word, 1000000, {==})

def native_projection(result: W.Division<64n>) -> {W.quotient(result) == quotient(64n, result) : Word(64n)}:
  match result:
    case W.Div{q, r}: {==}

# Connection to the actual duration core and the public independent numeric
# specification's nonnegative branch. Negative sign handling is separate.
def unsigned_milliseconds(+word: Word(64n)) -> {W.unsigned_milliseconds(word) == S.quotient_signed(word, False{}) : Word(64n)}:
  Equal.trans(Word(64n), W.unsigned_milliseconds(word), quotient(64n, W.div_million(64n, word)), S.quotient_signed(word, False{}), native_projection(W.div_million(64n, word)), actual(64n, word))
