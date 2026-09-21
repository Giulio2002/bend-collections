import Base
# Ported from reference/lru/proofs/subtraction_bounds.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as S
import ../../../reference/lru/proofs/map_difference_order.bend as Order
import ../../../reference/lru/proofs/map_routing.bend as Logic
import ../../../reference/lru/proofs/native_map.bend as Natural
import ./natural_products.bend as Product
import ./addition_bounds.bend as Bounds
import ./counter.bend as Counter
import ./word_subtraction.bend as Sub
import ./addition.bend as Add
import ./modular_negation.bend as Neg
import ../../../reference/lru/proofs/map_index.bend as Index
import ./word_bounds.bend as WB
import ./numeric.bend as Numeric

# If both minuends contain b, rearrange their complementary differences.
def complementary_difference(+a: Nat, +b: Nat, +m: Nat, ab: {Nat.is_le(b, a) == True{} : Bool}, bm: {Nat.is_le(b, m) == True{} : Bool}) -> {Nat.add(a, Nat.sub(m, b)) == Nat.add(Nat.sub(a, b), m) : Nat}:
  %Order.add_complement(a, b, ab) : {Nat.add(_, Nat.sub(m, b)) == Nat.add(Nat.sub(a, b), m) : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(b, Nat.sub(a, b)), Nat.sub(m, b)), Nat.add(Nat.sub(a, b), Nat.add(b, Nat.sub(m, b))), Nat.add(Nat.sub(a, b), m), Equal.trans(Nat, Nat.add(Nat.add(b, Nat.sub(a, b)), Nat.sub(m, b)), Nat.add(b, Nat.add(Nat.sub(a, b), Nat.sub(m, b))), Nat.add(Nat.sub(a, b), Nat.add(b, Nat.sub(m, b))), Equal.sym(Nat, Nat.add(b, Nat.add(Nat.sub(a, b), Nat.sub(m, b))), Nat.add(Nat.add(b, Nat.sub(a, b)), Nat.sub(m, b)), Natural.natural_add_associative(b, Nat.sub(a, b), Nat.sub(m, b))), Product.interchange(b, Nat.sub(a, b), Nat.sub(m, b))), Equal.cong(Nat, Nat, x => Nat.add(Nat.sub(a, b), x), Nat.add(b, Nat.sub(m, b)), m, Order.add_complement(m, b, bm)))

def predecessor(x: Nat) -> Nat:
  match x:
    case 0n: 0n
    case 1n+p: p

def cancel_left(a: Nat, b: Nat, c: Nat, e: {Nat.add(a, b) == Nat.add(a, c) : Nat}) -> {b == c : Nat}:
  match a:
    case 0n: e
    case 1n+p:
      cancel_left(p, b, c, Equal.cong(Nat, Nat, predecessor, 1n+Nat.add(p, b), 1n+Nat.add(p, c), e))

# A bounded machine result and the actual carry conservation determine the
# subtraction result uniquely; no no-borrow premise is assumed.
def solve(+n: Nat, +result: Nat, +difference: Nat, carry: Bool, bounded: {Nat.is_lt(result, S.scale_binary(n, 1n)) == True{} : Bool}, equation: {Nat.add(result, S.scale_binary(n, S.bit_value(carry))) == Nat.add(difference, S.scale_binary(n, 1n)) : Nat}) -> {result == difference : Nat}:
  match carry:
    case False{}:
      e = Equal.trans(Nat, result, Nat.add(result, S.scale_binary(n, 0n)), Nat.add(difference, S.scale_binary(n, 1n)), Equal.trans(Nat, result, Nat.add(result, 0n), Nat.add(result, S.scale_binary(n, 0n)), Equal.sym(Nat, Nat.add(result, 0n), result, Order.add_zero(result)), Equal.cong(Nat, Nat, x => Nat.add(result, x), 0n, S.scale_binary(n, 0n), Equal.sym(Nat, S.scale_binary(n, 0n), 0n, Counter.scale_zero(n)))), equation)
      Empty.absurd({result == difference : Nat}, Logic.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(difference, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(difference, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), False{}, Bounds.offset_not_less(S.scale_binary(n, 1n), difference)), Equal.trans(Bool, Nat.is_lt(Nat.add(difference, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), Nat.is_lt(result, S.scale_binary(n, 1n)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, S.scale_binary(n, 1n)), Nat.add(difference, S.scale_binary(n, 1n)), result, Equal.sym(Nat, result, Nat.add(difference, S.scale_binary(n, 1n)), e)), bounded))))
    case True{}:
      cancel_left(S.scale_binary(n, 1n), result, difference, Equal.trans(Nat, Nat.add(S.scale_binary(n, 1n), result), Nat.add(result, S.scale_binary(n, 1n)), Nat.add(S.scale_binary(n, 1n), difference), Order.add_commute(S.scale_binary(n, 1n), result), Equal.trans(Nat, Nat.add(result, S.scale_binary(n, 1n)), Nat.add(difference, S.scale_binary(n, 1n)), Nat.add(S.scale_binary(n, 1n), difference), equation, Order.add_commute(difference, S.scale_binary(n, 1n)))))

# Exact interpretation of executed Base subtraction when a >= b. The proof
# derives the carry from conservation and the universal word range.
def exact(+n: Nat, +a: Word(n), +b: Word(n), enough: {Nat.is_le(S.unsigned(n, b), S.unsigned(n, a)) == True{} : Bool}) -> {S.unsigned(n, Word.sub(n, a, b)) == Nat.sub(S.unsigned(n, a), S.unsigned(n, b)) : Nat}:
  Equal.trans(Nat, S.unsigned(n, Word.sub(n, a, b)), S.unsigned(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), Nat.sub(S.unsigned(n, a), S.unsigned(n, b)), Equal.cong(Word(n), Nat, w => S.unsigned(n, w), Word.sub(n, a, b), Word.adc(n, a, Word.not(n, b), False{}, True{}), Sub.flip(n, a, b, True{})), solve(n, S.unsigned(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), Nat.sub(S.unsigned(n, a), S.unsigned(n, b)), Add.carry_out(n, a, Word.not(n, b), True{}), WB.unsigned_bound(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), Equal.trans(Nat, Nat.add(S.unsigned(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), S.scale_binary(n, S.bit_value(Add.carry_out(n, a, Word.not(n, b), True{})))), 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b))), Nat.add(Nat.sub(S.unsigned(n, a), S.unsigned(n, b)), S.scale_binary(n, 1n)), Add.adc_conservation(n, a, Word.not(n, b), True{}), Equal.trans(Nat, 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b))), Nat.add(S.unsigned(n, a), 1n+S.unsigned(n, Word.not(n, b))), Nat.add(Nat.sub(S.unsigned(n, a), S.unsigned(n, b)), S.scale_binary(n, 1n)), Equal.sym(Nat, Nat.add(S.unsigned(n, a), 1n+S.unsigned(n, Word.not(n, b))), 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b))), Index.add_right_successor(S.unsigned(n, a), S.unsigned(n, Word.not(n, b)))), Equal.trans(Nat, Nat.add(S.unsigned(n, a), 1n+S.unsigned(n, Word.not(n, b))), Nat.add(S.unsigned(n, a), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, b))), Nat.add(Nat.sub(S.unsigned(n, a), S.unsigned(n, b)), S.scale_binary(n, 1n)), Equal.cong(Nat, Nat, x => Nat.add(S.unsigned(n, a), x), 1n+S.unsigned(n, Word.not(n, b)), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, b)), Equal.sym(Nat, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, b)), 1n+S.unsigned(n, Word.not(n, b)), Neg.complement_distance(n, b))), complementary_difference(S.unsigned(n, a), S.unsigned(n, b), S.scale_binary(n, 1n), enough, Order.less_is_le(S.unsigned(n, b), S.scale_binary(n, 1n), WB.unsigned_bound(n, b))))))))

def primitive_bound(+x: Word(32n), +y: Word(32n), enough: {Nat.is_le(Word.to_nat(32n, y), Word.to_nat(32n, x)) == True{} : Bool}) -> {Nat.is_le(S.unsigned(32n, y), S.unsigned(32n, x)) == True{} : Bool}:
  %Numeric.primitive_word_interpretation(32n, x) : {Nat.is_le(S.unsigned(32n, y), _) == True{} : Bool}
  %Numeric.primitive_word_interpretation(32n, y) : {Nat.is_le(_, Word.to_nat(32n, x)) == True{} : Bool}
  enough

def u32_exact(a: U32, b: U32, enough: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) -> {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Nat, Word.to_nat(32n, Word.sub(32n, x, y)), S.unsigned(32n, Word.sub(32n, x, y)), Numeric.primitive_word_interpretation(32n, Word.sub(32n, x, y))) : {_ == Nat.sub(Word.to_nat(32n, x), Word.to_nat(32n, y)) : Nat}
      %Equal.sym(Nat, Word.to_nat(32n, x), S.unsigned(32n, x), Numeric.primitive_word_interpretation(32n, x)) : {S.unsigned(32n, Word.sub(32n, x, y)) == Nat.sub(_, Word.to_nat(32n, y)) : Nat}
      %Equal.sym(Nat, Word.to_nat(32n, y), S.unsigned(32n, y), Numeric.primitive_word_interpretation(32n, y)) : {S.unsigned(32n, Word.sub(32n, x, y)) == Nat.sub(S.unsigned(32n, x), _) : Nat}
      exact(32n, x, y, primitive_bound(x, y, enough))
