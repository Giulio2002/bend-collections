import Base
# Ported from reference/lru/proofs/negation_magnitude.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ./natural_products.bend as Product
import ../../../src/lru/wide.bend as W
import ../../../spec/lru_numeric.bend as S
import ./counter.bend as Counter
import ./modular_negation.bend as Neg
import ../../../reference/lru/proofs/map_difference_order.bend as Order
import ../../../reference/lru/proofs/map_routing.bend as Logic

# The increment after complement overflows precisely for a zero input.
def carry_complement(+n: Nat, word: Word(n)) -> {Counter.carry(n, Word.not(n, word)) == W.is_zero(n, word) : Bool}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          Equal.cong(Bool, Bool, c => Bool.not(bit) && c, Counter.carry(p, Word.not(p, tail)), W.is_zero(p, tail), carry_complement(p, tail))

def sign_nonzero(n: Nat, word: Word(1n+n), negative: {W.last(1n+n, word) == True{} : Bool}) -> {W.is_zero(1n+n, word) == False{} : Bool}:
  match n:
    case 0n:
      match word:
        case WCon{False{}, WNil{}}: Empty.absurd({True{} == False{} : Bool}, Logic.false_true(negative))
        case WCon{True{}, WNil{}}: {==}
    case 1n+ +p:
      match word:
        case WCon{False{}, tail}: sign_nonzero(p, tail, negative)
        case WCon{True{}, tail}: {==}

# No overflow premise is assumed: nonzero input determines the actual carry.
def magnitude(+n: Nat, +word: Word(n), nonzero: {W.is_zero(n, word) == False{} : Bool}) -> {S.unsigned(n, Word.inc(n, Word.not(n, word))) == Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)) : Nat}:
  no_carry = Equal.trans(Bool, Counter.carry(n, Word.not(n, word)), W.is_zero(n, word), False{}, carry_complement(n, word), nonzero)
  zero = Equal.trans(Nat, S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word)))), S.scale_binary(n, 0n), 0n, Equal.cong(Bool, Nat, c => S.scale_binary(n, S.bit_value(c)), Counter.carry(n, Word.not(n, word)), False{}, no_carry), Counter.scale_zero(n))
  Equal.trans(Nat, S.unsigned(n, Word.inc(n, Word.not(n, word))), Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word))))), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), Equal.trans(Nat, S.unsigned(n, Word.inc(n, Word.not(n, word))), Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), 0n), Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word))))), Equal.sym(Nat, Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), 0n), S.unsigned(n, Word.inc(n, Word.not(n, word))), Order.add_zero(S.unsigned(n, Word.inc(n, Word.not(n, word))))), Equal.cong(Nat, Nat, x => Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), x), 0n, S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word)))), Equal.sym(Nat, S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word)))), 0n, zero))), Equal.trans(Nat, Nat.add(S.unsigned(n, Word.inc(n, Word.not(n, word))), S.scale_binary(n, S.bit_value(Counter.carry(n, Word.not(n, word))))), 1n+S.unsigned(n, Word.not(n, word)), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), Counter.increment_conservation(n, Word.not(n, word)), Equal.sym(Nat, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, word)), 1n+S.unsigned(n, Word.not(n, word)), Neg.complement_distance(n, word))))

def twice(+a: Nat) -> {Nat.mul(2n, a) == Nat.double(a) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(a, 0n)), Nat.add(a, a), Nat.double(a), Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(a, 0n), a, Order.add_zero(a)), Equal.sym(Nat, Nat.double(a), Nat.add(a, a), Product.double_sum(a)))

def scale_power(n: Nat) -> {S.scale_binary(n, 1n) == Nat.pow(2n, n) : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.double(S.scale_binary(p, 1n)), Nat.double(Nat.pow(2n, p)), Nat.mul(2n, Nat.pow(2n, p)), Equal.cong(Nat, Nat, Nat.double, S.scale_binary(p, 1n), Nat.pow(2n, p), scale_power(p)), Equal.sym(Nat, Nat.mul(2n, Nat.pow(2n, p)), Nat.double(Nat.pow(2n, p)), twice(Nat.pow(2n, p))))
