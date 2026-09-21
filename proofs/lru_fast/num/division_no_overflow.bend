import Base
# Ported from reference/lru/proofs/division_no_overflow.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../src/lru/wide.bend as W
import ../../../spec/lru_numeric.bend as S
import ./word_shift.bend as Shift
import ./division_shift.bend as Digit
import ../../../reference/lru/proofs/map_routing.bend as Logic
import ./counter.bend as Counter
import ./numeric.bend as Numeric
import ../../../reference/lru/proofs/map_difference_order.bend as Order

# Higher-bit comparison cannot be greater if the complete comparison is <=.
def higher_le(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_le(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: e

def high_monotone(n: Nat, a: Word(1n+n), b: Word(1n+n), low: {W.last(1n+n, b) == False{} : Bool}, le: {Cmp.is_le(Word.cmp(1n+n, a, b)) == True{} : Bool}) -> {W.last(1n+n, a) == False{} : Bool}:
  match n:
    case 0n:
      match a b:
        case WCon{False{}, WNil{}} WCon{False{}, WNil{}}: {==}
        case WCon{False{}, WNil{}} WCon{True{}, WNil{}}: {==}
        case WCon{True{}, WNil{}} WCon{False{}, WNil{}}: Empty.absurd({True{} == False{} : Bool}, Logic.false_true(le))
        case WCon{True{}, WNil{}} WCon{True{}, WNil{}}: low
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          high_monotone(p, at, bt, low, higher_le(Word.cmp(1n+p, at, bt), x, y, le))

def discarded(n: Nat, input: Bool, w: Word(1n+n)) -> {Shift.carry(1n+n, input, w) == W.last(1n+n, w) : Bool}:
  match n:
    case 0n:
      match w:
        case WCon{b, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{b, tail}: discarded(p, b, tail)

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

# The concrete divisor is handled as a native 32-bit word, avoiding expansion
# of a million unary constructors. This establishes absence of carry from the
# actual U32 comparison premise, not an assumed resource/range conclusion.
def bounded_carry(+w: Word(32n), +bit: Bool, le: {U32.is_le(U32{w}, 1000000) == True{} : Bool}) -> {Shift.carry(32n, bit, w) == False{} : Bool}:
  Equal.trans(Bool, Shift.carry(32n, bit, w), W.last(32n, w), False{}, discarded(31n, bit, w), high_monotone(31n, w, bits(1000000), {==}, le))

def exact_without_carry(+n: Nat, +w: Word(n), +bit: Bool, no_carry: {Shift.carry(n, bit, w) == False{} : Bool}) -> {S.unsigned(n, Word.shl.put(n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(S.unsigned(n, w))) : Nat}:
  e = Shift.conservation(n, bit, w)
  z = Equal.trans(Nat, S.scale_binary(n, S.bit_value(Shift.carry(n, bit, w))), S.scale_binary(n, 0n), 0n, Equal.cong(Bool, Nat, c => S.scale_binary(n, S.bit_value(c)), Shift.carry(n, bit, w), False{}, no_carry), Counter.scale_zero(n))
  Equal.trans(Nat, S.unsigned(n, Word.shl.put(n, bit, w)), Nat.add(S.unsigned(n, Word.shl.put(n, bit, w)), S.scale_binary(n, S.bit_value(Shift.carry(n, bit, w)))), Nat.add(S.bit_value(bit), Nat.double(S.unsigned(n, w))), Equal.trans(Nat, S.unsigned(n, Word.shl.put(n, bit, w)), Nat.add(S.unsigned(n, Word.shl.put(n, bit, w)), 0n), Nat.add(S.unsigned(n, Word.shl.put(n, bit, w)), S.scale_binary(n, S.bit_value(Shift.carry(n, bit, w)))), Equal.sym(Nat, Nat.add(S.unsigned(n, Word.shl.put(n, bit, w)), 0n), S.unsigned(n, Word.shl.put(n, bit, w)), Order.add_zero(S.unsigned(n, Word.shl.put(n, bit, w)))), Equal.cong(Nat, Nat, x => Nat.add(S.unsigned(n, Word.shl.put(n, bit, w)), x), 0n, S.scale_binary(n, S.bit_value(Shift.carry(n, bit, w))), Equal.sym(Nat, S.scale_binary(n, S.bit_value(Shift.carry(n, bit, w))), 0n, z))), e)

def decoded_candidate(+w: Word(32n), +bit: Bool, le: {U32.is_le(U32{w}, 1000000) == True{} : Bool}) -> {Word.to_nat(32n, Word.shl.put(32n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))) : Nat}:
  %Equal.sym(Nat, Word.to_nat(32n, Word.shl.put(32n, bit, w)), S.unsigned(32n, Word.shl.put(32n, bit, w)), Numeric.primitive_word_interpretation(32n, Word.shl.put(32n, bit, w))) : {_ == Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))) : Nat}
  %Equal.sym(Nat, Word.to_nat(32n, w), S.unsigned(32n, w), Numeric.primitive_word_interpretation(32n, w)) : {S.unsigned(32n, Word.shl.put(32n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(_)) : Nat}
  exact_without_carry(32n, w, bit, bounded_carry(w, bit, le))

def candidate_value(+r: U32, +bit: Bool, le: {U32.is_le(r, 1000000) == True{} : Bool}) -> {U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))) == Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))) : Nat}:
  match r:
    case U32{+w}:
      Equal.trans(Nat, U32.to_nat(U32.add(U32.mul(U32{w}, 2), W.bit_u32(bit))), Word.to_nat(32n, Word.shl.put(32n, bit, w)), Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))), Equal.cong(U32, Nat, U32.to_nat, U32.add(U32.mul(U32{w}, 2), W.bit_u32(bit)), Digit.shifted(U32{w}, bit), Digit.actual_candidate(U32{w}, bit)), decoded_candidate(w, bit, le))

def decoded_high(+w: Word(32n), +bit: Bool, high: {W.last(32n, w) == False{} : Bool}) -> {Word.to_nat(32n, Word.shl.put(32n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))) : Nat}:
  %Equal.sym(Nat, Word.to_nat(32n, Word.shl.put(32n, bit, w)), S.unsigned(32n, Word.shl.put(32n, bit, w)), Numeric.primitive_word_interpretation(32n, Word.shl.put(32n, bit, w))) : {_ == Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))) : Nat}
  %Equal.sym(Nat, Word.to_nat(32n, w), S.unsigned(32n, w), Numeric.primitive_word_interpretation(32n, w)) : {S.unsigned(32n, Word.shl.put(32n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(_)) : Nat}
  exact_without_carry(32n, w, bit, Equal.trans(Bool, Shift.carry(32n, bit, w), W.last(32n, w), False{}, discarded(31n, bit, w), high))

def double_value(d: U32, high: {W.last(32n, bits(d)) == False{} : Bool}) -> {U32.to_nat(U32.shl(d)) == Nat.double(U32.to_nat(d)) : Nat}:
  match d:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.shl(32n, w), Word.shl.put(32n, False{}, w), Shift.same_as_put(32n, w)) : {Word.to_nat(32n, _) == Nat.double(Word.to_nat(32n, w)) : Nat}
      decoded_high(w, False{}, high)

def high_candidate(+r: U32, +bit: Bool, high: {W.last(32n, bits(r)) == False{} : Bool}) -> {U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))) == Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))) : Nat}:
  match r:
    case U32{+w}:
      Equal.trans(Nat, U32.to_nat(U32.add(U32.mul(U32{w}, 2), W.bit_u32(bit))), Word.to_nat(32n, Word.shl.put(32n, bit, w)), Nat.add(S.bit_value(bit), Nat.double(Word.to_nat(32n, w))), Equal.cong(U32, Nat, U32.to_nat, U32.add(U32.mul(U32{w}, 2), W.bit_u32(bit)), Digit.shifted(U32{w}, bit), Digit.actual_candidate(U32{w}, bit)), decoded_high(w, bit, high))
