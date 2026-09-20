import Base
import ./map_difference_order.bend as Order
import ../spec/numeric.bend as S
import ./addition.bend as Add
import ./word_shift.bend as Shift
import ./natural_products.bend as P
import ./modular_addition.bend as M
import ./counter.bend as Counter
import ./native_map.bend as Natural
import ./numeric.bend as Numeric

# Overflow is calculated from input bits and the existing primitive carries.
def excess(+n: Nat, m: Nat, a: Word(m), +b: Word(n), +acc: Word(n)) -> Nat:
  match m:
    case 0n: 0n
    case 1n+ +p:
      match a:
        case WCon{False{}, +tail}:
          Nat.add(excess(n, p, tail, Word.shl(n, b), acc), Nat.mul(S.unsigned(p, tail), S.bit_value(Shift.carry(n, False{}, b))))
        case WCon{True{}, +tail}:
          Nat.add(Nat.add(excess(n, p, tail, Word.shl(n, b), Word.add(n, acc, b)), Nat.mul(S.unsigned(p, tail), S.bit_value(Shift.carry(n, False{}, b)))), S.bit_value(Add.carry_out(n, acc, b, False{})))

def restore_shift(+n: Nat, +result: Nat, +overflow: Nat, +tail: Nat, +carry: Nat, +acc: Nat, +shifted: Nat, +b: Nat, prior: {Nat.add(result, S.scale_binary(n, overflow)) == Nat.add(acc, Nat.mul(tail, shifted)) : Nat}, shift: {Nat.add(shifted, S.scale_binary(n, carry)) == Nat.double(b) : Nat}) -> {Nat.add(result, S.scale_binary(n, Nat.add(overflow, Nat.mul(tail, carry)))) == Nat.add(acc, Nat.mul(Nat.double(tail), b)) : Nat}:
  Equal.trans(Nat, Nat.add(result, S.scale_binary(n, Nat.add(overflow, Nat.mul(tail, carry)))), Nat.add(result, Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, Nat.mul(tail, carry)))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(result, x), S.scale_binary(n, Nat.add(overflow, Nat.mul(tail, carry))), Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, Nat.mul(tail, carry))), P.scale_sum(n, overflow, Nat.mul(tail, carry))), Equal.trans(Nat, Nat.add(result, Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, Nat.mul(tail, carry)))), Nat.add(Nat.add(result, S.scale_binary(n, overflow)), S.scale_binary(n, Nat.mul(tail, carry))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Natural.natural_add_associative(result, S.scale_binary(n, overflow), S.scale_binary(n, Nat.mul(tail, carry))), Equal.trans(Nat, Nat.add(Nat.add(result, S.scale_binary(n, overflow)), S.scale_binary(n, Nat.mul(tail, carry))), Nat.add(Nat.add(acc, Nat.mul(tail, shifted)), S.scale_binary(n, Nat.mul(tail, carry))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(x, S.scale_binary(n, Nat.mul(tail, carry))), Nat.add(result, S.scale_binary(n, overflow)), Nat.add(acc, Nat.mul(tail, shifted)), prior), Equal.trans(Nat, Nat.add(Nat.add(acc, Nat.mul(tail, shifted)), S.scale_binary(n, Nat.mul(tail, carry))), Nat.add(acc, Nat.add(Nat.mul(tail, shifted), S.scale_binary(n, Nat.mul(tail, carry)))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.sym(Nat, Nat.add(acc, Nat.add(Nat.mul(tail, shifted), S.scale_binary(n, Nat.mul(tail, carry)))), Nat.add(Nat.add(acc, Nat.mul(tail, shifted)), S.scale_binary(n, Nat.mul(tail, carry))), Natural.natural_add_associative(acc, Nat.mul(tail, shifted), S.scale_binary(n, Nat.mul(tail, carry)))), Equal.trans(Nat, Nat.add(acc, Nat.add(Nat.mul(tail, shifted), S.scale_binary(n, Nat.mul(tail, carry)))), Nat.add(acc, Nat.add(Nat.mul(tail, shifted), Nat.mul(tail, S.scale_binary(n, carry)))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(acc, Nat.add(Nat.mul(tail, shifted), x)), S.scale_binary(n, Nat.mul(tail, carry)), Nat.mul(tail, S.scale_binary(n, carry)), P.scale_product(n, tail, carry)), Equal.trans(Nat, Nat.add(acc, Nat.add(Nat.mul(tail, shifted), Nat.mul(tail, S.scale_binary(n, carry)))), Nat.add(acc, Nat.mul(tail, Nat.add(shifted, S.scale_binary(n, carry)))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(acc, x), Nat.add(Nat.mul(tail, shifted), Nat.mul(tail, S.scale_binary(n, carry))), Nat.mul(tail, Nat.add(shifted, S.scale_binary(n, carry))), Equal.sym(Nat, Nat.mul(tail, Nat.add(shifted, S.scale_binary(n, carry))), Nat.add(Nat.mul(tail, shifted), Nat.mul(tail, S.scale_binary(n, carry))), P.distribute(tail, shifted, S.scale_binary(n, carry)))), Equal.trans(Nat, Nat.add(acc, Nat.mul(tail, Nat.add(shifted, S.scale_binary(n, carry)))), Nat.add(acc, Nat.mul(tail, Nat.double(b))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(acc, Nat.mul(tail, x)), Nat.add(shifted, S.scale_binary(n, carry)), Nat.double(b), shift), Equal.trans(Nat, Nat.add(acc, Nat.mul(tail, Nat.double(b))), Nat.add(acc, Nat.double(Nat.mul(tail, b))), Nat.add(acc, Nat.mul(Nat.double(tail), b)), Equal.cong(Nat, Nat, x => Nat.add(acc, x), Nat.mul(tail, Nat.double(b)), Nat.double(Nat.mul(tail, b)), P.multiply_double(tail, b)), Equal.cong(Nat, Nat, x => Nat.add(acc, x), Nat.double(Nat.mul(tail, b)), Nat.mul(Nat.double(tail), b), Equal.sym(Nat, Nat.mul(Nat.double(tail), b), Nat.double(Nat.mul(tail, b)), P.double_product(tail, b)))))))))))

def swap_last(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b), Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Natural.natural_add_associative(a, b, c)), Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, c), Nat.add(c, b), Order.add_commute(b, c)), Natural.natural_add_associative(a, c, b)))

def restore_addition(+n: Nat, +result: Nat, +overflow: Nat, +carry: Nat, +next: Nat, +product: Nat, +acc: Nat, +b: Nat, prior: {Nat.add(result, S.scale_binary(n, overflow)) == Nat.add(next, product) : Nat}, addition: {Nat.add(next, S.scale_binary(n, carry)) == Nat.add(acc, b) : Nat}) -> {Nat.add(result, S.scale_binary(n, Nat.add(overflow, carry))) == Nat.add(acc, Nat.add(b, product)) : Nat}:
  Equal.trans(Nat, Nat.add(result, S.scale_binary(n, Nat.add(overflow, carry))), Nat.add(result, Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, carry))), Nat.add(acc, Nat.add(b, product)), Equal.cong(Nat, Nat, x => Nat.add(result, x), S.scale_binary(n, Nat.add(overflow, carry)), Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, carry)), P.scale_sum(n, overflow, carry)), Equal.trans(Nat, Nat.add(result, Nat.add(S.scale_binary(n, overflow), S.scale_binary(n, carry))), Nat.add(Nat.add(result, S.scale_binary(n, overflow)), S.scale_binary(n, carry)), Nat.add(acc, Nat.add(b, product)), Natural.natural_add_associative(result, S.scale_binary(n, overflow), S.scale_binary(n, carry)), Equal.trans(Nat, Nat.add(Nat.add(result, S.scale_binary(n, overflow)), S.scale_binary(n, carry)), Nat.add(Nat.add(next, product), S.scale_binary(n, carry)), Nat.add(acc, Nat.add(b, product)), Equal.cong(Nat, Nat, x => Nat.add(x, S.scale_binary(n, carry)), Nat.add(result, S.scale_binary(n, overflow)), Nat.add(next, product), prior), Equal.trans(Nat, Nat.add(Nat.add(next, product), S.scale_binary(n, carry)), Nat.add(Nat.add(next, S.scale_binary(n, carry)), product), Nat.add(acc, Nat.add(b, product)), swap_last(next, product, S.scale_binary(n, carry)), Equal.trans(Nat, Nat.add(Nat.add(next, S.scale_binary(n, carry)), product), Nat.add(Nat.add(acc, b), product), Nat.add(acc, Nat.add(b, product)), Equal.cong(Nat, Nat, x => Nat.add(x, product), Nat.add(next, S.scale_binary(n, carry)), Nat.add(acc, b), addition), Equal.sym(Nat, Nat.add(acc, Nat.add(b, product)), Nat.add(Nat.add(acc, b), product), Natural.natural_add_associative(acc, b, product)))))))

# Induction follows the actual multiplier's bit loop and restores every carry.
def conservation(+n: Nat, m: Nat, a: Word(m), +b: Word(n), +acc: Word(n)) -> {Nat.add(S.unsigned(n, Word.mul.go(n, m, a, b, acc)), S.scale_binary(n, excess(n, m, a, b, acc))) == Nat.add(S.unsigned(n, acc), Nat.mul(S.unsigned(m, a), S.unsigned(n, b))) : Nat}:
  match m:
    case 0n:
      match a:
        case WNil{}:
          Equal.cong(Nat, Nat, x => Nat.add(S.unsigned(n, acc), x), S.scale_binary(n, 0n), 0n, Counter.scale_zero(n))
    case 1n+ +p:
      match a:
        case WCon{False{}, +tail}:
          restore_shift(n, S.unsigned(n, Word.mul.go(n, p, tail, Word.shl(n, b), acc)), excess(n, p, tail, Word.shl(n, b), acc), S.unsigned(p, tail), S.bit_value(Shift.carry(n, False{}, b)), S.unsigned(n, acc), S.unsigned(n, Word.shl(n, b)), S.unsigned(n, b), conservation(n, p, tail, Word.shl(n, b), acc), Shift.shift_conservation(n, b))
        case WCon{True{}, +tail}:
          restore_addition(n, S.unsigned(n, Word.mul.go(n, p, tail, Word.shl(n, b), Word.add(n, acc, b))), Nat.add(excess(n, p, tail, Word.shl(n, b), Word.add(n, acc, b)), Nat.mul(S.unsigned(p, tail), S.bit_value(Shift.carry(n, False{}, b)))), S.bit_value(Add.carry_out(n, acc, b, False{})), S.unsigned(n, Word.add(n, acc, b)), Nat.mul(Nat.double(S.unsigned(p, tail)), S.unsigned(n, b)), S.unsigned(n, acc), S.unsigned(n, b), restore_shift(n, S.unsigned(n, Word.mul.go(n, p, tail, Word.shl(n, b), Word.add(n, acc, b))), excess(n, p, tail, Word.shl(n, b), Word.add(n, acc, b)), S.unsigned(p, tail), S.bit_value(Shift.carry(n, False{}, b)), S.unsigned(n, Word.add(n, acc, b)), S.unsigned(n, Word.shl(n, b)), S.unsigned(n, b), conservation(n, p, tail, Word.shl(n, b), Word.add(n, acc, b)), Shift.shift_conservation(n, b)), Add.adc_conservation(n, acc, b, False{}))

def go_refines(+n: Nat, +m: Nat, +a: Word(m), +b: Word(n), +acc: Word(n)) -> {Word.mul.go(n, m, a, b, acc) == S.from_nat(n, Nat.add(S.unsigned(n, acc), Nat.mul(S.unsigned(m, a), S.unsigned(n, b)))) : Word(n)}:
  %conservation(n, m, a, b, acc) : {Word.mul.go(n, m, a, b, acc) == S.from_nat(n, _) : Word(n)}
  Equal.sym(Word(n), S.from_nat(n, Nat.add(S.unsigned(n, Word.mul.go(n, m, a, b, acc)), S.scale_binary(n, excess(n, m, a, b, acc)))), Word.mul.go(n, m, a, b, acc), M.reconstruct(n, Word.mul.go(n, m, a, b, acc), excess(n, m, a, b, acc)))

def zero_unsigned(n: Nat) -> {S.unsigned(n, Word.zero(n)) == 0n : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, Nat.double, S.unsigned(p, Word.zero(p)), 0n, zero_unsigned(p))

def refines(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.mul(n, a, b) == S.from_nat(n, Nat.mul(S.unsigned(n, a), S.unsigned(n, b))) : Word(n)}:
  Equal.trans(Word(n), Word.mul(n, a, b), S.from_nat(n, Nat.add(S.unsigned(n, Word.zero(n)), Nat.mul(S.unsigned(n, a), S.unsigned(n, b)))), S.from_nat(n, Nat.mul(S.unsigned(n, a), S.unsigned(n, b))), go_refines(n, n, a, b, Word.zero(n)), Equal.cong(Nat, Word(n), x => S.from_nat(n, Nat.add(x, Nat.mul(S.unsigned(n, a), S.unsigned(n, b)))), S.unsigned(n, Word.zero(n)), 0n, zero_unsigned(n)))

def u32_refines(a: U32, b: U32) -> {U32.mul(a, b) == U32{S.from_nat(32n, Nat.mul(U32.to_nat(a), U32.to_nat(b)))} : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Nat, Word.to_nat(32n, x), S.unsigned(32n, x), Numeric.primitive_word_interpretation(32n, x)) : {U32.mul(U32{x}, U32{y}) == U32{S.from_nat(32n, Nat.mul(_, Word.to_nat(32n, y)))} : U32}
      %Equal.sym(Nat, Word.to_nat(32n, y), S.unsigned(32n, y), Numeric.primitive_word_interpretation(32n, y)) : {U32.mul(U32{x}, U32{y}) == U32{S.from_nat(32n, Nat.mul(S.unsigned(32n, x), _))} : U32}
      Equal.cong(Word(32n), U32, w => U32{w}, Word.mul(32n, x, y), S.from_nat(32n, Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y))), refines(32n, x, y))
