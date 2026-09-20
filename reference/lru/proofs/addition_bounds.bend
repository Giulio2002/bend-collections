import Base
import ../spec/numeric.bend as S
import ./addition.bend as Add
import ./counter.bend as Counter
import ./native_map.bend as Natural
import ./map_index.bend as Index
import ./map_routing.bend as Logic

def offset_not_less(b: Nat, +a: Nat) -> {Nat.is_lt(Nat.add(a, b), b) == False{} : Bool}:
  match b:
    case 0n:
      match a:
        case 0n: {==}
        case 1n+p: {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), Index.add_right_successor(a, p)) : {Nat.is_lt(_, 1n+p) == False{} : Bool}
      offset_not_less(p, a)

# Input range discharges the carry, rather than assuming no overflow.
def no_wrap(+n: Nat, +result: Nat, +total: Nat, carry: Bool, conservation: {Nat.add(result, S.scale_binary(n, S.bit_value(carry))) == total : Nat}, bound: {Nat.is_lt(total, S.scale_binary(n, 1n)) == True{} : Bool}) -> {result == total : Nat}:
  match carry:
    case False{}:
      Equal.trans(Nat, result, Nat.add(result, 0n), total, Equal.sym(Nat, Nat.add(result, 0n), result, Natural.natural_add_right_zero(result)), Equal.trans(Nat, Nat.add(result, 0n), Nat.add(result, S.scale_binary(n, 0n)), total, Equal.cong(Nat, Nat, x => Nat.add(result, x), 0n, S.scale_binary(n, 0n), Equal.sym(Nat, S.scale_binary(n, 0n), 0n, Counter.scale_zero(n))), conservation))
    case True{}:
      Empty.absurd({result == total : Nat}, Logic.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), False{}, offset_not_less(S.scale_binary(n, 1n), result)), Equal.trans(Bool, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n)), S.scale_binary(n, 1n)), Nat.is_lt(total, S.scale_binary(n, 1n)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, S.scale_binary(n, 1n)), Nat.add(result, S.scale_binary(n, 1n)), total, conservation), bound))))

def exact(+n: Nat, +a: Word(n), +b: Word(n), bound: {Nat.is_lt(Nat.add(S.unsigned(n, a), S.unsigned(n, b)), S.scale_binary(n, 1n)) == True{} : Bool}) -> {S.unsigned(n, Word.add(n, a, b)) == Nat.add(S.unsigned(n, a), S.unsigned(n, b)) : Nat}:
  no_wrap(n, S.unsigned(n, Word.add(n, a, b)), Nat.add(S.unsigned(n, a), S.unsigned(n, b)), Add.carry_out(n, a, b, False{}), Add.adc_conservation(n, a, b, False{}), bound)
