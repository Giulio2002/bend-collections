import Base
import ../spec/numeric.bend as S
import ./word_multiplication.bend as Mul
import ./natural_products.bend as P
import ./addition_bounds.bend as Bounds
import ./counter.bend as Counter
import ./native_map.bend as Natural
import ./map_routing.bend as Logic

# Every positive multiple of the modulus is at least one modulus, even after
# adding a nonnegative output. This discharges arbitrary multiplication overflow.
def positive_excess(+n: Nat, +result: Nat, +extra: Nat) -> {Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n+extra)), S.scale_binary(n, 1n)) == False{} : Bool}:
  %Equal.sym(Nat, S.scale_binary(n, 1n+extra), Nat.add(S.scale_binary(n, 1n), S.scale_binary(n, extra)), P.scale_sum(n, 1n, extra)) : {Nat.is_lt(Nat.add(result, _), S.scale_binary(n, 1n)) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(result, Nat.add(S.scale_binary(n, 1n), S.scale_binary(n, extra))), Nat.add(Nat.add(result, S.scale_binary(n, 1n)), S.scale_binary(n, extra)), Natural.natural_add_associative(result, S.scale_binary(n, 1n), S.scale_binary(n, extra))) : {Nat.is_lt(_, S.scale_binary(n, 1n)) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(result, S.scale_binary(n, 1n)), S.scale_binary(n, extra)), Nat.add(Nat.add(result, S.scale_binary(n, extra)), S.scale_binary(n, 1n)), Mul.swap_last(result, S.scale_binary(n, 1n), S.scale_binary(n, extra))) : {Nat.is_lt(_, S.scale_binary(n, 1n)) == False{} : Bool}
  Bounds.offset_not_less(S.scale_binary(n, 1n), Nat.add(result, S.scale_binary(n, extra)))

def no_wrap(+n: Nat, +result: Nat, +total: Nat, excess: Nat, conservation: {Nat.add(result, S.scale_binary(n, excess)) == total : Nat}, bound: {Nat.is_lt(total, S.scale_binary(n, 1n)) == True{} : Bool}) -> {result == total : Nat}:
  match excess:
    case 0n:
      Bounds.no_wrap(n, result, total, False{}, conservation, bound)
    case 1n+ +p:
      Empty.absurd({result == total : Nat}, Logic.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n+p)), S.scale_binary(n, 1n)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n+p)), S.scale_binary(n, 1n)), False{}, positive_excess(n, result, p)), Equal.trans(Bool, Nat.is_lt(Nat.add(result, S.scale_binary(n, 1n+p)), S.scale_binary(n, 1n)), Nat.is_lt(total, S.scale_binary(n, 1n)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, S.scale_binary(n, 1n)), Nat.add(result, S.scale_binary(n, 1n+p)), total, conservation), bound))))

def exact(+n: Nat, +a: Word(n), +b: Word(n), bound: {Nat.is_lt(Nat.mul(S.unsigned(n, a), S.unsigned(n, b)), S.scale_binary(n, 1n)) == True{} : Bool}) -> {S.unsigned(n, Word.mul(n, a, b)) == Nat.mul(S.unsigned(n, a), S.unsigned(n, b)) : Nat}:
  no_wrap(n, S.unsigned(n, Word.mul(n, a, b)), Nat.mul(S.unsigned(n, a), S.unsigned(n, b)), Mul.excess(n, n, a, b, Word.zero(n)), %Mul.zero_unsigned(n) : {Nat.add(S.unsigned(n, Word.mul(n, a, b)), S.scale_binary(n, Mul.excess(n, n, a, b, Word.zero(n)))) == Nat.add(_, Nat.mul(S.unsigned(n, a), S.unsigned(n, b))) : Nat} Mul.conservation(n, n, a, b, Word.zero(n)), bound)
