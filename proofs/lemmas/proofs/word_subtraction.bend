import Base
import ./numeric.bend as Numeric
import ../spec/numeric.bend as S
import ./addition.bend as Add
import ./word_addition.bend as Addition
import ./modular_negation.bend as Negation
import ./map_index.bend as Index

def shape(+n: Nat, a: Word(n), b: Word(n), pair: Bool & Bool) -> {Word.adc.con(n, a, b, True{}, pair) == WCon{Add.sum_bit(pair), Word.adc(n, a, b, True{}, Add.carry_bit(pair))} : Word(1n+n)}:
  (sum, carry) = pair
  {==}

# The subtraction branch of existing Base.adc equals addition of complemented
# bits with the same input carry. No arithmetic algorithm is substituted.
def flip(+n: Nat, a: Word(n), b: Word(n), +carry: Bool) -> {Word.adc(n, a, b, True{}, carry) == Word.adc(n, a, Word.not(n, b), False{}, carry) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Equal.trans(Word(1n+p), Word.adc.con(p, at, bt, True{}, Bool.full_add(x, Bool.not(y), carry)), WCon{Add.sum_bit(Bool.full_add(x, Bool.not(y), carry)), Word.adc(p, at, bt, True{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry)))}, Word.adc.con(p, at, Word.not(p, bt), False{}, Bool.full_add(x, Bool.not(y), carry)), shape(p, at, bt, Bool.full_add(x, Bool.not(y), carry)), Equal.trans(Word(1n+p), WCon{Add.sum_bit(Bool.full_add(x, Bool.not(y), carry)), Word.adc(p, at, bt, True{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry)))}, WCon{Add.sum_bit(Bool.full_add(x, Bool.not(y), carry)), Word.adc(p, at, Word.not(p, bt), False{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry)))}, Word.adc.con(p, at, Word.not(p, bt), False{}, Bool.full_add(x, Bool.not(y), carry)), Equal.cong(Word(p), Word(1n+p), w => WCon{Add.sum_bit(Bool.full_add(x, Bool.not(y), carry)), w}, Word.adc(p, at, bt, True{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry))), Word.adc(p, at, Word.not(p, bt), False{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry))), flip(p, at, bt, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry)))), Equal.sym(Word(1n+p), Word.adc.con(p, at, Word.not(p, bt), False{}, Bool.full_add(x, Bool.not(y), carry)), WCon{Add.sum_bit(Bool.full_add(x, Bool.not(y), carry)), Word.adc(p, at, Word.not(p, bt), False{}, Add.carry_bit(Bool.full_add(x, Bool.not(y), carry)))}, Add.adc_shape(p, at, Word.not(p, bt), Bool.full_add(x, Bool.not(y), carry)))))

def complement_form(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.sub(n, a, b) == S.from_nat(n, 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b)))) : Word(n)}:
  Equal.trans(Word(n), Word.sub(n, a, b), Word.adc(n, a, Word.not(n, b), False{}, True{}), S.from_nat(n, 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b)))), flip(n, a, b, True{}), Addition.with_carry(n, a, Word.not(n, b), True{}))

# Exact modulo subtraction expressed using nonnegative mathematical magnitudes.
def refines(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.sub(n, a, b) == S.from_nat(n, Nat.add(S.unsigned(n, a), Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, b)))) : Word(n)}:
  %Equal.sym(Nat, Nat.sub(S.scale_binary(n, 1n), S.unsigned(n, b)), 1n+S.unsigned(n, Word.not(n, b)), Negation.complement_distance(n, b)) : {Word.sub(n, a, b) == S.from_nat(n, Nat.add(S.unsigned(n, a), _)) : Word(n)}
  %Equal.sym(Nat, Nat.add(S.unsigned(n, a), 1n+S.unsigned(n, Word.not(n, b))), 1n+Nat.add(S.unsigned(n, a), S.unsigned(n, Word.not(n, b))), Index.add_right_successor(S.unsigned(n, a), S.unsigned(n, Word.not(n, b)))) : {Word.sub(n, a, b) == S.from_nat(n, _) : Word(n)}
  complement_form(n, a, b)

# Concrete primitive used in wide.digit_result; the independent complement
# conservation above gives the equivalent nonnegative modular-subtraction form.
def u32_refines(a: U32, b: U32) -> {U32.sub(a, b) == U32{S.from_nat(32n, 1n+Nat.add(U32.to_nat(a), U32.to_nat(U32.not(b))))} : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Nat, Word.to_nat(32n, x), S.unsigned(32n, x), Numeric.primitive_word_interpretation(32n, x)) : {U32.sub(U32{x}, U32{y}) == U32{S.from_nat(32n, 1n+Nat.add(_, Word.to_nat(32n, Word.not(32n, y))))} : U32}
      %Equal.sym(Nat, Word.to_nat(32n, Word.not(32n, y)), S.unsigned(32n, Word.not(32n, y)), Numeric.primitive_word_interpretation(32n, Word.not(32n, y))) : {U32.sub(U32{x}, U32{y}) == U32{S.from_nat(32n, 1n+Nat.add(S.unsigned(32n, x), _))} : U32}
      Equal.cong(Word(32n), U32, w => U32{w}, Word.sub(32n, x, y), S.from_nat(32n, 1n+Nat.add(S.unsigned(32n, x), S.unsigned(32n, Word.not(32n, y)))), complement_form(32n, x, y))
