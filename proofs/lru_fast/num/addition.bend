import Base
# Ported from reference/lru/proofs/addition.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as S
import ../../../src/lru/wide.bend as W
import ./numeric.bend as N
import ../../../reference/lru/proofs/native_map.bend as A

# Carry is computed from input bits; it is not an assumed property of Word.add.
def sum_bit(r: Bool & Bool) -> Bool:
  (s, c) = r
  s

def carry_bit(r: Bool & Bool) -> Bool:
  (s, c) = r
  c

def carry_out(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          carry_out(p, at, bt, carry_bit(Bool.full_add(ah, bh, c)))

law bit_conservation:
  for a: Nat
  for +b: Nat
  for x: Bool
  for y: Bool
  for c: Bool
  {Nat.add(S.bit_value(sum_bit(Bool.full_add(x, y, c))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(x, y, c))), Nat.add(a, b)))) == Nat.add(S.bit_value(c), Nat.add(Nat.add(S.bit_value(x), Nat.double(a)), Nat.add(S.bit_value(y), Nat.double(b)))) : Nat}
def bit_conservation(a, b, x, y, c):
  match a:
    case 0n:
      match x y c:
        case False{} False{} False{}: {==}
        case False{} False{} True{}: {==}
        case False{} True{} False{}: {==}
        case False{} True{} True{}: {==}
        case True{} False{} False{}: {==}
        case True{} False{} True{}: {==}
        case True{} True{} False{}: {==}
        case True{} True{} True{}: {==}
    case 1n+p:
      match x y c:
        case False{} False{} False{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(False{}, False{}, False{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(False{}, False{}, False{}))), Nat.add(p, b)))), Nat.add(S.bit_value(False{}), Nat.add(Nat.add(S.bit_value(False{}), Nat.double(p)), Nat.add(S.bit_value(False{}), Nat.double(b)))), bit_conservation(p, b, False{}, False{}, False{}))
        case False{} False{} True{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(False{}, False{}, True{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(False{}, False{}, True{}))), Nat.add(p, b)))), Nat.add(S.bit_value(True{}), Nat.add(Nat.add(S.bit_value(False{}), Nat.double(p)), Nat.add(S.bit_value(False{}), Nat.double(b)))), bit_conservation(p, b, False{}, False{}, True{}))
        case False{} True{} False{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(False{}, True{}, False{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(False{}, True{}, False{}))), Nat.add(p, b)))), Nat.add(S.bit_value(False{}), Nat.add(Nat.add(S.bit_value(False{}), Nat.double(p)), Nat.add(S.bit_value(True{}), Nat.double(b)))), bit_conservation(p, b, False{}, True{}, False{}))
        case False{} True{} True{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(False{}, True{}, True{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(False{}, True{}, True{}))), Nat.add(p, b)))), Nat.add(S.bit_value(True{}), Nat.add(Nat.add(S.bit_value(False{}), Nat.double(p)), Nat.add(S.bit_value(True{}), Nat.double(b)))), bit_conservation(p, b, False{}, True{}, True{}))
        case True{} False{} False{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(True{}, False{}, False{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(True{}, False{}, False{}))), Nat.add(p, b)))), Nat.add(S.bit_value(False{}), Nat.add(Nat.add(S.bit_value(True{}), Nat.double(p)), Nat.add(S.bit_value(False{}), Nat.double(b)))), bit_conservation(p, b, True{}, False{}, False{}))
        case True{} False{} True{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(True{}, False{}, True{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(True{}, False{}, True{}))), Nat.add(p, b)))), Nat.add(S.bit_value(True{}), Nat.add(Nat.add(S.bit_value(True{}), Nat.double(p)), Nat.add(S.bit_value(False{}), Nat.double(b)))), bit_conservation(p, b, True{}, False{}, True{}))
        case True{} True{} False{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(True{}, True{}, False{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(True{}, True{}, False{}))), Nat.add(p, b)))), Nat.add(S.bit_value(False{}), Nat.add(Nat.add(S.bit_value(True{}), Nat.double(p)), Nat.add(S.bit_value(True{}), Nat.double(b)))), bit_conservation(p, b, True{}, True{}, False{}))
        case True{} True{} True{}:
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(S.bit_value(sum_bit(Bool.full_add(True{}, True{}, True{}))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(True{}, True{}, True{}))), Nat.add(p, b)))), Nat.add(S.bit_value(True{}), Nat.add(Nat.add(S.bit_value(True{}), Nat.double(p)), Nat.add(S.bit_value(True{}), Nat.double(b)))), bit_conservation(p, b, True{}, True{}, True{}))

law lift_conservation:
  for +bit: Bool
  for +value: Nat
  for +carry: Nat
  for +total: Nat
  for e: {Nat.add(value, carry) == total : Nat}
  {Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(carry)) == Nat.add(S.bit_value(bit), Nat.double(total)) : Nat}
def lift_conservation(bit, value, carry, total, e):
  Equal.trans(Nat, Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(carry)), Nat.add(S.bit_value(bit), Nat.add(Nat.double(value), Nat.double(carry))), Nat.add(S.bit_value(bit), Nat.double(total)), Equal.sym(Nat, Nat.add(S.bit_value(bit), Nat.add(Nat.double(value), Nat.double(carry))), Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(carry)), A.natural_add_associative(S.bit_value(bit), Nat.double(value), Nat.double(carry))), Equal.cong(Nat, Nat, z => Nat.add(S.bit_value(bit), z), Nat.add(Nat.double(value), Nat.double(carry)), Nat.double(total), Equal.trans(Nat, Nat.add(Nat.double(value), Nat.double(carry)), Nat.double(Nat.add(value, carry)), Nat.double(total), Equal.sym(Nat, Nat.double(Nat.add(value, carry)), Nat.add(Nat.double(value), Nat.double(carry)), N.double_add(value, carry)), Equal.cong(Nat, Nat, Nat.double, Nat.add(value, carry), total, e))))

law adc_shape:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for pair: Bool & Bool
  {Word.adc.con(n, a, b, False{}, pair) == WCon{sum_bit(pair), Word.adc(n, a, b, False{}, carry_bit(pair))} : Word(1n+n)}
def adc_shape(n, a, b, pair):
  match pair:
    case Tuple{s, c}:
      {==}

law step:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +x: Bool
  for +y: Bool
  for +c: Bool
  for e: {Nat.add(S.unsigned(n, Word.adc(n, a, b, False{}, carry_bit(Bool.full_add(x, y, c)))), S.scale_binary(n, S.bit_value(carry_out(n, a, b, carry_bit(Bool.full_add(x, y, c)))))) == Nat.add(S.bit_value(carry_bit(Bool.full_add(x, y, c))), Nat.add(S.unsigned(n, a), S.unsigned(n, b))) : Nat}
  {Nat.add(S.unsigned(1n+n, Word.adc(1n+n, WCon{x, a}, WCon{y, b}, False{}, c)), S.scale_binary(1n+n, S.bit_value(carry_out(1n+n, WCon{x, a}, WCon{y, b}, c)))) == Nat.add(S.bit_value(c), Nat.add(S.unsigned(1n+n, WCon{x, a}), S.unsigned(1n+n, WCon{y, b}))) : Nat}
def step(n, a, b, x, y, c, e):
  %Equal.sym(Word(1n+n), Word.adc.con(n, a, b, False{}, Bool.full_add(x, y, c)), WCon{sum_bit(Bool.full_add(x, y, c)), Word.adc(n, a, b, False{}, carry_bit(Bool.full_add(x, y, c)))}, adc_shape(n, a, b, Bool.full_add(x, y, c))) : {Nat.add(S.unsigned(1n+n, _), S.scale_binary(1n+n, S.bit_value(carry_out(1n+n, WCon{x, a}, WCon{y, b}, c)))) == Nat.add(S.bit_value(c), Nat.add(S.unsigned(1n+n, WCon{x, a}), S.unsigned(1n+n, WCon{y, b}))) : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(S.bit_value(sum_bit(Bool.full_add(x, y, c))), Nat.double(S.unsigned(n, Word.adc(n, a, b, False{}, carry_bit(Bool.full_add(x, y, c)))))), Nat.double(S.scale_binary(n, S.bit_value(carry_out(n, a, b, carry_bit(Bool.full_add(x, y, c))))))), Nat.add(S.bit_value(sum_bit(Bool.full_add(x, y, c))), Nat.double(Nat.add(S.bit_value(carry_bit(Bool.full_add(x, y, c))), Nat.add(S.unsigned(n, a), S.unsigned(n, b))))), Nat.add(S.bit_value(c), Nat.add(S.unsigned(1n+n, WCon{x, a}), S.unsigned(1n+n, WCon{y, b}))), lift_conservation(sum_bit(Bool.full_add(x, y, c)), S.unsigned(n, Word.adc(n, a, b, False{}, carry_bit(Bool.full_add(x, y, c)))), S.scale_binary(n, S.bit_value(carry_out(n, a, b, carry_bit(Bool.full_add(x, y, c))))), Nat.add(S.bit_value(carry_bit(Bool.full_add(x, y, c))), Nat.add(S.unsigned(n, a), S.unsigned(n, b))), e), bit_conservation(S.unsigned(n, a), S.unsigned(n, b), x, y, c))

law adc_conservation:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +c: Bool
  {Nat.add(S.unsigned(n, Word.adc(n, a, b, False{}, c)), S.scale_binary(n, S.bit_value(carry_out(n, a, b, c)))) == Nat.add(S.bit_value(c), Nat.add(S.unsigned(n, a), S.unsigned(n, b))) : Nat}
def adc_conservation(n, a, b, c):
  match n:
    case 0n:
      Equal.sym(Nat, Nat.add(S.bit_value(c), 0n), S.bit_value(c), A.natural_add_right_zero(S.bit_value(c)))
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          step(p, at, bt, x, y, c, adc_conservation(p, at, bt, carry_bit(Bool.full_add(x, y, c))))

# A full-width arithmetic law linked to the actual cache deadline adder.
# Range/modulo uniqueness and signed division are separate remaining obligations.
law addition_conservation:
  for +a: Word(64n)
  for +b: Word(64n)
  {Nat.add(S.unsigned(64n, W.add(a, b)), S.scale_binary(64n, S.bit_value(carry_out(64n, a, b, False{})))) == Nat.add(S.unsigned(64n, a), S.unsigned(64n, b)) : Nat}
def addition_conservation(a, b):
  adc_conservation(64n, a, b, False{})
