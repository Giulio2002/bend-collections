import Base
import ./native_map.bend as Natural
import ./numeric.bend as Numeric
import ../spec/numeric.bend as S
import ../src/wide.bend as W

# Carry out is mathematical all-bits-set, not an assumed increment result.
def carry(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, tail}:
          b && carry(p, tail)

law scale_zero:
  for n: Nat
  {S.scale_binary(n, 0n) == 0n : Nat}
def scale_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, S.scale_binary(p, 0n), 0n, scale_zero(p))

# Exact integer conservation for the installed ripple increment at every width:
# result + (carry-out * 2^width) = input + 1. This includes width zero and proves
# all bit patterns, rather than testing only the maximum-word rollover example.
law increment_conservation:
  for +n: Nat
  for w: Word(n)
  {Nat.add(S.unsigned(n, Word.inc(n, w)), S.scale_binary(n, S.bit_value(carry(n, w)))) == 1n+S.unsigned(n, w) : Nat}
def increment_conservation(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +tail}:
          %Equal.sym(Nat, S.scale_binary(p, 0n), 0n, scale_zero(p)) : {Nat.add(1n+Nat.double(S.unsigned(p, tail)), Nat.double(_)) == 1n+Nat.double(S.unsigned(p, tail)) : Nat}
          Natural.natural_add_right_zero(1n+Nat.double(S.unsigned(p, tail)))
        case WCon{True{}, +tail}:
          Equal.trans(Nat, Nat.add(Nat.double(S.unsigned(p, Word.inc(p, tail))), Nat.double(S.scale_binary(p, S.bit_value(carry(p, tail))))), Nat.double(Nat.add(S.unsigned(p, Word.inc(p, tail)), S.scale_binary(p, S.bit_value(carry(p, tail))))), 2n+Nat.double(S.unsigned(p, tail)), Equal.sym(Nat, Nat.double(Nat.add(S.unsigned(p, Word.inc(p, tail)), S.scale_binary(p, S.bit_value(carry(p, tail))))), Nat.add(Nat.double(S.unsigned(p, Word.inc(p, tail))), Nat.double(S.scale_binary(p, S.bit_value(carry(p, tail))))), Numeric.double_add(S.unsigned(p, Word.inc(p, tail)), S.scale_binary(p, S.bit_value(carry(p, tail))))), Equal.cong(Nat, Nat, Nat.double, Nat.add(S.unsigned(p, Word.inc(p, tail)), S.scale_binary(p, S.bit_value(carry(p, tail)))), 1n+S.unsigned(p, tail), increment_conservation(p, tail)))

law counter_conservation:
  for +w: Word(64n)
  {Nat.add(S.unsigned(64n, W.inc(w)), S.scale_binary(64n, S.bit_value(carry(64n, w)))) == 1n+S.unsigned(64n, w) : Nat}
def counter_conservation(w):
  increment_conservation(64n, w)
