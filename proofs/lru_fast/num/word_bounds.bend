import Base
# Ported from reference/lru/proofs/word_bounds.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as S

law doubled_bound:
  for a: Nat
  for bound: Nat
  for bit: Bool
  {Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(a)), Nat.double(bound)) == Nat.is_lt(a, bound) : Bool}
def doubled_bound(a, bound, bit):
  match a bound:
    case 0n 0n:
      match bit:
        case False{}:
          {==}
        case True{}:
          {==}
    case 0n 1n+p:
      match bit:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p 0n:
      match bit:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p 1n+q:
      match bit:
        case False{}:
          doubled_bound(p, q, False{})
        case True{}:
          doubled_bound(p, q, True{})

# Independent interpretation of every n-bit word lies in [0, 2^n).
law unsigned_bound:
  for +n: Nat
  for w: Word(n)
  {Nat.is_lt(S.unsigned(n, w), S.scale_binary(n, 1n)) == True{} : Bool}
def unsigned_bound(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+bit, +tail}:
          Equal.trans(Bool, Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(S.unsigned(p, tail))), Nat.double(S.scale_binary(p, 1n))), Nat.is_lt(S.unsigned(p, tail), S.scale_binary(p, 1n)), True{}, doubled_bound(S.unsigned(p, tail), S.scale_binary(p, 1n), bit), unsigned_bound(p, tail))
