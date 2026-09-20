import Base
import ./map_routing.bend as Logic
import ./native_map.bend as N

# Existing Base.divmod quotient translation; no replacement division algorithm.
def next_quotient(pair: Nat & Nat) -> Nat & Nat:
  (q, r) = pair
  (1n+q, r)

law quotient_translation:
  for n: Nat
  for m: Nat
  for +q: Nat
  for r: Nat
  {Nat.divmod.go(n, m, 1n+q, r) == next_quotient(Nat.divmod.go(n, m, q, r)) : Nat & Nat}
def quotient_translation(n, m, q, r):
  match n:
    case 0n: {==}
    case 1n+p:
      match m:
        case 0n:
          quotient_translation(p, r, 1n+q, 0n)
        case 1n+k:
          quotient_translation(p, k, q, 1n+r)

law character_stride:
  for position: Nat
  {Nat.divmod(Nat.add(33n, position), 33n) == next_quotient(Nat.divmod(position, 33n)) : Nat & Nat}
def character_stride(position):
  quotient_translation(position, 32n, 0n, 0n)

law bit_at_next:
  for h: Char
  for tail: String
  for pair: Nat & Nat
  {Map.bit.at(SCon{h, tail}, next_quotient(pair)) == Map.bit.go.rec(h, Map.bit.at(tail, pair)) : String & Bool}
def bit_at_next(h, tail, pair):
  match pair:
    case Tuple{q, r}: {==}

# This exact key-preserving result connects bit positions across String prefixes
# using the native division and bit traversal definitions.
law native_character_stride:
  for +h: Char
  for +tail: String
  for +position: Nat
  {Map.bit(SCon{h, tail}, Nat.add(33n, position)) == Map.bit.go.rec(h, Map.bit(tail, position)) : String & Bool}
def native_character_stride(h, tail, position):
  Equal.trans(String & Bool, Map.bit(SCon{h, tail}, Nat.add(33n, position)), Map.bit.at(SCon{h, tail}, next_quotient(Nat.divmod(position, 33n))), Map.bit.go.rec(h, Map.bit(tail, position)), Equal.cong(Nat & Nat, String & Bool, qr => Map.bit.at(SCon{h, tail}, qr), Nat.divmod(Nat.add(33n, position), 33n), next_quotient(Nat.divmod(position, 33n)), character_stride(position)), bit_at_next(h, tail, Nat.divmod(position, 33n)))

law add_right_successor:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}
def add_right_successor(a, b):
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_right_successor(p, b))

law division_no_wrap:
  for n: Nat
  for m: Nat
  for +q: Nat
  for +r: Nat
  for bound: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.divmod.go(n, m, q, r) == (q, Nat.add(n, r)) : Nat & Nat}
def division_no_wrap(n, m, q, r, bound):
  match n:
    case 0n: {==}
    case 1n+ +p:
      match m:
        case 0n:
          Empty.absurd({Nat.divmod.go(1n+p, 0n, q, r) == (q, Nat.add(1n+p, r)) : Nat & Nat}, Logic.false_true(bound))
        case 1n+ +k:
          Equal.trans(Nat & Nat, Nat.divmod.go(p, k, q, 1n+r), (q, Nat.add(p, 1n+r)), (q, 1n+Nat.add(p, r)), division_no_wrap(p, k, q, 1n+r, bound), Equal.cong(Nat, Nat & Nat, s => (q, s), Nat.add(p, 1n+r), 1n+Nat.add(p, r), add_right_successor(p, r)))

law first_character_division:
  for +position: Nat
  for bound: {Nat.is_le(position, 32n) == True{} : Bool}
  {Nat.divmod(position, 33n) == (0n, position) : Nat & Nat}
def first_character_division(position, bound):
  Equal.trans(Nat & Nat, Nat.divmod(position, 33n), (0n, Nat.add(position, 0n)), (0n, position), division_no_wrap(position, 32n, 0n, 0n, bound), Equal.cong(Nat, Nat & Nat, r => (0n, r), Nat.add(position, 0n), position, N.natural_add_right_zero(position)))

law native_first_character:
  for +head: Char
  for +tail: String
  for +position: Nat
  for bound: {Nat.is_le(position, 32n) == True{} : Bool}
  {Map.bit(SCon{head, tail}, position) == Map.bit.go.chr(tail, Map.bit.chr(head, position)) : String & Bool}
def native_first_character(head, tail, position, bound):
  Equal.cong(Nat & Nat, String & Bool, qr => Map.bit.at(SCon{head, tail}, qr), Nat.divmod(position, 33n), (0n, position), first_character_division(position, bound))
