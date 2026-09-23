import Base
import ./map_bits.bend as Bits
import ./map_msb.bend as M
import ./map_routing.bend as Logic
import ./recency_bounds.bend as Bounds

law le_self:
  for n: Nat
  {Nat.is_le(n, n) == True{} : Bool}
def le_self(n):
  match n:
    case 0n: {==}
    case 1n+p: le_self(p)

law subtract_bound:
  for n: Nat
  for k: Nat
  {Nat.is_le(Nat.sub(n, k), n) == True{} : Bool}
def subtract_bound(n, k):
  match n k:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n:
      le_self(1n+p)
    case 1n+ +p 1n+ +q:
      Bounds.le_weaken(Nat.sub(p, q), p, subtract_bound(p, q))

law subtract_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}
def subtract_self(n):
  match n:
    case 0n: {==}
    case 1n+p: subtract_self(p)

law subtract_successor:
  for n: Nat
  for k: Nat
  for bound: {Nat.is_le(k, n) == True{} : Bool}
  {Nat.sub(1n+n, k) == 1n+Nat.sub(n, k) : Nat}
def subtract_successor(n, k, bound):
  match n k:
    case 0n 0n: {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, Logic.false_true(bound))
    case 1n+p 0n: {==}
    case 1n+p 1n+q:
      subtract_successor(p, q, bound)

law subtract_involution:
  for n: Nat
  for k: Nat
  for bound: {Nat.is_le(k, n) == True{} : Bool}
  {Nat.sub(n, Nat.sub(n, k)) == k : Nat}
def subtract_involution(n, k, bound):
  match n k:
    case 0n 0n: {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+q)) == 1n+q : Nat}, Logic.false_true(bound))
    case 1n+p 0n:
      subtract_self(1n+p)
    case 1n+ +p 1n+ +q:
      Equal.trans(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), 1n+q, subtract_successor(p, Nat.sub(p, q), subtract_bound(p, q)), Equal.cong(Nat, Nat, x => 1n+x, Nat.sub(p, Nat.sub(p, q)), q, subtract_involution(p, q, bound)))

def bit(r: Char & Bool) -> Bool:
  (c, b) = r
  b

law character_offset:
  for +x: U32
  for +position: Nat
  for +bound: {Nat.is_le(position, 31n) == True{} : Bool}
  {bit(Map.bit.chr(Chr{x}, Nat.sub(32n, position))) == Map.bit.u(x, position) : Bool}
def character_offset(x, position, bound):
  %Equal.sym(Nat, Nat.sub(32n, position), 1n+Nat.sub(31n, position), subtract_successor(31n, position, bound)) : {bit(Map.bit.chr(Chr{x}, _)) == Map.bit.u(x, position) : Bool}
  Equal.cong(Nat, Bool, i => Map.bit.u(x, i), Nat.sub(31n, Nat.sub(31n, position)), position, subtract_involution(31n, position, bound))

law from_difference:
  for +a: U32
  for +b: U32
  for difference: M.Difference(a, b)
  {Bool.xor(bit(Map.bit.chr(Chr{a}, Map.diff.chr(U32.xor(a, b)))), bit(Map.bit.chr(Chr{b}, Map.diff.chr(U32.xor(a, b))))) == True{} : Bool}
def from_difference(a, b, difference):
  match difference:
    case Tuple{+position, Tuple{+length, differing}}:
      +bound = {%length : {Nat.is_le(_, 32n) == True{} : Bool} M.native_bound(32n, U32.xor(a, b)) : {Nat.is_le(position, 31n) == True{} : Bool}}
      %Equal.sym(Nat, Map.msb.u(32n, U32.xor(a, b)), 1n+position, length) : {Bool.xor(bit(Map.bit.chr(Chr{a}, Nat.sub(33n, _))), bit(Map.bit.chr(Chr{b}, Nat.sub(33n, _)))) == True{} : Bool}
      %Equal.sym(Bool, bit(Map.bit.chr(Chr{a}, Nat.sub(32n, position))), Map.bit.u(a, position), character_offset(a, position, bound)) : {Bool.xor(_, bit(Map.bit.chr(Chr{b}, Nat.sub(32n, position)))) == True{} : Bool}
      %Equal.sym(Bool, bit(Map.bit.chr(Chr{b}, Nat.sub(32n, position))), Map.bit.u(b, position), character_offset(b, position, bound)) : {Bool.xor(Map.bit.u(a, position), _) == True{} : Bool}
      differing

# Actual Map.diff.chr chooses a genuinely differing character bit. Least-bit
# prefix and whole-string offset/routing composition are separate obligations.
law native_character_difference:
  for +a: U32
  for +b: U32
  for unequal: {U32.is_eq(a, b) == False{} : Bool}
  {Bool.xor(bit(Map.bit.chr(Chr{a}, Map.diff.chr(U32.xor(a, b)))), bit(Map.bit.chr(Chr{b}, Map.diff.chr(U32.xor(a, b))))) == True{} : Bool}
def native_character_difference(a, b, unequal):
  from_difference(a, b, M.unequal_character_difference(a, b, unequal))

law earlier_word_bits_agree:
  for +a: U32
  for +b: U32
  for +distance: Nat
  {Bool.xor(Map.bit.u(a, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance)), Map.bit.u(b, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance))) == False{} : Bool}
def earlier_word_bits_agree(a, b, distance):
  Equal.trans(Bool, Bool.xor(Map.bit.u(a, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance)), Map.bit.u(b, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance))), Map.bit.u(U32.xor(a, b), Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance)), False{}, Equal.sym(Bool, Map.bit.u(U32.xor(a, b), Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance)), Bool.xor(Map.bit.u(a, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance)), Map.bit.u(b, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance))), Bits.native_xor(a, b, Nat.add(Map.msb.u(32n, U32.xor(a, b)), distance))), M.above_native_msb(U32.xor(a, b), distance))

law difference_bound:
  for +a: U32
  for +b: U32
  for difference: M.Difference(a, b)
  {Nat.is_le(Map.diff.chr(U32.xor(a, b)), 32n) == True{} : Bool}
def difference_bound(a, b, difference):
  match difference:
    case Tuple{position, Tuple{length, differing}}:
      %Equal.sym(Nat, Map.msb.u(32n, U32.xor(a, b)), 1n+position, length) : {Nat.is_le(Nat.sub(33n, _), 32n) == True{} : Bool}
      subtract_bound(32n, position)
