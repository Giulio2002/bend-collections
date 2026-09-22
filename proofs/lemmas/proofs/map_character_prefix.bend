import Base
import ./map_difference_char.bend as D
import ./map_difference_order.bend as O
import ./map_index.bend as Index
import ./map_msb.bend as M

law earlier_index:
  for +scan: Nat
  for +index: Nat
  for +bound: {Nat.is_le(scan, 32n) == True{} : Bool}
  for earlier: {Nat.is_lt(1n+index, Nat.sub(33n, scan)) == True{} : Bool}
  {Nat.is_le(scan, Nat.sub(31n, index)) == True{} : Bool}
def earlier_index(scan, index, bound, earlier):
  small = {%D.subtract_successor(32n, scan, bound) : {Nat.is_lt(1n+index, _) == True{} : Bool} earlier : {Nat.is_lt(index, Nat.sub(32n, scan)) == True{} : Bool}}
  sum = O.add_sub_bound(32n, scan, 1n+index, bound, O.strict_successor(index, Nat.sub(32n, scan), small))
  O.sub_from_add(31n, index, scan, %O.add_commute(scan, index) : {Nat.is_le(_, 31n) == True{} : Bool} %Index.add_right_successor(scan, index) : {Nat.is_le(_, 32n) == True{} : Bool} sum)

law word_above_scan:
  for +a: U32
  for +b: U32
  for +index: Nat
  for bound: {Nat.is_le(Map.msb.u(32n, U32.xor(a, b)), index) == True{} : Bool}
  {Bool.xor(Map.bit.u(a, index), Map.bit.u(b, index)) == False{} : Bool}
def word_above_scan(a, b, index, bound):
  %O.add_complement(index, Map.msb.u(32n, U32.xor(a, b)), bound) : {Bool.xor(Map.bit.u(a, _), Map.bit.u(b, _)) == False{} : Bool}
  D.earlier_word_bits_agree(a, b, Nat.sub(index, Map.msb.u(32n, U32.xor(a, b))))

# All character offsets strictly before the native discriminator agree.
# Unlike distinction, prefix agreement also holds when the characters are equal.
law native_character_prefix:
  for +a: U32
  for +b: U32
  for offset: Nat
  for earlier: {Nat.is_lt(offset, Map.diff.chr(U32.xor(a, b))) == True{} : Bool}
  {Bool.xor(D.bit(Map.bit.chr(Chr{a}, offset)), D.bit(Map.bit.chr(Chr{b}, offset))) == False{} : Bool}
def native_character_prefix(a, b, offset, earlier):
  match offset:
    case 0n: {==}
    case 1n+ +index:
      word_above_scan(a, b, Nat.sub(31n, index), earlier_index(Map.msb.u(32n, U32.xor(a, b)), index, M.native_bound(32n, U32.xor(a, b)), earlier))
