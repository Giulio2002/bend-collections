import Base
import ../../../src/math/hash.bend as HS
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32div.bend as UD

# src/math/hash.bend: every bucket index lies inside the table.
#   bucket_le: bucket(w, mask) <= mask for every mask
#   bucket_lt: bucket(w, mask) < 2^k when mask is the low k bits (a table of
#              2^k buckets)

def bit_and_le(+a: Bool, +b: Bool) -> {Nat.is_le(S.bit_value(Bool.and(a, b)), S.bit_value(b)) == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  +l1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(c, b)) == True{} : Bool}, Nat.add(c, a), Nat.add(a, c), N.add_comm(c, a), N.le_add_left(a, b, c, h1))
  +l2 = L.subst(Nat, z => {Nat.is_le(Nat.add(a, c), z) == True{} : Bool}, Nat.add(c, b), Nat.add(b, c), N.add_comm(c, b), l1)
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), l2, N.le_add_left(c, d, b, h2))

# masking never exceeds the mask
def and_le(+n: Nat, +x: Word(n), +m: Word(n)) -> {Nat.is_le(WD.uw(n, Word.and(n, x, m)), WD.uw(n, m)) == True{} : Bool}:
  match n x m:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{a, t1} WCon{b, t2}:
      add_le(S.bit_value(Bool.and(a, b)), S.bit_value(b), Nat.double(WD.uw(p, Word.and(p, t1, t2))), Nat.double(WD.uw(p, t2)), bit_and_le(a, b), N.double_le(WD.uw(p, Word.and(p, t1, t2)), WD.uw(p, t2), and_le(p, t1, t2)))

def and_le32(+x: U32, +m: U32) -> {Nat.is_le(UD.v(U32.and(x, m)), UD.v(m)) == True{} : Bool}:
  match x m:
    case U32{+a} U32{+b}:
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, a, b)}), WD.uw(32n, Word.and(32n, a, b)), UD.vw(Word.and(32n, a, b))) : {Nat.is_le(_, UD.v(U32{b})) == True{} : Bool}
      %Equal.sym(Nat, UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)) : {Nat.is_le(WD.uw(32n, Word.and(32n, a, b)), _) == True{} : Bool}
      and_le(32n, a, b)

# THEOREM: a bucket never exceeds the mask.
def bucket_le(+w: U32, +mask: U32) -> {Nat.is_le(UD.v(HS.bucket(w, mask)), UD.v(mask)) == True{} : Bool}:
  and_le32(U32.xor(U32.mul(w, HS.phi32()), U32.shrn(U32.mul(w, HS.phi32()), 16n)), mask)

def and_mask_lt(+x: U32, +k: Nat) -> {Nat.is_lt(UD.v(U32.and(x, U32{WD.mask(32n, k)})), WD.sc(k, 1n)) == True{} : Bool}:
  match x:
    case U32{+xw}:
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, xw, WD.mask(32n, k))}), WD.uw(32n, Word.and(32n, xw, WD.mask(32n, k))), UD.vw(Word.and(32n, xw, WD.mask(32n, k)))) : {Nat.is_lt(_, WD.sc(k, 1n)) == True{} : Bool}
      WD.mask_lt(32n, k, 1n, {==}, xw)

def bucket_ltw(+w: U32, +k: Nat) -> {Nat.is_lt(UD.v(HS.bucket(w, U32{WD.mask(32n, k)})), WD.sc(k, 1n)) == True{} : Bool}:
  and_mask_lt(U32.xor(U32.mul(w, HS.phi32()), U32.shrn(U32.mul(w, HS.phi32()), 16n)), k)

# THEOREM: with mask = 2^k - 1 (k low bits) the bucket indexes a table of 2^k.
def bucket_lt(+w: U32, +k: Nat, +mask: U32, +hm: {mask == U32{WD.mask(32n, k)} : U32}) -> {Nat.is_lt(UD.v(HS.bucket(w, mask)), WD.sc(k, 1n)) == True{} : Bool}:
  L.subst(U32, z => {Nat.is_lt(UD.v(HS.bucket(w, z)), WD.sc(k, 1n)) == True{} : Bool}, U32{WD.mask(32n, k)}, mask, Equal.sym(U32, mask, U32{WD.mask(32n, k)}, hm), bucket_ltw(w, k))
