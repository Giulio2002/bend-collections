import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ../../lib/word.bend as WD
import ../../lib/u32div.bend as UD
import ./table.bend as TB
import ../../lib/words32.bend as W32

# Base.Array reads on the mirror trees of the hash map's arrays, and the
# bucket index arithmetic (bucket i's word at 2i, its link at 2i + 1).


# 2^d <= 2^32 for d < 32

# the word index 2i and the link index 2i + 1 of bucket i
def ix_w(+i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.shl(i)) == Nat.double(UD.v(i)) : Nat}:
  U.shl_value(i, d, N.lt_le(d, 32n, hd), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(d), N.lt_succ(Nat.double(UD.v(i))), h))

def ix_l1(+one: Nat, +h1: {one == 1n : Nat}, +i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.inc(U32.shl(i))) == 1n+Nat.double(UD.v(i)) : Nat}:
  +ew = ix_w(i, d, hd, h)
  +hb = L.subst(Nat, z => {Nat.is_lt(1n+z, WD.sc(32n, one)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_le_trans(1n+Nat.double(UD.v(i)), SC.pow2(d), WD.sc(32n, one), h, W32.pow_le32(one, h1, d, hd)))
  Equal.trans(Nat, UD.v(U32.inc(U32.shl(i))), 1n+UD.v(U32.shl(i)), 1n+Nat.double(UD.v(i)), W32.inc_val(one, h1, U32.shl(i), hb), Equal.cong(Nat, Nat, z => 1n+z, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew))

def ix_l(+i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.inc(U32.shl(i))) == 1n+Nat.double(UD.v(i)) : Nat}:
  ix_l1(1n, {==}, i, d, hd, h)

# reading a word array at an index below its size
def getw(+d: Nat, +t: AR.Tree<U32>, +j: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {Nat.is_lt(UD.v(j), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, t), j) == (AR.thaw(U32, t), W32.nth0(AR.slots(U32, t), UD.v(j))) : Array<U32> & U32}:
  +hl = L.subst(Nat, z => {Nat.is_lt(UD.v(j), z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.slots(U32, t)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, t)), SC.pow2(d), AR.slots_length(U32, d, t, pf)), hj)
  AR.get(U32, d, t, j, W32.nth0(AR.slots(U32, t), UD.v(j)), hd, hj, W32.nth_some(AR.slots(U32, t), UD.v(j), hl), pf)

def nths_of(+d: Nat, +t: AR.Tree<String>, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(String, d, t) == True{} : Bool}) -> {SC.nth(String, AR.slots(String, t), j) == Some{TB.nths(AR.slots(String, t), j)} : Maybe<&2, String>}:
  TB.nths_some(AR.slots(String, t), j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(String, AR.slots(String, t)), Equal.sym(Nat, SC.length(String, AR.slots(String, t)), SC.pow2(d), AR.slots_length(String, d, t, pf)), hj))
