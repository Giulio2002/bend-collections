import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../math/word.bend as WD
import ../math/arith.bend as AT
import ../math/u32div.bend as UD
import ./cyc.bend as CY
import ./table.bend as TB

# Base.Array reads on the mirror trees of the hash map's arrays, and the
# bucket index arithmetic (bucket i's word at 2i, its link at 2i + 1).

def pow_one(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat) -> {SC.pow2(d) == WD.sc(d, one) : Nat}:
  Equal.trans(Nat, SC.pow2(d), WD.sc(d, 1n), WD.sc(d, one), U.pow2_scale(d), Equal.cong(Nat, Nat, o => WD.sc(d, o), 1n, one, Equal.sym(Nat, one, 1n, h1)))

# 2^d <= 2^32 for d < 32
def pow_le32(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {Nat.is_le(SC.pow2(d), WD.sc(32n, one)) == True{} : Bool}:
  +j = Nat.sub(32n, d)
  +e = Equal.trans(Nat, WD.sc(32n, one), WD.sc(Nat.add(d, j), one), WD.sc(d, WD.sc(j, one)), Equal.cong(Nat, Nat, z => WD.sc(z, one), 32n, Nat.add(d, j), Equal.sym(Nat, Nat.add(d, j), 32n, N.sub_add(32n, d, N.lt_le(d, 32n, hd)))), AT.sc_idx(d, j, one))
  L.subst(Nat, z => {Nat.is_le(SC.pow2(d), z) == True{} : Bool}, WD.sc(d, WD.sc(j, one)), WD.sc(32n, one), Equal.sym(Nat, WD.sc(32n, one), WD.sc(d, WD.sc(j, one)), e), L.subst(Nat, z => {Nat.is_le(z, WD.sc(d, WD.sc(j, one))) == True{} : Bool}, WD.sc(d, one), SC.pow2(d), Equal.sym(Nat, SC.pow2(d), WD.sc(d, one), pow_one(one, h1, d)), AT.sc_le(d, one, WD.sc(j, one), AT.le_sc(j, one))))

# the word index 2i and the link index 2i + 1 of bucket i
def ix_w(+i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.shl(i)) == Nat.double(UD.v(i)) : Nat}:
  U.shl_value(i, d, N.lt_le(d, 32n, hd), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(d), N.lt_succ(Nat.double(UD.v(i))), h))

def ix_l1(+one: Nat, +h1: {one == 1n : Nat}, +i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.inc(U32.shl(i))) == 1n+Nat.double(UD.v(i)) : Nat}:
  +ew = ix_w(i, d, hd, h)
  +hb = L.subst(Nat, z => {Nat.is_lt(1n+z, WD.sc(32n, one)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_le_trans(1n+Nat.double(UD.v(i)), SC.pow2(d), WD.sc(32n, one), h, pow_le32(one, h1, d, hd)))
  Equal.trans(Nat, UD.v(U32.inc(U32.shl(i))), 1n+UD.v(U32.shl(i)), 1n+Nat.double(UD.v(i)), CY.inc_val(one, h1, U32.shl(i), hb), Equal.cong(Nat, Nat, z => 1n+z, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew))

def ix_l(+i: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +h: {Nat.is_lt(1n+Nat.double(UD.v(i)), SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.inc(U32.shl(i))) == 1n+Nat.double(UD.v(i)) : Nat}:
  ix_l1(1n, {==}, i, d, hd, h)

# reading a word array at an index below its size
def getw(+d: Nat, +t: AR.Tree<U32>, +j: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hj: {Nat.is_lt(UD.v(j), SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, t), j) == (AR.thaw(U32, t), TB.nth0(AR.slots(U32, t), UD.v(j))) : Array<U32> & U32}:
  +hl = L.subst(Nat, z => {Nat.is_lt(UD.v(j), z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.slots(U32, t)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, t)), SC.pow2(d), AR.slots_length(U32, d, t, pf)), hj)
  AR.get(U32, d, t, j, TB.nth0(AR.slots(U32, t), UD.v(j)), hd, hj, TB.nth_some(AR.slots(U32, t), UD.v(j), hl), pf)

def nths_of(+d: Nat, +t: AR.Tree<String>, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(String, d, t) == True{} : Bool}) -> {SC.nth(String, AR.slots(String, t), j) == Some{TB.nths(AR.slots(String, t), j)} : Maybe<&2, String>}:
  TB.nths_some(AR.slots(String, t), j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(String, AR.slots(String, t)), Equal.sym(Nat, SC.length(String, AR.slots(String, t)), SC.pow2(d), AR.slots_length(String, d, t, pf)), hj))
