import Base
import ../lib/logic.bend as L
import ../../src/lru/wide.bend as W
import ./num/numeric.bend as NUM
import ../../types/lru_model.bend as T
import ./state.bend as ST
import ../lib/array.bend as AR
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import support/links_state.bend as DST
import support/links_links.bend as LK
import support/links_tolist.bend as TL
import support/links_insert.bend as IN
import support/array_shift.bend as SH

# The five 64-bit counters are kept as ten U32 limbs (low limb at 2c, high at
# 2c + 1). Incrementing the pair (increment the low limb; if it wrapped to 0,
# increment the high limb) is the 64-bit increment of the packed word.

# every bit set: incrementing wraps to zero
def carry(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          Bool.and(h, carry(p, t))

def wpick(-m: Nat, b: Bool, x: Word(m), y: Word(m)) -> Word(m):
  match b:
    case True{}:
      x
    case False{}:
      y

# the increment of a joined word carries into the high part exactly when the
# low part is all ones
def winc_bit(+p: Nat, +m: Nat, h: Bool, t: Word(p), +b: Word(m), ih: {Word.inc(Nat.add(p, m), W.join(p, m, t, b)) == W.join(p, m, Word.inc(p, t), wpick(m, carry(p, t), Word.inc(m, b), b)) : Word(Nat.add(p, m))}) -> {Word.inc(Nat.add(1n+p, m), W.join(1n+p, m, WCon{h, t}, b)) == W.join(1n+p, m, Word.inc(1n+p, WCon{h, t}), wpick(m, carry(1n+p, WCon{h, t}), Word.inc(m, b), b)) : Word(Nat.add(1n+p, m))}:
  match h:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Word(Nat.add(p, m)), Word(Nat.add(1n+p, m)), z => WCon{False{}, z}, Word.inc(Nat.add(p, m), W.join(p, m, t, b)), W.join(p, m, Word.inc(p, t), wpick(m, carry(p, t), Word.inc(m, b), b)), ih)

# incrementing leaves zero exactly when it carried

def winc_join(n: Nat, +m: Nat, a: Word(n), +b: Word(m)) -> {Word.inc(Nat.add(n, m), W.join(n, m, a, b)) == W.join(n, m, Word.inc(n, a), wpick(m, carry(n, a), Word.inc(m, b), b)) : Word(Nat.add(n, m))}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{h, +t}:
          winc_bit(p, m, h, t, b, winc_join(p, m, t, b))

def zero_inc_bit(+p: Nat, h: Bool, t: Word(p), ih: {W.is_zero(p, Word.inc(p, t)) == carry(p, t) : Bool}) -> {W.is_zero(1n+p, Word.inc(1n+p, WCon{h, t})) == carry(1n+p, WCon{h, t}) : Bool}:
  match h:
    case False{}:
      {==}
    case True{}:
      ih


def zero_inc(n: Nat, w: Word(n)) -> {W.is_zero(n, Word.inc(n, w)) == carry(n, w) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{h, +t}:
          zero_inc_bit(p, h, t, zero_inc(p, t))

def u32_data(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

def u32_eta(x: U32) -> {x == U32{u32_data(x)} : U32}:
  match x:
    case U32{w}:
      {==}

def u32_pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# the runtime's wrap test on the low limb is the carry
def wrap_test(+x: U32) -> {U32.is_eq(U32.inc(x), 0) == carry(32n, u32_data(x)) : Bool}:
  match x:
    case U32{w}:
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.inc(32n, w), Word.zero(32n))), W.is_zero(32n, Word.inc(32n, w)), carry(32n, w), NUM.zero_comparison_correspondence(32n, Word.inc(32n, w)), zero_inc(32n, w))

def pick_pack(b: Bool, +x: U32, +y: U32) -> {u32_data(u32_pick(b, x, y)) == wpick(32n, b, u32_data(x), u32_data(y)) : Word(32n)}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the limb-pair increment is the 64-bit increment
def pack_inc(+lo: U32, +hi: U32) -> {W.pack(U32.inc(lo), u32_pick(U32.is_eq(U32.inc(lo), 0), U32.inc(hi), hi)) == Word.inc(64n, W.pack(lo, hi)) : Word(64n)}:
  match lo hi:
    case U32{a} U32{b}:
      %Equal.sym(Bool, U32.is_eq(U32.inc(U32{a}), 0), carry(32n, a), wrap_test(U32{a})) : {W.pack(U32{Word.inc(32n, a)}, u32_pick(_, U32{Word.inc(32n, b)}, U32{b})) == Word.inc(64n, W.join(32n, 32n, a, b)) : Word(64n)}
      %Equal.sym(U32, u32_pick(carry(32n, a), U32{Word.inc(32n, b)}, U32{b}), U32{u32_data(u32_pick(carry(32n, a), U32{Word.inc(32n, b)}, U32{b}))}, u32_eta(u32_pick(carry(32n, a), U32{Word.inc(32n, b)}, U32{b}))) : {W.pack(U32{Word.inc(32n, a)}, _) == Word.inc(64n, W.join(32n, 32n, a, b)) : Word(64n)}
      %Equal.sym(Word(32n), u32_data(u32_pick(carry(32n, a), U32{Word.inc(32n, b)}, U32{b})), wpick(32n, carry(32n, a), Word.inc(32n, b), b), pick_pack(carry(32n, a), U32{Word.inc(32n, b)}, U32{b})) : {W.join(32n, 32n, Word.inc(32n, a), _) == Word.inc(64n, W.join(32n, 32n, a, b)) : Word(64n)}
      Equal.sym(Word(64n), Word.inc(64n, W.join(32n, 32n, a, b)), W.join(32n, 32n, Word.inc(32n, a), wpick(32n, carry(32n, a), Word.inc(32n, b), b)), winc_join(32n, 32n, a, b))

# ---- the counter block ----

def cget(+t: AR.Tree<U32>, +x: U32) -> Array<U32> & U32:
  (AR.thaw(U32, t), x)

def bt_hi(+t1: AR.Tree<U32>, +i: Nat, +h: U32, zero: Bool) -> AR.Tree<U32>:
  match zero:
    case True{}:
      AR.upd(U32, 4n, t1, 1n+i, U32.inc(h))
    case False{}:
      t1

# the counter tree after incrementing the counter whose low limb is at i
def bt(+tc: AR.Tree<U32>, +i: Nat) -> AR.Tree<U32>:
  bt_hi(AR.upd(U32, 4n, tc, i, U32.inc(DST.lat(AR.slots(U32, tc), i))), i, DST.lat(AR.slots(U32, tc), 1n+i), U32.is_eq(U32.inc(DST.lat(AR.slots(U32, tc), i)), 0))

def bh_ok(+t1: AR.Tree<U32>, +c: U32, +i: Nat, +ec2: {U32.inc(U32.shl(c)) == U32.from_nat(1n+i) : U32}, +pf: {AR.perfect(U32, 4n, t1) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}, zero: Bool) -> {F.bump_hi(AR.thaw(U32, t1), c, zero) == AR.thaw(U32, bt_hi(t1, i, DST.lat(AR.slots(U32, t1), 1n+i), zero)) : Array<U32>}:
  match zero:
    case False{}:
      {==}
    case True{}:
      +h = DST.lat(AR.slots(U32, t1), 1n+i)
      %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t1), U32.inc(U32.shl(c))), cget(t1, h), Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t1), U32.inc(U32.shl(c))), Array.get(U32, AR.thaw(U32, t1), U32.from_nat(1n+i)), cget(t1, h), Equal.cong(U32, Array<U32> & U32, z => Array.get(U32, AR.thaw(U32, t1), z), U32.inc(U32.shl(c)), U32.from_nat(1n+i), ec2), TL.get_at(U32, 4n, t1, 1n+i, 0, {==}, pf, hi))) : {F.bump_hi_go(U32.inc(U32.shl(c)), _) == AR.thaw(U32, AR.upd(U32, 4n, t1, 1n+i, U32.inc(h))) : Array<U32>}
      Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, t1), U32.inc(U32.shl(c)), U32.inc(h)), Array.set(U32, AR.thaw(U32, t1), U32.from_nat(1n+i), U32.inc(h)), AR.thaw(U32, AR.upd(U32, 4n, t1, 1n+i, U32.inc(h))),
        Equal.cong(U32, Array<U32>, z => Array.set(U32, AR.thaw(U32, t1), z, U32.inc(h)), U32.inc(U32.shl(c)), U32.from_nat(1n+i), ec2),
        IN.set_f(U32, 4n, t1, 1n+i, U32.inc(h), {==}, hi, pf))

# The runtime increment of counter c (low limb at i = 2c) on the counter block.
def bump_ok(+tc: AR.Tree<U32>, +c: U32, +i: Nat, +ec1: {U32.shl(c) == U32.from_nat(i) : U32}, +ec2: {U32.inc(U32.shl(c)) == U32.from_nat(1n+i) : U32}, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}) -> {F.bump(c, AR.thaw(U32, tc)) == AR.thaw(U32, bt(tc, i)) : Array<U32>}:
  +cs = AR.slots(U32, tc)
  +l = DST.lat(cs, i)
  +hi0 = N.lt_trans(i, 1n+i, 16n, N.lt_succ(i), hi)
  +t1 = AR.upd(U32, 4n, tc, i, U32.inc(l))
  +pf1 = AR.upd_perfect(U32, 4n, tc, i, U32.inc(l), pf)
  +eh = Equal.trans(U32, DST.lat(AR.slots(U32, t1), 1n+i), DST.lat(SC.update(U32, cs, i, U32.inc(l)), 1n+i), DST.lat(cs, 1n+i),
    Equal.cong(List<&2, U32>, U32, z => DST.lat(z, 1n+i), AR.slots(U32, t1), SC.update(U32, cs, i, U32.inc(l)), AR.upd_slots(U32, 4n, tc, i, U32.inc(l), hi0, pf)),
    LK.lat_other(cs, i, U32.inc(l), 1n+i, SH.ne_of_lt(i, 1n+i, N.lt_succ(i))))
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tc), U32.shl(c)), cget(tc, l), Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tc), U32.shl(c)), Array.get(U32, AR.thaw(U32, tc), U32.from_nat(i)), cget(tc, l), Equal.cong(U32, Array<U32> & U32, z => Array.get(U32, AR.thaw(U32, tc), z), U32.shl(c), U32.from_nat(i), ec1), TL.get_at(U32, 4n, tc, i, 0, {==}, pf, hi0))) : {F.bump_lo(c, _) == AR.thaw(U32, bt(tc, i)) : Array<U32>}
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tc), U32.shl(c), U32.inc(l)), AR.thaw(U32, t1), Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, tc), U32.shl(c), U32.inc(l)), Array.set(U32, AR.thaw(U32, tc), U32.from_nat(i), U32.inc(l)), AR.thaw(U32, t1), Equal.cong(U32, Array<U32>, z => Array.set(U32, AR.thaw(U32, tc), z, U32.inc(l)), U32.shl(c), U32.from_nat(i), ec1), IN.set_f(U32, 4n, tc, i, U32.inc(l), {==}, hi0, pf))) : {F.bump_hi(_, c, U32.is_eq(U32.inc(l), 0)) == AR.thaw(U32, bt(tc, i)) : Array<U32>}
  L.subst(U32, z => {F.bump_hi(AR.thaw(U32, t1), c, U32.is_eq(U32.inc(l), 0)) == AR.thaw(U32, bt_hi(t1, i, z, U32.is_eq(U32.inc(l), 0))) : Array<U32>}, DST.lat(AR.slots(U32, t1), 1n+i), DST.lat(cs, 1n+i), eh, bh_ok(t1, c, i, ec2, pf1, hi, U32.is_eq(U32.inc(l), 0)))

# ---- the counters after an increment ----

def sbt(+cs: List<&2, U32>, +i: Nat, zero: Bool, +h: U32, +l2: U32) -> List<&2, U32>:
  match zero:
    case True{}:
      SC.update(U32, SC.update(U32, cs, i, l2), 1n+i, U32.inc(h))
    case False{}:
      SC.update(U32, cs, i, l2)

def slots_bt_c(+tc: AR.Tree<U32>, +i: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}, +l2: U32, +h: U32, zero: Bool) -> {AR.slots(U32, bt_hi(AR.upd(U32, 4n, tc, i, l2), i, h, zero)) == sbt(AR.slots(U32, tc), i, zero, h, l2) : List<&2, U32>}:
  match zero:
    case False{}:
      +hi0 = N.lt_trans(i, 1n+i, 16n, N.lt_succ(i), hi)
      AR.upd_slots(U32, 4n, tc, i, l2, hi0, pf)
    case True{}:
      +hi0 = N.lt_trans(i, 1n+i, 16n, N.lt_succ(i), hi)
      Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 4n, AR.upd(U32, 4n, tc, i, l2), 1n+i, U32.inc(h))), SC.update(U32, AR.slots(U32, AR.upd(U32, 4n, tc, i, l2)), 1n+i, U32.inc(h)), SC.update(U32, SC.update(U32, AR.slots(U32, tc), i, l2), 1n+i, U32.inc(h)),
        AR.upd_slots(U32, 4n, AR.upd(U32, 4n, tc, i, l2), 1n+i, U32.inc(h), hi, AR.upd_perfect(U32, 4n, tc, i, l2, pf)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, 1n+i, U32.inc(h)), AR.slots(U32, AR.upd(U32, 4n, tc, i, l2)), SC.update(U32, AR.slots(U32, tc), i, l2), AR.upd_slots(U32, 4n, tc, i, l2, hi0, pf)))

def slots_bt(+tc: AR.Tree<U32>, +i: Nat, +pf: {AR.perfect(U32, 4n, tc) == True{} : Bool}, +hi: {Nat.is_lt(1n+i, 16n) == True{} : Bool}) -> {AR.slots(U32, bt(tc, i)) == sbt(AR.slots(U32, tc), i, U32.is_eq(U32.inc(DST.lat(AR.slots(U32, tc), i)), 0), DST.lat(AR.slots(U32, tc), 1n+i), U32.inc(DST.lat(AR.slots(U32, tc), i))) : List<&2, U32>}:
  slots_bt_c(tc, i, pf, hi, U32.inc(DST.lat(AR.slots(U32, tc), i)), DST.lat(AR.slots(U32, tc), 1n+i), U32.is_eq(U32.inc(DST.lat(AR.slots(U32, tc), i)), 0))

def lat_sbt_other(+cs: List<&2, U32>, +i: Nat, +h: U32, +l2: U32, +j: Nat, +hj0: {Nat.is_eq(i, j) == False{} : Bool}, +hj1: {Nat.is_eq(1n+i, j) == False{} : Bool}, zero: Bool) -> {DST.lat(sbt(cs, i, zero, h, l2), j) == DST.lat(cs, j) : U32}:
  match zero:
    case False{}:
      LK.lat_other(cs, i, l2, j, hj0)
    case True{}:
      Equal.trans(U32, DST.lat(SC.update(U32, SC.update(U32, cs, i, l2), 1n+i, U32.inc(h)), j), DST.lat(SC.update(U32, cs, i, l2), j), DST.lat(cs, j), LK.lat_other(SC.update(U32, cs, i, l2), 1n+i, U32.inc(h), j, hj1), LK.lat_other(cs, i, l2, j, hj0))

def pk_other(+cs: List<&2, U32>, +i: Nat, +h: U32, +l2: U32, +j: Nat, +k: Nat, +hj0: {Nat.is_eq(i, j) == False{} : Bool}, +hj1: {Nat.is_eq(1n+i, j) == False{} : Bool}, +hk0: {Nat.is_eq(i, k) == False{} : Bool}, +hk1: {Nat.is_eq(1n+i, k) == False{} : Bool}, +zero: Bool) -> {ST.pk(sbt(cs, i, zero, h, l2), j, k) == ST.pk(cs, j, k) : Word(64n)}:
  %Equal.sym(U32, DST.lat(sbt(cs, i, zero, h, l2), j), DST.lat(cs, j), lat_sbt_other(cs, i, h, l2, j, hj0, hj1, zero)) : {W.pack(_, DST.lat(sbt(cs, i, zero, h, l2), k)) == ST.pk(cs, j, k) : Word(64n)}
  %Equal.sym(U32, DST.lat(sbt(cs, i, zero, h, l2), k), DST.lat(cs, k), lat_sbt_other(cs, i, h, l2, k, hk0, hk1, zero)) : {W.pack(DST.lat(cs, j), _) == ST.pk(cs, j, k) : Word(64n)}
  {==}

def pk_same_c(+cs: List<&2, U32>, +i: Nat, +hlen: {Nat.is_lt(1n+i, SC.length(U32, cs)) == True{} : Bool}, zero: Bool, +ez: {U32.is_eq(U32.inc(DST.lat(cs, i)), 0) == zero : Bool}) -> {ST.pk(sbt(cs, i, zero, DST.lat(cs, 1n+i), U32.inc(DST.lat(cs, i))), i, 1n+i) == Word.inc(64n, ST.pk(cs, i, 1n+i)) : Word(64n)}:
  match zero:
    case False{}:
      +l = DST.lat(cs, i)
      +h = DST.lat(cs, 1n+i)
      +hi0 = N.lt_trans(i, 1n+i, SC.length(U32, cs), N.lt_succ(i), hlen)
      +epk = L.subst(Bool, z => {W.pack(U32.inc(l), u32_pick(z, U32.inc(h), h)) == Word.inc(64n, W.pack(l, h)) : Word(64n)}, U32.is_eq(U32.inc(l), 0), zero, ez, pack_inc(l, h))
      %Equal.sym(U32, DST.lat(SC.update(U32, cs, i, U32.inc(l)), i), U32.inc(l), LK.lat_same(cs, i, U32.inc(l), hi0)) : {W.pack(_, DST.lat(SC.update(U32, cs, i, U32.inc(l)), 1n+i)) == Word.inc(64n, W.pack(l, h)) : Word(64n)}
      %Equal.sym(U32, DST.lat(SC.update(U32, cs, i, U32.inc(l)), 1n+i), h, LK.lat_other(cs, i, U32.inc(l), 1n+i, SH.ne_of_lt(i, 1n+i, N.lt_succ(i)))) : {W.pack(U32.inc(l), _) == Word.inc(64n, W.pack(l, h)) : Word(64n)}
      epk
    case True{}:
      +l = DST.lat(cs, i)
      +h = DST.lat(cs, 1n+i)
      +hi0 = N.lt_trans(i, 1n+i, SC.length(U32, cs), N.lt_succ(i), hlen)
      +epk = L.subst(Bool, z => {W.pack(U32.inc(l), u32_pick(z, U32.inc(h), h)) == Word.inc(64n, W.pack(l, h)) : Word(64n)}, U32.is_eq(U32.inc(l), 0), zero, ez, pack_inc(l, h))
      +c1 = SC.update(U32, cs, i, U32.inc(l))
      %Equal.sym(U32, DST.lat(SC.update(U32, c1, 1n+i, U32.inc(h)), i), U32.inc(l), Equal.trans(U32, DST.lat(SC.update(U32, c1, 1n+i, U32.inc(h)), i), DST.lat(c1, i), U32.inc(l), LK.lat_other(c1, 1n+i, U32.inc(h), i, SH.ne_flip(i, 1n+i, SH.ne_of_lt(i, 1n+i, N.lt_succ(i)))), LK.lat_same(cs, i, U32.inc(l), hi0))) : {W.pack(_, DST.lat(SC.update(U32, c1, 1n+i, U32.inc(h)), 1n+i)) == Word.inc(64n, W.pack(l, h)) : Word(64n)}
      %Equal.sym(U32, DST.lat(SC.update(U32, c1, 1n+i, U32.inc(h)), 1n+i), U32.inc(h), LK.lat_same(c1, 1n+i, U32.inc(h), L.subst(Nat, z => {Nat.is_lt(1n+i, z) == True{} : Bool}, SC.length(U32, cs), SC.length(U32, c1), Equal.sym(Nat, SC.length(U32, c1), SC.length(U32, cs), LL.length_update(U32, cs, i, U32.inc(l))), hlen))) : {W.pack(U32.inc(l), _) == Word.inc(64n, W.pack(l, h)) : Word(64n)}
      epk

def pk_same(+cs: List<&2, U32>, +i: Nat, +hlen: {Nat.is_lt(1n+i, SC.length(U32, cs)) == True{} : Bool}) -> {ST.pk(sbt(cs, i, U32.is_eq(U32.inc(DST.lat(cs, i)), 0), DST.lat(cs, 1n+i), U32.inc(DST.lat(cs, i))), i, 1n+i) == Word.inc(64n, ST.pk(cs, i, 1n+i)) : Word(64n)}:
  pk_same_c(cs, i, hlen, U32.is_eq(U32.inc(DST.lat(cs, i)), 0), {==})

def mets_bump_0(+cs: List<&2, U32>, +hlen: {Nat.is_lt(1n, SC.length(U32, cs)) == True{} : Bool}) -> {ST.mets(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)))) == T.bump(0n, ST.mets(cs)) : T.Metrics}:
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 2n, 3n), ST.pk(cs, 2n, 3n), pk_other(cs, 0n, DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)), 2n, 3n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0))) : {T.Counts{Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 0n, 1n), Con{_, Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 4n, 5n), Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 6n, 7n), Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 8n, 9n), Nil{}}}}}}} == T.bump(0n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 4n, 5n), ST.pk(cs, 4n, 5n), pk_other(cs, 0n, DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)), 4n, 5n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0))) : {T.Counts{Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{_, Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 6n, 7n), Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 8n, 9n), Nil{}}}}}}} == T.bump(0n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 6n, 7n), ST.pk(cs, 6n, 7n), pk_other(cs, 0n, DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)), 6n, 7n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0))) : {T.Counts{Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{_, Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 8n, 9n), Nil{}}}}}}} == T.bump(0n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 8n, 9n), ST.pk(cs, 8n, 9n), pk_other(cs, 0n, DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n)), 8n, 9n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0))) : {T.Counts{Con{ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{_, Nil{}}}}}}} == T.bump(0n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 0n, U32.is_eq(U32.inc(DST.lat(cs, 0n)), 0), DST.lat(cs, 1n), U32.inc(DST.lat(cs, 0n))), 0n, 1n), Word.inc(64n, ST.pk(cs, 0n, 1n)), pk_same(cs, 0n, hlen)) : {T.Counts{Con{_, Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}} == T.bump(0n, ST.mets(cs)) : T.Metrics}
  {==}

def mets_bump_1(+cs: List<&2, U32>, +hlen: {Nat.is_lt(3n, SC.length(U32, cs)) == True{} : Bool}) -> {ST.mets(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)))) == T.bump(1n, ST.mets(cs)) : T.Metrics}:
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 0n, 1n), ST.pk(cs, 0n, 1n), pk_other(cs, 2n, DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)), 0n, 1n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0))) : {T.Counts{Con{_, Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 2n, 3n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 4n, 5n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 6n, 7n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 8n, 9n), Nil{}}}}}}} == T.bump(1n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 4n, 5n), ST.pk(cs, 4n, 5n), pk_other(cs, 2n, DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)), 4n, 5n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 2n, 3n), Con{_, Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 6n, 7n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 8n, 9n), Nil{}}}}}}} == T.bump(1n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 6n, 7n), ST.pk(cs, 6n, 7n), pk_other(cs, 2n, DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)), 6n, 7n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{_, Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 8n, 9n), Nil{}}}}}}} == T.bump(1n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 8n, 9n), ST.pk(cs, 8n, 9n), pk_other(cs, 2n, DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n)), 8n, 9n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{_, Nil{}}}}}}} == T.bump(1n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 2n, U32.is_eq(U32.inc(DST.lat(cs, 2n)), 0), DST.lat(cs, 3n), U32.inc(DST.lat(cs, 2n))), 2n, 3n), Word.inc(64n, ST.pk(cs, 2n, 3n)), pk_same(cs, 2n, hlen)) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{_, Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}} == T.bump(1n, ST.mets(cs)) : T.Metrics}
  {==}

def mets_bump_2(+cs: List<&2, U32>, +hlen: {Nat.is_lt(5n, SC.length(U32, cs)) == True{} : Bool}) -> {ST.mets(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)))) == T.bump(2n, ST.mets(cs)) : T.Metrics}:
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 0n, 1n), ST.pk(cs, 0n, 1n), pk_other(cs, 4n, DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)), 0n, 1n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0))) : {T.Counts{Con{_, Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 2n, 3n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 4n, 5n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 6n, 7n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 8n, 9n), Nil{}}}}}}} == T.bump(2n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 2n, 3n), ST.pk(cs, 2n, 3n), pk_other(cs, 4n, DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)), 2n, 3n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{_, Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 4n, 5n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 6n, 7n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 8n, 9n), Nil{}}}}}}} == T.bump(2n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 6n, 7n), ST.pk(cs, 6n, 7n), pk_other(cs, 4n, DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)), 6n, 7n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 4n, 5n), Con{_, Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 8n, 9n), Nil{}}}}}}} == T.bump(2n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 8n, 9n), ST.pk(cs, 8n, 9n), pk_other(cs, 4n, DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n)), 8n, 9n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{_, Nil{}}}}}}} == T.bump(2n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 4n, U32.is_eq(U32.inc(DST.lat(cs, 4n)), 0), DST.lat(cs, 5n), U32.inc(DST.lat(cs, 4n))), 4n, 5n), Word.inc(64n, ST.pk(cs, 4n, 5n)), pk_same(cs, 4n, hlen)) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{_, Con{ST.pk(cs, 6n, 7n), Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}} == T.bump(2n, ST.mets(cs)) : T.Metrics}
  {==}

def mets_bump_3(+cs: List<&2, U32>, +hlen: {Nat.is_lt(7n, SC.length(U32, cs)) == True{} : Bool}) -> {ST.mets(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)))) == T.bump(3n, ST.mets(cs)) : T.Metrics}:
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 0n, 1n), ST.pk(cs, 0n, 1n), pk_other(cs, 6n, DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)), 0n, 1n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0))) : {T.Counts{Con{_, Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 2n, 3n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 4n, 5n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 6n, 7n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 8n, 9n), Nil{}}}}}}} == T.bump(3n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 2n, 3n), ST.pk(cs, 2n, 3n), pk_other(cs, 6n, DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)), 2n, 3n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{_, Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 4n, 5n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 6n, 7n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 8n, 9n), Nil{}}}}}}} == T.bump(3n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 4n, 5n), ST.pk(cs, 4n, 5n), pk_other(cs, 6n, DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)), 4n, 5n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{_, Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 6n, 7n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 8n, 9n), Nil{}}}}}}} == T.bump(3n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 8n, 9n), ST.pk(cs, 8n, 9n), pk_other(cs, 6n, DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n)), 8n, 9n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 6n, 7n), Con{_, Nil{}}}}}}} == T.bump(3n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 6n, U32.is_eq(U32.inc(DST.lat(cs, 6n)), 0), DST.lat(cs, 7n), U32.inc(DST.lat(cs, 6n))), 6n, 7n), Word.inc(64n, ST.pk(cs, 6n, 7n)), pk_same(cs, 6n, hlen)) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{_, Con{ST.pk(cs, 8n, 9n), Nil{}}}}}}} == T.bump(3n, ST.mets(cs)) : T.Metrics}
  {==}

def mets_bump_4(+cs: List<&2, U32>, +hlen: {Nat.is_lt(9n, SC.length(U32, cs)) == True{} : Bool}) -> {ST.mets(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)))) == T.bump(4n, ST.mets(cs)) : T.Metrics}:
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 0n, 1n), ST.pk(cs, 0n, 1n), pk_other(cs, 8n, DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)), 0n, 1n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0))) : {T.Counts{Con{_, Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 2n, 3n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 4n, 5n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 6n, 7n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 8n, 9n), Nil{}}}}}}} == T.bump(4n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 2n, 3n), ST.pk(cs, 2n, 3n), pk_other(cs, 8n, DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)), 2n, 3n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{_, Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 4n, 5n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 6n, 7n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 8n, 9n), Nil{}}}}}}} == T.bump(4n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 4n, 5n), ST.pk(cs, 4n, 5n), pk_other(cs, 8n, DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)), 4n, 5n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{_, Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 6n, 7n), Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 8n, 9n), Nil{}}}}}}} == T.bump(4n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 6n, 7n), ST.pk(cs, 6n, 7n), pk_other(cs, 8n, DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n)), 6n, 7n, {==}, {==}, {==}, {==}, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0))) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{_, Con{ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 8n, 9n), Nil{}}}}}}} == T.bump(4n, ST.mets(cs)) : T.Metrics}
  %Equal.sym(Word(64n), ST.pk(sbt(cs, 8n, U32.is_eq(U32.inc(DST.lat(cs, 8n)), 0), DST.lat(cs, 9n), U32.inc(DST.lat(cs, 8n))), 8n, 9n), Word.inc(64n, ST.pk(cs, 8n, 9n)), pk_same(cs, 8n, hlen)) : {T.Counts{Con{ST.pk(cs, 0n, 1n), Con{ST.pk(cs, 2n, 3n), Con{ST.pk(cs, 4n, 5n), Con{ST.pk(cs, 6n, 7n), Con{_, Nil{}}}}}}} == T.bump(4n, ST.mets(cs)) : T.Metrics}
  {==}
