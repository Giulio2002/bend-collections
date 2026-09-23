import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32.bend as U
import ../lib/u32alg.bend as A
import ../lib/array.bend as AR
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ../../src/containers/internal/dlist_storage.bend as R
import ../hash_table/insu.bend as IU
import ../hash_table/state.bend as HT
import ../hash_table/table.bend as TB
import ../hash_table/insa.bend as IA
import ../lru/state.bend as LST
import ../lru/meta.bend as MT
import ../lru/tfind.bend as TF
import ../lru/lists.bend as LS
import ../lru/dll.bend as DL
import ./state.bend as ST
import ./links.bend as LK

# Relinking: the writes of an insertion between two neighbours and of an
# unlink, over the prev and next lists.


# ---- writes at the first id of b / the last id of a ----

# the first id of b is in xs
def fstin(b: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{+b0, t}:
      HT.memn(b0, xs)

# the last id of a is in xs
def lastin(a: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case Con{+a0, +t}:
      HT.memn(DL.lastn(t, a0), xs)

def upd_first(+pl: List<&2, U32>, b: List<&2, Nat>, +v: U32) -> List<&2, U32>:
  match b:
    case Nil{}:
      pl
    case Con{+b0, t}:
      SC.update(U32, pl, b0, v)

def upd_last(+nl: List<&2, U32>, a: List<&2, Nat>, +v: U32) -> List<&2, U32>:
  match a:
    case Nil{}:
      nl
    case Con{+a0, +t}:
      SC.update(U32, nl, DL.lastn(t, a0), v)

def tu_first(+d: Nat, +tr: AR.Tree<U32>, b: List<&2, Nat>, +v: U32) -> AR.Tree<U32>:
  match b:
    case Nil{}:
      tr
    case Con{+b0, t}:
      AR.upd(U32, d, tr, b0, v)

def tu_last(+d: Nat, +tr: AR.Tree<U32>, a: List<&2, Nat>, +v: U32) -> AR.Tree<U32>:
  match a:
    case Nil{}:
      tr
    case Con{+a0, +t}:
      AR.upd(U32, d, tr, DL.lastn(t, a0), v)

# ---- bounds ----

def hd1(+d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}) -> {Nat.is_lt(1n+d, 32n) == True{} : Bool}:
  N.lt_trans(d, 30n, 31n, hd, {==})

def hd0(+d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.lt_trans(d, 30n, 32n, hd, {==})

def self_in(+b: Nat, +t: List<&2, Nat>) -> {HT.memn(b, Con{b, t}) == True{} : Bool}:
  DL.or_tl(Nat.is_eq(b, b), HT.memn(b, t), N.is_eq_refl(b))


def slok_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hy: {Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +hm: {Bool.or(c, HT.memn(x, t)) == True{} : Bool}, rec: @hm2: {HT.memn(x, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(z, fr), ST.live(T, vl, z)) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
    case False{}:
      rec(hm)

# a member of a slok list is below fr and live
def slok_mem(~T: Data, +x: Nat, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}, +hm: {HT.memn(x, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}, L.false_true(hm))
    case Con{+y, +t}:
      +hy = L.and_left(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      slok_c(~T, x, y, t, fr, vl, hy, Nat.is_eq(y, x), {==}, hm, hm2 => slok_mem(~T, x, t, fr, vl, ht, hm2))

def flok_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hy: {Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +hm: {Bool.or(c, HT.memn(x, t)) == True{} : Bool}, rec: @hm2: {HT.memn(x, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(z, fr), Bool.not(ST.live(T, vl, z))) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
    case False{}:
      rec(hm)

# a member of a flok list is below fr and vacant
def flok_mem(~T: Data, +x: Nat, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +h: {ST.flok(~T, xs, fr, vl) == True{} : Bool}, +hm: {HT.memn(x, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}, L.false_true(hm))
    case Con{+y, +t}:
      +hy = L.and_left(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h)
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h)
      flok_c(~T, x, y, t, fr, vl, hy, Nat.is_eq(y, x), {==}, hm, hm2 => flok_mem(~T, x, t, fr, vl, ht, hm2))

def slok_app(~T: Data, +a: List<&2, Nat>, +b: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>) -> {ST.slok(~T, SC.append(Nat, a, b), fr, vl) == Bool.and(ST.slok(~T, a, fr, vl), ST.slok(~T, b, fr, vl)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +ih = slok_app(~T, t, b, fr, vl)
      Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, SC.append(Nat, t, b), fr, vl)), Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), Bool.and(ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl))), Bool.and(Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl)), ST.slok(~T, b, fr, vl)), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), z), ST.slok(~T, SC.append(Nat, t, b), fr, vl), Bool.and(ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl)), ih), LS.and_assoc(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl)))

# a live id is not on a vacant list
def dj_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == True{} : Bool}, +hy: {Bool.not(ST.live(T, vl, y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +ih: {HT.memn(x, t) == False{} : Bool}) -> {Bool.or(c, HT.memn(x, t)) == False{} : Bool}:
  match c:
    case True{}:
      +hy2 = L.subst(Nat, z => {Bool.not(ST.live(T, vl, z)) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
      Empty.absurd({Bool.or(True{}, HT.memn(x, t)) == False{} : Bool}, L.true_not_false(ST.live(T, vl, x), hx, L.not_true(ST.live(T, vl, x), hy2)))
    case False{}:
      ih

def live_nf(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == True{} : Bool}, +h: {ST.flok(~T, ys, fr, vl) == True{} : Bool}) -> {HT.memn(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_right(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y)), L.and_left(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h)
      dj_c(~T, x, y, t, vl, hx, hy, Nat.is_eq(y, x), {==}, live_nf(~T, x, t, fr, vl, hx, ht))

# an id at or above fr is on no slok list
def hi_c(+x: Nat, +y: Nat, +fr: Nat, +hy: {Nat.is_lt(y, fr) == True{} : Bool}, +hx: {Nat.is_le(fr, x) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +m: Bool, +ih: {m == False{} : Bool}) -> {Bool.or(c, m) == False{} : Bool}:
  match c:
    case True{}:
      +hy2 = L.subst(Nat, z => {Nat.is_lt(z, fr) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
      Empty.absurd({Bool.or(True{}, m) == False{} : Bool}, N.lt_ne(x, x, N.lt_le_trans(x, fr, x, hy2, hx), {==}))
    case False{}:
      ih

def hi_ns(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {Nat.is_le(fr, x) == True{} : Bool}, +h: {ST.slok(~T, ys, fr, vl) == True{} : Bool}) -> {HT.memn(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_left(Nat.is_lt(y, fr), ST.live(T, vl, y), L.and_left(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      hi_c(x, y, fr, hy, hx, Nat.is_eq(y, x), {==}, HT.memn(x, t), hi_ns(~T, x, t, fr, vl, hx, ht))

def hi_nf(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {Nat.is_le(fr, x) == True{} : Bool}, +h: {ST.flok(~T, ys, fr, vl) == True{} : Bool}) -> {HT.memn(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_left(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y)), L.and_left(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h)
      hi_c(x, y, fr, hy, hx, Nat.is_eq(y, x), {==}, HT.memn(x, t), hi_nf(~T, x, t, fr, vl, hx, ht))

# ---- first/last bounds ----

def fstlt(b: List<&2, Nat>, +m: Nat) -> Bool:
  match b:
    case Nil{}:
      True{}
    case Con{+b0, t}:
      Nat.is_lt(b0, m)

def lastlt(a: List<&2, Nat>, +m: Nat) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{+a0, +t}:
      Nat.is_lt(DL.lastn(t, a0), m)

def fstlt_of(~T: Data, +b: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +m: Nat, +hfr: {Nat.is_le(fr, m) == True{} : Bool}, +h: {ST.slok(~T, b, fr, vl) == True{} : Bool}) -> {fstlt(b, m) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      N.lt_le_trans(b0, fr, m, L.and_left(Nat.is_lt(b0, fr), ST.live(T, vl, b0), slok_mem(~T, b0, Con{b0, t}, fr, vl, h, self_in(b0, t))), hfr)

def lastlt_of(~T: Data, +a: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +m: Nat, +hfr: {Nat.is_le(fr, m) == True{} : Bool}, +h: {ST.slok(~T, a, fr, vl) == True{} : Bool}) -> {lastlt(a, m) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      N.lt_le_trans(DL.lastn(t, a0), fr, m, L.and_left(Nat.is_lt(DL.lastn(t, a0), fr), ST.live(T, vl, DL.lastn(t, a0)), slok_mem(~T, DL.lastn(t, a0), Con{a0, t}, fr, vl, h, DL.lastn_mem(t, a0))), hfr)

# ---- links of ids below 2^d ----

def lnk_nz(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.pow2(d)) == True{} : Bool}) -> {U32.is_eq(LST.lnk(b), 0) == False{} : Bool}:
  +hk = N.lt_le(d, 32n, hd0(d, hd))
  +e1 = U.to_nat_from_nat(b, d, hk, hb)
  +hb2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, b, UD.v(U32.from_nat(b)), Equal.sym(Nat, UD.v(U32.from_nat(b)), b, e1), hb)
  IU.link_nz(one, h1, U32.from_nat(b), IU.bound32(one, h1, UD.v(U32.from_nat(b)), d, hd1(d, hd), hb2))

def slot_lnk(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.pow2(d)) == True{} : Bool}) -> {UD.v(R.slot(LST.lnk(b))) == b : Nat}:
  TF.slot_lnk(one, h1, b, d, hd1(d, hd), hb)


# the write at the id of a link
def sn_c(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b0: Nat, +hb: {Nat.is_lt(b0, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LST.lnk(b0), v) == AR.thaw(U32, AR.upd(U32, d, tr, b0, v)) : Array<U32>}:
  +i = R.slot(LST.lnk(b0))
  +es = slot_lnk(one, h1, b0, d, hd, hb)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, b0, UD.v(i), Equal.sym(Nat, UD.v(i), b0, es), hb)
  +e1 = Equal.cong(Bool, Array<U32>, z => R.set_next_go(AR.thaw(U32, tr), LST.lnk(b0), v, z), U32.is_eq(LST.lnk(b0), 0), False{}, lnk_nz(one, h1, b0, d, hd, hb))
  +e2 = MT.uset_a(d, hd0(d, hd), tr, pf, i, hi, v)
  +e3 = Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, tr, z, v)), UD.v(i), b0, es)
  Equal.trans(Array<U32>, R.set_next(AR.thaw(U32, tr), LST.lnk(b0), v), Array.set(U32, AR.thaw(U32, tr), i, v), AR.thaw(U32, AR.upd(U32, d, tr, b0, v)), e1, Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, tr), i, v), AR.thaw(U32, AR.upd(U32, d, tr, UD.v(i), v)), AR.thaw(U32, AR.upd(U32, d, tr, b0, v)), e2, e3))

# set_next at b's first link
def sn_first(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +hb: {fstlt(b, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LST.fst_or(b, 0), v) == AR.thaw(U32, tu_first(d, tr, b, v)) : Array<U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      sn_c(one, h1, d, hd, tr, pf, b0, hb, v)

# set_next at a's last link
def sn_last(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +ha: {lastlt(a, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LST.last_or(a, 0), v) == AR.thaw(U32, tu_last(d, tr, a, v)) : Array<U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      +e0 = Equal.cong(U32, Array<U32>, w => R.set_next(AR.thaw(U32, tr), w, v), LST.last_or(t, LST.lnk(a0)), LST.lnk(DL.lastn(t, a0)), DL.last_lnk(t, a0))
      Equal.trans(Array<U32>, R.set_next(AR.thaw(U32, tr), LST.last_or(t, LST.lnk(a0)), v), R.set_next(AR.thaw(U32, tr), LST.lnk(DL.lastn(t, a0)), v), AR.thaw(U32, AR.upd(U32, d, tr, DL.lastn(t, a0), v)), e0, sn_c(one, h1, d, hd, tr, pf, DL.lastn(t, a0), ha, v))

def tf_p(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +v: U32) -> {AR.perfect(U32, d, tu_first(d, tr, b, v)) == True{} : Bool}:
  match b:
    case Nil{}:
      pf
    case Con{+b0, +t}:
      MT.uset_p(d, tr, pf, b0, v)

def tl_p(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +v: U32) -> {AR.perfect(U32, d, tu_last(d, tr, a, v)) == True{} : Bool}:
  match a:
    case Nil{}:
      pf
    case Con{+a0, +t}:
      MT.uset_p(d, tr, pf, DL.lastn(t, a0), v)

def tf_s(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +hb: {fstlt(b, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {AR.slots(U32, tu_first(d, tr, b, v)) == upd_first(AR.slots(U32, tr), b, v) : List<&2, U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      MT.uset_s(d, tr, pf, b0, hb, v)

def tl_s(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +ha: {lastlt(a, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {AR.slots(U32, tu_last(d, tr, a, v)) == upd_last(AR.slots(U32, tr), a, v) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      MT.uset_s(d, tr, pf, DL.lastn(t, a0), ha, v)

# ---- frames ----

def seg_ffp(+pl: List<&2, U32>, +nl: List<&2, U32>, +b: List<&2, Nat>, +v: U32, +xs: List<&2, Nat>, +p: U32, +q: U32, +h: {fstin(b, xs) == False{} : Bool}) -> {ST.seg(upd_first(pl, b, v), nl, xs, p, q) == ST.seg(pl, nl, xs, p, q) : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      LK.seg_fp(pl, nl, b0, v, xs, p, q, h)

def seg_lfn(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +xs: List<&2, Nat>, +p: U32, +q: U32, +h: {lastin(a, xs) == False{} : Bool}) -> {ST.seg(pl, upd_last(nl, a, v), xs, p, q) == ST.seg(pl, nl, xs, p, q) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      LK.seg_fn(pl, nl, DL.lastn(t, a0), v, xs, p, q, h)

def fll_lfn(+nl: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +fl: List<&2, Nat>, +h: {lastin(a, fl) == False{} : Bool}) -> {ST.fll(upd_last(nl, a, v), fl) == ST.fll(nl, fl) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      LK.fll_fn(nl, DL.lastn(t, a0), v, fl, h)

def ne1(+n: Nat, +x: Nat, +h: {HT.memn(x, Con{n, Nil{}}) == False{} : Bool}) -> {Nat.is_eq(x, n) == False{} : Bool}:
  DL.ne_sym(n, x, DL.or_ff_l(Nat.is_eq(n, x), False{}, h))

def nth_uf(+pl: List<&2, U32>, +b: List<&2, Nat>, +v: U32, +n: Nat, +h: {fstin(b, Con{n, Nil{}}) == False{} : Bool}) -> {TB.nth0(upd_first(pl, b, v), n) == TB.nth0(pl, n) : U32}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      IA.nth0_upd_other(pl, b0, n, v, ne1(n, b0, h))

def nth_ul(+nl: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +n: Nat, +h: {lastin(a, Con{n, Nil{}}) == False{} : Bool}) -> {TB.nth0(upd_last(nl, a, v), n) == TB.nth0(nl, n) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      IA.nth0_upd_other(nl, DL.lastn(t, a0), n, v, ne1(n, DL.lastn(t, a0), h))

# ---- re-targeting ----

def seg_ufp(+pl: List<&2, U32>, +nl: List<&2, U32>, +b: List<&2, Nat>, +x: U32, +q: U32, +y: U32, +hs: {ST.seg(pl, nl, b, x, q) == True{} : Bool}, +hn: {LST.nodupn(b) == True{} : Bool}, +hl: {fstlt(b, SC.length(U32, pl)) == True{} : Bool}) -> {ST.seg(upd_first(pl, b, y), nl, b, y, q) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      LK.segp(pl, nl, b0, t, x, q, y, hs, hn, hl)

def seg_ulq(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +p: U32, +x: U32, +y: U32, +hs: {ST.seg(pl, nl, a, p, x) == True{} : Bool}, +hn: {LST.nodupn(a) == True{} : Bool}, +hl: {lastlt(a, SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(pl, upd_last(nl, a, y), a, p, y) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      LK.segq(pl, nl, t, a0, p, x, y, hs, hn, hl)

# ---- rewriting a truth ----

# b1 is true when b1 == b2 and b2 is
def by_eq(+b1: Bool, +b2: Bool, +e: {b1 == b2 : Bool}, +h: {b2 == True{} : Bool}) -> {b1 == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, b2, b1, Equal.sym(Bool, b1, b2, e), h)

# b2 is true when b1 == b2 and b1 is
def to_eq(+b1: Bool, +b2: Bool, +e: {b1 == b2 : Bool}, +h: {b1 == True{} : Bool}) -> {b2 == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, b1, b2, e, h)

def u_is(+x: U32, +y: U32, +e: {x == y : U32}) -> {U32.is_eq(x, y) == True{} : Bool}:
  L.subst(U32, z => {U32.is_eq(z, y) == True{} : Bool}, y, x, Equal.sym(U32, x, y, e), DL.u_refl(y))

# ---- disjointness of the parts of a list without repeats ----

# a ++ s :: b: b's first id is not in a
def fin_dj(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hn: {LST.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {fstin(b, a) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      LS.nd_dj(a, Con{s, Con{b0, t}}, hn, b0, DL.or_tr(Nat.is_eq(s, b0), HT.memn(b0, Con{b0, t}), self_in(b0, t)))

# a ++ s :: b: a's last id is not in b
def lin_dj(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hn: {LST.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {lastin(a, b) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      DL.or_ff_r(Nat.is_eq(s, DL.lastn(t, a0)), HT.memn(DL.lastn(t, a0), b), LS.nd_dj2(Con{a0, t}, Con{s, b}, hn, DL.lastn(t, a0), DL.lastn_mem(t, a0)))

# a ++ b: b's first id is not in a
def fin_dj2(+a: List<&2, Nat>, +b: List<&2, Nat>, +hn: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {fstin(b, a) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      LS.nd_dj(a, Con{b0, t}, hn, b0, self_in(b0, t))

# a ++ b: a's last id is not in b
def lin_dj2(+a: List<&2, Nat>, +b: List<&2, Nat>, +hn: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {lastin(a, b) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      LS.nd_dj2(Con{a0, t}, b, hn, DL.lastn(t, a0), DL.lastn_mem(t, a0))

def or_f(+x: Bool, +h: {x == False{} : Bool}) -> {Bool.or(x, False{}) == False{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, False{}) == False{} : Bool}, False{}, x, Equal.sym(Bool, x, False{}, h), {==})

# n off b: b's first id is not n
def fin1(+b: List<&2, Nat>, +n: Nat, +h: {HT.memn(n, b) == False{} : Bool}) -> {fstin(b, Con{n, Nil{}}) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      or_f(Nat.is_eq(n, b0), DL.ne_sym(b0, n, DL.or_ff_l(Nat.is_eq(b0, n), HT.memn(n, t), h)))

# n off a: a's last id is not n
def lin1(+a: List<&2, Nat>, +n: Nat, +h: {HT.memn(n, a) == False{} : Bool}) -> {lastin(a, Con{n, Nil{}}) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      or_f(Nat.is_eq(n, DL.lastn(t, a0)), DL.ne_sym(DL.lastn(t, a0), n, DL.ne_mem(n, DL.lastn(t, a0), Con{a0, t}, DL.not_f(HT.memn(n, Con{a0, t}), h), DL.lastn_mem(t, a0))))


# THEOREM (unlink): s between a and b; b's first prev becomes a's last link
# and a's last next becomes b's first link: a ++ b is linked
def unl_seg(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}, +hn: {LST.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hlp: {fstlt(b, SC.length(U32, pl)) == True{} : Bool}, +hln: {lastlt(a, SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(upd_first(pl, b, LST.last_or(a, 0)), upd_last(nl, a, LST.fst_or(b, 0)), SC.append(Nat, a, b), 0, 0) == True{} : Bool}:
  +pl2 = upd_first(pl, b, LST.last_or(a, 0))
  +nl2 = upd_last(nl, a, LST.fst_or(b, 0))
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsA = L.and_left(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0), hsp)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0), hsp)
  +hsB = L.and_right(U32.is_eq(TB.nth0(nl, s), LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.lnk(s), 0), L.and_right(U32.is_eq(TB.nth0(pl, s), LST.last_or(a, 0)), Bool.and(U32.is_eq(TB.nth0(nl, s), LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.lnk(s), 0)), hsS))
  +hnS = LS.nd_r(a, Con{s, b}, hn)
  +hA1 = seg_ulq(pl, nl, a, 0, LST.lnk(s), LST.fst_or(b, 0), hsA, LS.nd_l(a, Con{s, b}, hn), hln)
  +hA = by_eq(ST.seg(pl2, nl2, a, 0, LST.fst_or(b, 0)), ST.seg(pl, nl2, a, 0, LST.fst_or(b, 0)), seg_ffp(pl, nl2, b, LST.last_or(a, 0), a, 0, LST.fst_or(b, 0), fin_dj(a, s, b, hn)), hA1)
  +hB1 = seg_ufp(pl, nl, b, LST.lnk(s), 0, LST.last_or(a, 0), hsB, L.and_right(Bool.not(HT.memn(s, b)), LST.nodupn(b), hnS), hlp)
  +hB = by_eq(ST.seg(pl2, nl2, b, LST.last_or(a, 0), 0), ST.seg(pl2, nl, b, LST.last_or(a, 0), 0), seg_lfn(pl2, nl, a, LST.fst_or(b, 0), b, LST.last_or(a, 0), 0, lin_dj(a, s, b, hn)), hB1)
  by_eq(ST.seg(pl2, nl2, SC.append(Nat, a, b), 0, 0), Bool.and(ST.seg(pl2, nl2, a, 0, LST.fst_or(b, 0)), ST.seg(pl2, nl2, b, LST.last_or(a, 0), 0)), LK.seg_app(pl2, nl2, a, b, 0, 0), L.and_intro(ST.seg(pl2, nl2, a, 0, LST.fst_or(b, 0)), ST.seg(pl2, nl2, b, LST.last_or(a, 0), 0), hA, hB))

# ... and s's own links are a's last and b's first
def unl_p(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}) -> {TB.nth0(pl, s) == LST.last_or(a, 0) : U32}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0), hsp)
  A.eq_of(TB.nth0(pl, s), LST.last_or(a, 0), L.and_left(U32.is_eq(TB.nth0(pl, s), LST.last_or(a, 0)), Bool.and(U32.is_eq(TB.nth0(nl, s), LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.lnk(s), 0)), hsS))

def unl_n(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}) -> {TB.nth0(nl, s) == LST.fst_or(b, 0) : U32}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LST.lnk(s)), ST.seg(pl, nl, Con{s, b}, LST.last_or(a, 0), 0), hsp)
  +hr = L.and_right(U32.is_eq(TB.nth0(pl, s), LST.last_or(a, 0)), Bool.and(U32.is_eq(TB.nth0(nl, s), LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.lnk(s), 0)), hsS)
  A.eq_of(TB.nth0(nl, s), LST.fst_or(b, 0), L.and_left(U32.is_eq(TB.nth0(nl, s), LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.lnk(s), 0), hr))


# THEOREM (insert between): n off a ++ b takes a's last as prev and b's
# first as next, and becomes their next and prev: a ++ n :: b is linked
def ins_seg(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +hs: {ST.seg(pl, nl, SC.append(Nat, a, b), 0, 0) == True{} : Bool}, +hn: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +hna: {HT.memn(n, a) == False{} : Bool}, +hnb: {HT.memn(n, b) == False{} : Bool}, +hlp: {Nat.is_lt(n, SC.length(U32, pl)) == True{} : Bool}, +hlq: {Nat.is_lt(n, SC.length(U32, nl)) == True{} : Bool}, +hfp: {fstlt(b, SC.length(U32, SC.update(U32, pl, n, LST.last_or(a, 0)))) == True{} : Bool}, +hfq: {lastlt(a, SC.length(U32, SC.update(U32, nl, n, LST.fst_or(b, 0)))) == True{} : Bool}) -> {ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), SC.append(Nat, a, Con{n, b}), 0, 0) == True{} : Bool}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, b), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, b, 0, 0), hs)
  +hsA = L.and_left(ST.seg(pl, nl, a, 0, LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.last_or(a, 0), 0), hsp)
  +hsB = L.and_right(ST.seg(pl, nl, a, 0, LST.fst_or(b, 0)), ST.seg(pl, nl, b, LST.last_or(a, 0), 0), hsp)
  +hA1 = by_eq(ST.seg(pl, SC.update(U32, nl, n, LST.fst_or(b, 0)), a, 0, LST.fst_or(b, 0)), ST.seg(pl, nl, a, 0, LST.fst_or(b, 0)), LK.seg_fn(pl, nl, n, LST.fst_or(b, 0), a, 0, LST.fst_or(b, 0), hna), hsA)
  +hA2 = seg_ulq(pl, SC.update(U32, nl, n, LST.fst_or(b, 0)), a, 0, LST.fst_or(b, 0), LST.lnk(n), hA1, LS.nd_l(a, b, hn), hfq)
  +hA3 = by_eq(ST.seg(SC.update(U32, pl, n, LST.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), ST.seg(pl, upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), LK.seg_fp(pl, upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), n, LST.last_or(a, 0), a, 0, LST.lnk(n), hna), hA2)
  +hA = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), ST.seg(SC.update(U32, pl, n, LST.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), seg_ffp(SC.update(U32, pl, n, LST.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), b, LST.lnk(n), a, 0, LST.lnk(n), fin_dj2(a, b, hn)), hA3)
  +ep = Equal.trans(U32, TB.nth0(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), n), TB.nth0(SC.update(U32, pl, n, LST.last_or(a, 0)), n), LST.last_or(a, 0), nth_uf(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n), n, fin1(b, n, hnb)), IA.nth0_upd_same(pl, n, LST.last_or(a, 0), hlp))
  +eq = Equal.trans(U32, TB.nth0(upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), n), TB.nth0(SC.update(U32, nl, n, LST.fst_or(b, 0)), n), LST.fst_or(b, 0), nth_ul(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n), n, lin1(a, n, hna)), IA.nth0_upd_same(nl, n, LST.fst_or(b, 0), hlq))
  +hB1 = by_eq(ST.seg(SC.update(U32, pl, n, LST.last_or(a, 0)), nl, b, LST.last_or(a, 0), 0), ST.seg(pl, nl, b, LST.last_or(a, 0), 0), LK.seg_fp(pl, nl, n, LST.last_or(a, 0), b, LST.last_or(a, 0), 0, hnb), hsB)
  +hB2 = seg_ufp(SC.update(U32, pl, n, LST.last_or(a, 0)), nl, b, LST.last_or(a, 0), 0, LST.lnk(n), hB1, LS.nd_r(a, b, hn), hfp)
  +hB3 = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), SC.update(U32, nl, n, LST.fst_or(b, 0)), b, LST.lnk(n), 0), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), nl, b, LST.lnk(n), 0), LK.seg_fn(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), nl, n, LST.fst_or(b, 0), b, LST.lnk(n), 0, hnb), hB2)
  +hB = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), b, LST.lnk(n), 0), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), SC.update(U32, nl, n, LST.fst_or(b, 0)), b, LST.lnk(n), 0), seg_lfn(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n), b, LST.lnk(n), 0, lin_dj2(a, b, hn)), hB3)
  +hN = L.and_intro(U32.is_eq(TB.nth0(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), n), LST.last_or(a, 0)), Bool.and(U32.is_eq(TB.nth0(upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), n), LST.fst_or(b, 0)), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), b, LST.lnk(n), 0)), u_is(TB.nth0(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), n), LST.last_or(a, 0), ep), L.and_intro(U32.is_eq(TB.nth0(upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), n), LST.fst_or(b, 0)), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), b, LST.lnk(n), 0), u_is(TB.nth0(upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), n), LST.fst_or(b, 0), eq), hB))
  by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), SC.append(Nat, a, Con{n, b}), 0, 0), Bool.and(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), Con{n, b}, LST.last_or(a, 0), 0)), LK.seg_app(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, Con{n, b}, 0, 0), L.and_intro(ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), a, 0, LST.lnk(n)), ST.seg(upd_first(SC.update(U32, pl, n, LST.last_or(a, 0)), b, LST.lnk(n)), upd_last(SC.update(U32, nl, n, LST.fst_or(b, 0)), a, LST.lnk(n)), Con{n, b}, LST.last_or(a, 0), 0), hA, hN))
