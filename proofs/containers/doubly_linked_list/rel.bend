import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as A
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/internal/dlist_storage.bend as R
import ./state.bend as ST
import ./links.bend as LK
import ../../lib/nat_list.bend as NL
import ../../lib/links.bend as LKx
import ../../lib/words32.bend as W32
import ../../lib/u32_tree.bend as UT

# Relinking: the writes of an insertion between two neighbours and of an
# unlink, over the prev and next lists.


# ---- writes at the first id of b / the last id of a ----

# the first id of b is in xs
def fstin(b: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{+b0, t}:
      NL.memn(b0, xs)

# the last id of a is in xs
def lastin(a: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case Con{+a0, +t}:
      NL.memn(NL.lastn(t, a0), xs)

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
      SC.update(U32, nl, NL.lastn(t, a0), v)

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
      AR.upd(U32, d, tr, NL.lastn(t, a0), v)

# ---- bounds ----

def hd1(+d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}) -> {Nat.is_lt(1n+d, 32n) == True{} : Bool}:
  N.lt_trans(d, 30n, 31n, hd, {==})

def hd0(+d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.lt_trans(d, 30n, 32n, hd, {==})

def self_in(+b: Nat, +t: List<&2, Nat>) -> {NL.memn(b, Con{b, t}) == True{} : Bool}:
  NL.or_tl(Nat.is_eq(b, b), NL.memn(b, t), N.is_eq_refl(b))


def slok_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hy: {Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +hm: {Bool.or(c, NL.memn(x, t)) == True{} : Bool}, rec: @hm2: {NL.memn(x, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(z, fr), ST.live(T, vl, z)) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
    case False{}:
      rec(hm)

# a member of a slok list is below fr and live
def slok_mem(~T: Data, +x: Nat, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}, +hm: {NL.memn(x, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)) == True{} : Bool}, L.false_true(hm))
    case Con{+y, +t}:
      +hy = L.and_left(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      slok_c(~T, x, y, t, fr, vl, hy, Nat.is_eq(y, x), {==}, hm, hm2 => slok_mem(~T, x, t, fr, vl, ht, hm2))

def flok_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hy: {Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +hm: {Bool.or(c, NL.memn(x, t)) == True{} : Bool}, rec: @hm2: {NL.memn(x, t) == True{} : Bool} -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.and(Nat.is_lt(z, fr), Bool.not(ST.live(T, vl, z))) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
    case False{}:
      rec(hm)

# a member of a flok list is below fr and vacant
def flok_mem(~T: Data, +x: Nat, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +h: {ST.flok(~T, xs, fr, vl) == True{} : Bool}, +hm: {NL.memn(x, xs) == True{} : Bool}) -> {Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(T, vl, x))) == True{} : Bool}:
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
      Equal.trans(Bool, Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, SC.append(Nat, t, b), fr, vl)), Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), Bool.and(ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl))), Bool.and(Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl)), ST.slok(~T, b, fr, vl)), Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), z), ST.slok(~T, SC.append(Nat, t, b), fr, vl), Bool.and(ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl)), ih), NL.and_assoc(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), ST.slok(~T, b, fr, vl)))

# a live id is not on a vacant list
def dj_c(~T: Data, +x: Nat, +y: Nat, +t: List<&2, Nat>, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == True{} : Bool}, +hy: {Bool.not(ST.live(T, vl, y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}, +ih: {NL.memn(x, t) == False{} : Bool}) -> {Bool.or(c, NL.memn(x, t)) == False{} : Bool}:
  match c:
    case True{}:
      +hy2 = L.subst(Nat, z => {Bool.not(ST.live(T, vl, z)) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), hy)
      Empty.absurd({Bool.or(True{}, NL.memn(x, t)) == False{} : Bool}, L.true_not_false(ST.live(T, vl, x), hx, L.not_true(ST.live(T, vl, x), hy2)))
    case False{}:
      ih

def live_nf(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {ST.live(T, vl, x) == True{} : Bool}, +h: {ST.flok(~T, ys, fr, vl) == True{} : Bool}) -> {NL.memn(x, ys) == False{} : Bool}:
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

def hi_ns(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {Nat.is_le(fr, x) == True{} : Bool}, +h: {ST.slok(~T, ys, fr, vl) == True{} : Bool}) -> {NL.memn(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_left(Nat.is_lt(y, fr), ST.live(T, vl, y), L.and_left(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), ST.live(T, vl, y)), ST.slok(~T, t, fr, vl), h)
      hi_c(x, y, fr, hy, hx, Nat.is_eq(y, x), {==}, NL.memn(x, t), hi_ns(~T, x, t, fr, vl, hx, ht))

def hi_nf(~T: Data, +x: Nat, +ys: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +hx: {Nat.is_le(fr, x) == True{} : Bool}, +h: {ST.flok(~T, ys, fr, vl) == True{} : Bool}) -> {NL.memn(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = L.and_left(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y)), L.and_left(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(y, fr), Bool.not(ST.live(T, vl, y))), ST.flok(~T, t, fr, vl), h)
      hi_c(x, y, fr, hy, hx, Nat.is_eq(y, x), {==}, NL.memn(x, t), hi_nf(~T, x, t, fr, vl, hx, ht))

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
      Nat.is_lt(NL.lastn(t, a0), m)

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
      N.lt_le_trans(NL.lastn(t, a0), fr, m, L.and_left(Nat.is_lt(NL.lastn(t, a0), fr), ST.live(T, vl, NL.lastn(t, a0)), slok_mem(~T, NL.lastn(t, a0), Con{a0, t}, fr, vl, h, NL.lastn_mem(t, a0))), hfr)

# ---- links of ids below 2^d ----

def lnk_nz(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.pow2(d)) == True{} : Bool}) -> {U32.is_eq(LKx.lnk(b), 0) == False{} : Bool}:
  +hk = N.lt_le(d, 32n, hd0(d, hd))
  +e1 = U.to_nat_from_nat(b, d, hk, hb)
  +hb2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, b, UD.v(U32.from_nat(b)), Equal.sym(Nat, UD.v(U32.from_nat(b)), b, e1), hb)
  W32.link_nz(one, h1, U32.from_nat(b), W32.bound32(one, h1, UD.v(U32.from_nat(b)), d, hd1(d, hd), hb2))

def slot_lnk(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.pow2(d)) == True{} : Bool}) -> {UD.v(R.slot(LKx.lnk(b))) == b : Nat}:
  LKx.slot_lnk(one, h1, b, d, hd1(d, hd), hb)


# the write at the id of a link
def sn_c(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b0: Nat, +hb: {Nat.is_lt(b0, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LKx.lnk(b0), v) == AR.thaw(U32, AR.upd(U32, d, tr, b0, v)) : Array<U32>}:
  +i = R.slot(LKx.lnk(b0))
  +es = slot_lnk(one, h1, b0, d, hd, hb)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, b0, UD.v(i), Equal.sym(Nat, UD.v(i), b0, es), hb)
  +e1 = Equal.cong(Bool, Array<U32>, z => R.set_next_go(AR.thaw(U32, tr), LKx.lnk(b0), v, z), U32.is_eq(LKx.lnk(b0), 0), False{}, lnk_nz(one, h1, b0, d, hd, hb))
  +e2 = UT.uset_a(d, hd0(d, hd), tr, pf, i, hi, v)
  +e3 = Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, tr, z, v)), UD.v(i), b0, es)
  Equal.trans(Array<U32>, R.set_next(AR.thaw(U32, tr), LKx.lnk(b0), v), Array.set(U32, AR.thaw(U32, tr), i, v), AR.thaw(U32, AR.upd(U32, d, tr, b0, v)), e1, Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, tr), i, v), AR.thaw(U32, AR.upd(U32, d, tr, UD.v(i), v)), AR.thaw(U32, AR.upd(U32, d, tr, b0, v)), e2, e3))

# set_next at b's first link
def sn_first(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +hb: {fstlt(b, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LKx.fst_or(b, 0), v) == AR.thaw(U32, tu_first(d, tr, b, v)) : Array<U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      sn_c(one, h1, d, hd, tr, pf, b0, hb, v)

# set_next at a's last link
def sn_last(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +ha: {lastlt(a, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {R.set_next(AR.thaw(U32, tr), LKx.last_or(a, 0), v) == AR.thaw(U32, tu_last(d, tr, a, v)) : Array<U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      +e0 = Equal.cong(U32, Array<U32>, w => R.set_next(AR.thaw(U32, tr), w, v), LKx.last_or(t, LKx.lnk(a0)), LKx.lnk(NL.lastn(t, a0)), LKx.last_lnk(t, a0))
      Equal.trans(Array<U32>, R.set_next(AR.thaw(U32, tr), LKx.last_or(t, LKx.lnk(a0)), v), R.set_next(AR.thaw(U32, tr), LKx.lnk(NL.lastn(t, a0)), v), AR.thaw(U32, AR.upd(U32, d, tr, NL.lastn(t, a0), v)), e0, sn_c(one, h1, d, hd, tr, pf, NL.lastn(t, a0), ha, v))

def tf_p(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +v: U32) -> {AR.perfect(U32, d, tu_first(d, tr, b, v)) == True{} : Bool}:
  match b:
    case Nil{}:
      pf
    case Con{+b0, +t}:
      UT.uset_p(d, tr, pf, b0, v)

def tl_p(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +v: U32) -> {AR.perfect(U32, d, tu_last(d, tr, a, v)) == True{} : Bool}:
  match a:
    case Nil{}:
      pf
    case Con{+a0, +t}:
      UT.uset_p(d, tr, pf, NL.lastn(t, a0), v)

def tf_s(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +b: List<&2, Nat>, +hb: {fstlt(b, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {AR.slots(U32, tu_first(d, tr, b, v)) == upd_first(AR.slots(U32, tr), b, v) : List<&2, U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      UT.uset_s(d, tr, pf, b0, hb, v)

def tl_s(+d: Nat, +tr: AR.Tree<U32>, +pf: {AR.perfect(U32, d, tr) == True{} : Bool}, +a: List<&2, Nat>, +ha: {lastlt(a, SC.pow2(d)) == True{} : Bool}, +v: U32) -> {AR.slots(U32, tu_last(d, tr, a, v)) == upd_last(AR.slots(U32, tr), a, v) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      UT.uset_s(d, tr, pf, NL.lastn(t, a0), ha, v)

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
      LK.seg_fn(pl, nl, NL.lastn(t, a0), v, xs, p, q, h)

def fll_lfn(+nl: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +fl: List<&2, Nat>, +h: {lastin(a, fl) == False{} : Bool}) -> {ST.fll(upd_last(nl, a, v), fl) == ST.fll(nl, fl) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      LK.fll_fn(nl, NL.lastn(t, a0), v, fl, h)

def ne1(+n: Nat, +x: Nat, +h: {NL.memn(x, Con{n, Nil{}}) == False{} : Bool}) -> {Nat.is_eq(x, n) == False{} : Bool}:
  NL.ne_sym(n, x, NL.or_ff_l(Nat.is_eq(n, x), False{}, h))

def nth_uf(+pl: List<&2, U32>, +b: List<&2, Nat>, +v: U32, +n: Nat, +h: {fstin(b, Con{n, Nil{}}) == False{} : Bool}) -> {W32.nth0(upd_first(pl, b, v), n) == W32.nth0(pl, n) : U32}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      W32.nth0_upd_other(pl, b0, n, v, ne1(n, b0, h))

def nth_ul(+nl: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +n: Nat, +h: {lastin(a, Con{n, Nil{}}) == False{} : Bool}) -> {W32.nth0(upd_last(nl, a, v), n) == W32.nth0(nl, n) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      W32.nth0_upd_other(nl, NL.lastn(t, a0), n, v, ne1(n, NL.lastn(t, a0), h))

# ---- re-targeting ----

def seg_ufp(+pl: List<&2, U32>, +nl: List<&2, U32>, +b: List<&2, Nat>, +x: U32, +q: U32, +y: U32, +hs: {ST.seg(pl, nl, b, x, q) == True{} : Bool}, +hn: {NL.nodupn(b) == True{} : Bool}, +hl: {fstlt(b, SC.length(U32, pl)) == True{} : Bool}) -> {ST.seg(upd_first(pl, b, y), nl, b, y, q) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      LK.segp(pl, nl, b0, t, x, q, y, hs, hn, hl)

def seg_ulq(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +p: U32, +x: U32, +y: U32, +hs: {ST.seg(pl, nl, a, p, x) == True{} : Bool}, +hn: {NL.nodupn(a) == True{} : Bool}, +hl: {lastlt(a, SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(pl, upd_last(nl, a, y), a, p, y) == True{} : Bool}:
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
  L.subst(U32, z => {U32.is_eq(z, y) == True{} : Bool}, y, x, Equal.sym(U32, x, y, e), LKx.u_refl(y))

# ---- disjointness of the parts of a list without repeats ----

# a ++ s :: b: b's first id is not in a
def fin_dj(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hn: {NL.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {fstin(b, a) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      NL.nd_dj(a, Con{s, Con{b0, t}}, hn, b0, NL.or_tr(Nat.is_eq(s, b0), NL.memn(b0, Con{b0, t}), self_in(b0, t)))

# a ++ s :: b: a's last id is not in b
def lin_dj(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hn: {NL.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {lastin(a, b) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      NL.or_ff_r(Nat.is_eq(s, NL.lastn(t, a0)), NL.memn(NL.lastn(t, a0), b), NL.nd_dj2(Con{a0, t}, Con{s, b}, hn, NL.lastn(t, a0), NL.lastn_mem(t, a0)))

# a ++ b: b's first id is not in a
def fin_dj2(+a: List<&2, Nat>, +b: List<&2, Nat>, +hn: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {fstin(b, a) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      NL.nd_dj(a, Con{b0, t}, hn, b0, self_in(b0, t))

# a ++ b: a's last id is not in b
def lin_dj2(+a: List<&2, Nat>, +b: List<&2, Nat>, +hn: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {lastin(a, b) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      NL.nd_dj2(Con{a0, t}, b, hn, NL.lastn(t, a0), NL.lastn_mem(t, a0))

def or_f(+x: Bool, +h: {x == False{} : Bool}) -> {Bool.or(x, False{}) == False{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, False{}) == False{} : Bool}, False{}, x, Equal.sym(Bool, x, False{}, h), {==})

# n off b: b's first id is not n
def fin1(+b: List<&2, Nat>, +n: Nat, +h: {NL.memn(n, b) == False{} : Bool}) -> {fstin(b, Con{n, Nil{}}) == False{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+b0, +t}:
      or_f(Nat.is_eq(n, b0), NL.ne_sym(b0, n, NL.or_ff_l(Nat.is_eq(b0, n), NL.memn(n, t), h)))

# n off a: a's last id is not n
def lin1(+a: List<&2, Nat>, +n: Nat, +h: {NL.memn(n, a) == False{} : Bool}) -> {lastin(a, Con{n, Nil{}}) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      or_f(Nat.is_eq(n, NL.lastn(t, a0)), NL.ne_sym(NL.lastn(t, a0), n, NL.ne_mem(n, NL.lastn(t, a0), Con{a0, t}, NL.not_f(NL.memn(n, Con{a0, t}), h), NL.lastn_mem(t, a0))))


# THEOREM (unlink): s between a and b; b's first prev becomes a's last link
# and a's last next becomes b's first link: a ++ b is linked
def unl_seg(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}, +hn: {NL.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hlp: {fstlt(b, SC.length(U32, pl)) == True{} : Bool}, +hln: {lastlt(a, SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(upd_first(pl, b, LKx.last_or(a, 0)), upd_last(nl, a, LKx.fst_or(b, 0)), SC.append(Nat, a, b), 0, 0) == True{} : Bool}:
  +pl2 = upd_first(pl, b, LKx.last_or(a, 0))
  +nl2 = upd_last(nl, a, LKx.fst_or(b, 0))
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsA = L.and_left(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0), hsp)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0), hsp)
  +hsB = L.and_right(U32.is_eq(W32.nth0(nl, s), LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.lnk(s), 0), L.and_right(U32.is_eq(W32.nth0(pl, s), LKx.last_or(a, 0)), Bool.and(U32.is_eq(W32.nth0(nl, s), LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.lnk(s), 0)), hsS))
  +hnS = NL.nd_r(a, Con{s, b}, hn)
  +hA1 = seg_ulq(pl, nl, a, 0, LKx.lnk(s), LKx.fst_or(b, 0), hsA, NL.nd_l(a, Con{s, b}, hn), hln)
  +hA = by_eq(ST.seg(pl2, nl2, a, 0, LKx.fst_or(b, 0)), ST.seg(pl, nl2, a, 0, LKx.fst_or(b, 0)), seg_ffp(pl, nl2, b, LKx.last_or(a, 0), a, 0, LKx.fst_or(b, 0), fin_dj(a, s, b, hn)), hA1)
  +hB1 = seg_ufp(pl, nl, b, LKx.lnk(s), 0, LKx.last_or(a, 0), hsB, L.and_right(Bool.not(NL.memn(s, b)), NL.nodupn(b), hnS), hlp)
  +hB = by_eq(ST.seg(pl2, nl2, b, LKx.last_or(a, 0), 0), ST.seg(pl2, nl, b, LKx.last_or(a, 0), 0), seg_lfn(pl2, nl, a, LKx.fst_or(b, 0), b, LKx.last_or(a, 0), 0, lin_dj(a, s, b, hn)), hB1)
  by_eq(ST.seg(pl2, nl2, SC.append(Nat, a, b), 0, 0), Bool.and(ST.seg(pl2, nl2, a, 0, LKx.fst_or(b, 0)), ST.seg(pl2, nl2, b, LKx.last_or(a, 0), 0)), LK.seg_app(pl2, nl2, a, b, 0, 0), L.and_intro(ST.seg(pl2, nl2, a, 0, LKx.fst_or(b, 0)), ST.seg(pl2, nl2, b, LKx.last_or(a, 0), 0), hA, hB))

# ... and s's own links are a's last and b's first
def unl_p(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}) -> {W32.nth0(pl, s) == LKx.last_or(a, 0) : U32}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0), hsp)
  A.eq_of(W32.nth0(pl, s), LKx.last_or(a, 0), L.and_left(U32.is_eq(W32.nth0(pl, s), LKx.last_or(a, 0)), Bool.and(U32.is_eq(W32.nth0(nl, s), LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.lnk(s), 0)), hsS))

def unl_n(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hs: {ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0) == True{} : Bool}) -> {W32.nth0(nl, s) == LKx.fst_or(b, 0) : U32}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, Con{s, b}), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, Con{s, b}, 0, 0), hs)
  +hsS = L.and_right(ST.seg(pl, nl, a, 0, LKx.lnk(s)), ST.seg(pl, nl, Con{s, b}, LKx.last_or(a, 0), 0), hsp)
  +hr = L.and_right(U32.is_eq(W32.nth0(pl, s), LKx.last_or(a, 0)), Bool.and(U32.is_eq(W32.nth0(nl, s), LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.lnk(s), 0)), hsS)
  A.eq_of(W32.nth0(nl, s), LKx.fst_or(b, 0), L.and_left(U32.is_eq(W32.nth0(nl, s), LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.lnk(s), 0), hr))


# THEOREM (insert between): n off a ++ b takes a's last as prev and b's
# first as next, and becomes their next and prev: a ++ n :: b is linked
def ins_seg(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +hs: {ST.seg(pl, nl, SC.append(Nat, a, b), 0, 0) == True{} : Bool}, +hn: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +hna: {NL.memn(n, a) == False{} : Bool}, +hnb: {NL.memn(n, b) == False{} : Bool}, +hlp: {Nat.is_lt(n, SC.length(U32, pl)) == True{} : Bool}, +hlq: {Nat.is_lt(n, SC.length(U32, nl)) == True{} : Bool}, +hfp: {fstlt(b, SC.length(U32, SC.update(U32, pl, n, LKx.last_or(a, 0)))) == True{} : Bool}, +hfq: {lastlt(a, SC.length(U32, SC.update(U32, nl, n, LKx.fst_or(b, 0)))) == True{} : Bool}) -> {ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), SC.append(Nat, a, Con{n, b}), 0, 0) == True{} : Bool}:
  +hsp = to_eq(ST.seg(pl, nl, SC.append(Nat, a, b), 0, 0), Bool.and(ST.seg(pl, nl, a, 0, LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.last_or(a, 0), 0)), LK.seg_app(pl, nl, a, b, 0, 0), hs)
  +hsA = L.and_left(ST.seg(pl, nl, a, 0, LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.last_or(a, 0), 0), hsp)
  +hsB = L.and_right(ST.seg(pl, nl, a, 0, LKx.fst_or(b, 0)), ST.seg(pl, nl, b, LKx.last_or(a, 0), 0), hsp)
  +hA1 = by_eq(ST.seg(pl, SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, 0, LKx.fst_or(b, 0)), ST.seg(pl, nl, a, 0, LKx.fst_or(b, 0)), LK.seg_fn(pl, nl, n, LKx.fst_or(b, 0), a, 0, LKx.fst_or(b, 0), hna), hsA)
  +hA2 = seg_ulq(pl, SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, 0, LKx.fst_or(b, 0), LKx.lnk(n), hA1, NL.nd_l(a, b, hn), hfq)
  +hA3 = by_eq(ST.seg(SC.update(U32, pl, n, LKx.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), ST.seg(pl, upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), LK.seg_fp(pl, upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), n, LKx.last_or(a, 0), a, 0, LKx.lnk(n), hna), hA2)
  +hA = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), ST.seg(SC.update(U32, pl, n, LKx.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), seg_ffp(SC.update(U32, pl, n, LKx.last_or(a, 0)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), b, LKx.lnk(n), a, 0, LKx.lnk(n), fin_dj2(a, b, hn)), hA3)
  +ep = Equal.trans(U32, W32.nth0(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), n), W32.nth0(SC.update(U32, pl, n, LKx.last_or(a, 0)), n), LKx.last_or(a, 0), nth_uf(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n), n, fin1(b, n, hnb)), W32.nth0_upd_same(pl, n, LKx.last_or(a, 0), hlp))
  +eq = Equal.trans(U32, W32.nth0(upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), n), W32.nth0(SC.update(U32, nl, n, LKx.fst_or(b, 0)), n), LKx.fst_or(b, 0), nth_ul(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n), n, lin1(a, n, hna)), W32.nth0_upd_same(nl, n, LKx.fst_or(b, 0), hlq))
  +hB1 = by_eq(ST.seg(SC.update(U32, pl, n, LKx.last_or(a, 0)), nl, b, LKx.last_or(a, 0), 0), ST.seg(pl, nl, b, LKx.last_or(a, 0), 0), LK.seg_fp(pl, nl, n, LKx.last_or(a, 0), b, LKx.last_or(a, 0), 0, hnb), hsB)
  +hB2 = seg_ufp(SC.update(U32, pl, n, LKx.last_or(a, 0)), nl, b, LKx.last_or(a, 0), 0, LKx.lnk(n), hB1, NL.nd_r(a, b, hn), hfp)
  +hB3 = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), SC.update(U32, nl, n, LKx.fst_or(b, 0)), b, LKx.lnk(n), 0), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), nl, b, LKx.lnk(n), 0), LK.seg_fn(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), nl, n, LKx.fst_or(b, 0), b, LKx.lnk(n), 0, hnb), hB2)
  +hB = by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), b, LKx.lnk(n), 0), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), SC.update(U32, nl, n, LKx.fst_or(b, 0)), b, LKx.lnk(n), 0), seg_lfn(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n), b, LKx.lnk(n), 0, lin_dj2(a, b, hn)), hB3)
  +hN = L.and_intro(U32.is_eq(W32.nth0(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), n), LKx.last_or(a, 0)), Bool.and(U32.is_eq(W32.nth0(upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), n), LKx.fst_or(b, 0)), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), b, LKx.lnk(n), 0)), u_is(W32.nth0(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), n), LKx.last_or(a, 0), ep), L.and_intro(U32.is_eq(W32.nth0(upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), n), LKx.fst_or(b, 0)), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), b, LKx.lnk(n), 0), u_is(W32.nth0(upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), n), LKx.fst_or(b, 0), eq), hB))
  by_eq(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), SC.append(Nat, a, Con{n, b}), 0, 0), Bool.and(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), Con{n, b}, LKx.last_or(a, 0), 0)), LK.seg_app(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, Con{n, b}, 0, 0), L.and_intro(ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), a, 0, LKx.lnk(n)), ST.seg(upd_first(SC.update(U32, pl, n, LKx.last_or(a, 0)), b, LKx.lnk(n)), upd_last(SC.update(U32, nl, n, LKx.fst_or(b, 0)), a, LKx.lnk(n)), Con{n, b}, LKx.last_or(a, 0), 0), hA, hN))
