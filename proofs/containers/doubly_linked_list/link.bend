import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as A
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/doubly_linked_list.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/internal/dlist_storage.bend as R
import ../../../src/containers/types/internal_dlist.bend as I
import ./rel.bend as RL
import ../../lib/nat_list.bend as NL
import ../../lib/links.bend as LK
import ../../lib/u32_tree.bend as UT

# link_in over the mirror trees: the storage record it builds.


# ---- value arrays ----

def nth_val(-T: Data, +vl: List<&2, Maybe<&2, T>>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, vl, i) == Some{S.val_of(T, vl, i)} : Maybe<&2, Maybe<&2, T>>}:
  match vl i:
    case Nil{} _:
      Empty.absurd({SC.nth(Maybe<&2, T>, Nil{}, i) == Some{S.val_of(T, Nil{}, i)} : Maybe<&2, Maybe<&2, T>>}, N.lt_zero_absurd(i, h))
    case Con{m, t} 0n:
      {==}
    case Con{m, +t} 1n+p:
      nth_val(T, t, p, h)


def vget(-T: Data, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}) -> {Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), i) == (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(i))) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  AR.get(Maybe<&2, T>, d, vT, i, S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(i)), RL.hd0(d, hd), hi, nth_val(T, AR.slots(Maybe<&2, T>, vT), UD.v(i), UT.len_of(Maybe<&2, T>, d, vT, pv, UD.v(i), hi)), pv)

def vset(-T: Data, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}, +x: Maybe<&2, T>) -> {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), i, x) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, UD.v(i), x)) : Array<Maybe<&2, T>>}:
  AR.set(Maybe<&2, T>, d, vT, i, x, S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(i)), RL.hd0(d, hd), hi, nth_val(T, AR.slots(Maybe<&2, T>, vT), UD.v(i), UT.len_of(Maybe<&2, T>, d, vT, pv, UD.v(i), hi)), pv)

def vswap(-T: Data, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}, +x: Maybe<&2, T>) -> {Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), i, x) == (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, UD.v(i), x)), S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(i))) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  AR.swap(Maybe<&2, T>, d, vT, i, x, S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(i)), RL.hd0(d, hd), hi, nth_val(T, AR.slots(Maybe<&2, T>, vT), UD.v(i), UT.len_of(Maybe<&2, T>, d, vT, pv, UD.v(i), hi)), pv)

# ---- ids as U32 ----

def fn_v(+nn: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hn: {Nat.is_lt(nn, SC.pow2(d)) == True{} : Bool}) -> {UD.v(U32.from_nat(nn)) == nn : Nat}:
  U.to_nat_from_nat(nn, d, N.lt_le(d, 32n, RL.hd0(d, hd)), hn)

def fn_lt(+nn: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hn: {Nat.is_lt(nn, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(UD.v(U32.from_nat(nn)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, nn, UD.v(U32.from_nat(nn)), Equal.sym(Nat, UD.v(U32.from_nat(nn)), nn, fn_v(nn, d, hd, hn)), hn)

# a U32 below 2^k is the U32 of its value
def fn_of(+i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}) -> {U32.from_nat(UD.v(i)) == i : U32}:
  U.injective(U32.from_nat(UD.v(i)), i, U.to_nat_from_nat(UD.v(i), k, hk, h))

# the slot of an id's link is the id's U32
def slot_fn(+one: Nat, +h1: {one == 1n : Nat}, +nn: Nat, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +hn: {Nat.is_lt(nn, SC.pow2(d)) == True{} : Bool}) -> {R.slot(LK.lnk(nn)) == U32.from_nat(nn) : U32}:
  U.injective(R.slot(LK.lnk(nn)), U32.from_nat(nn), Equal.trans(Nat, UD.v(R.slot(LK.lnk(nn))), nn, UD.v(U32.from_nat(nn)), RL.slot_lnk(one, h1, nn, d, hd, hn), Equal.sym(Nat, UD.v(U32.from_nat(nn)), nn, fn_v(nn, d, hd, hn))))

# ---- head and tail ----

def pick_f(+c: Bool, +h: {c == False{} : Bool}, +x: U32, +y: U32) -> {R.pick_end(c, x, y) == y : U32}:
  L.subst(Bool, z => {R.pick_end(z, x, y) == y : U32}, False{}, c, Equal.sym(Bool, c, False{}, h), {==})


# the head after linking n between a and b
def hd_in(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +head: U32, +hh: {U32.is_eq(head, LK.fst_or(SC.append(Nat, a, b), 0)) == True{} : Bool}, +ha: {RL.lastlt(a, SC.pow2(d)) == True{} : Bool}) -> {R.pick_end(U32.is_eq(LK.last_or(a, 0), 0), LK.lnk(n), head) == LK.fst_or(SC.append(Nat, a, Con{n, b}), 0) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      +z = NL.lastn(t, a0)
      +hc = Equal.trans(Bool, U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), U32.is_eq(LK.lnk(z), 0), False{}, Equal.cong(U32, Bool, w => U32.is_eq(w, 0), LK.last_or(t, LK.lnk(a0)), LK.lnk(z), LK.last_lnk(t, a0)), RL.lnk_nz(one, h1, z, d, hd, ha))
      Equal.trans(U32, R.pick_end(U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), LK.lnk(n), head), head, LK.lnk(a0), pick_f(U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), hc, LK.lnk(n), head), A.eq_of(head, LK.lnk(a0), hh))

# the tail after linking n between a and b
def tl_in(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +tail: U32, +ht: {U32.is_eq(tail, LK.last_or(SC.append(Nat, a, b), 0)) == True{} : Bool}, +hb: {RL.fstlt(b, SC.pow2(d)) == True{} : Bool}) -> {R.pick_end(U32.is_eq(LK.fst_or(b, 0), 0), LK.lnk(n), tail) == LK.last_or(SC.append(Nat, a, Con{n, b}), 0) : U32}:
  match b:
    case Nil{}:
      Equal.sym(U32, LK.last_or(SC.append(Nat, a, Con{n, Nil{}}), 0), LK.lnk(n), LK.last_app(a, Con{n, Nil{}}, 0))
    case Con{+b0, +t}:
      +et = Equal.trans(U32, tail, LK.last_or(SC.append(Nat, a, Con{b0, t}), 0), LK.last_or(t, LK.lnk(b0)), A.eq_of(tail, LK.last_or(SC.append(Nat, a, Con{b0, t}), 0), ht), LK.last_app(a, Con{b0, t}, 0))
      Equal.trans(U32, R.pick_end(U32.is_eq(LK.lnk(b0), 0), LK.lnk(n), tail), tail, LK.last_or(SC.append(Nat, a, Con{n, Con{b0, t}}), 0), pick_f(U32.is_eq(LK.lnk(b0), 0), RL.lnk_nz(one, h1, b0, d, hd, hb), LK.lnk(n), tail), Equal.trans(U32, tail, LK.last_or(t, LK.lnk(b0)), LK.last_or(SC.append(Nat, a, Con{n, Con{b0, t}}), 0), et, Equal.sym(U32, LK.last_or(SC.append(Nat, a, Con{n, Con{b0, t}}), 0), LK.last_or(t, LK.lnk(b0)), LK.last_app(a, Con{n, Con{b0, t}}, 0))))

# the head after unlinking s from between a and b
def hd_rm(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +head: U32, +hh: {U32.is_eq(head, LK.fst_or(SC.append(Nat, a, Con{s, b}), 0)) == True{} : Bool}, +ha: {RL.lastlt(a, SC.pow2(d)) == True{} : Bool}) -> {R.pick_end(U32.is_eq(LK.last_or(a, 0), 0), LK.fst_or(b, 0), head) == LK.fst_or(SC.append(Nat, a, b), 0) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+a0, +t}:
      +z = NL.lastn(t, a0)
      +hc = Equal.trans(Bool, U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), U32.is_eq(LK.lnk(z), 0), False{}, Equal.cong(U32, Bool, w => U32.is_eq(w, 0), LK.last_or(t, LK.lnk(a0)), LK.lnk(z), LK.last_lnk(t, a0)), RL.lnk_nz(one, h1, z, d, hd, ha))
      Equal.trans(U32, R.pick_end(U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), LK.fst_or(b, 0), head), head, LK.lnk(a0), pick_f(U32.is_eq(LK.last_or(t, LK.lnk(a0)), 0), hc, LK.fst_or(b, 0), head), A.eq_of(head, LK.lnk(a0), hh))

# the tail after unlinking s from between a and b
def tl_rm(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +tail: U32, +ht: {U32.is_eq(tail, LK.last_or(SC.append(Nat, a, Con{s, b}), 0)) == True{} : Bool}, +hb: {RL.fstlt(b, SC.pow2(d)) == True{} : Bool}) -> {R.pick_end(U32.is_eq(LK.fst_or(b, 0), 0), LK.last_or(a, 0), tail) == LK.last_or(SC.append(Nat, a, b), 0) : U32}:
  match b:
    case Nil{}:
      Equal.cong(List<&2, Nat>, U32, w => LK.last_or(w, 0), a, SC.append(Nat, a, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, a, Nil{}), a, LL.append_nil(Nat, a)))
    case Con{+b0, +t}:
      +et = Equal.trans(U32, tail, LK.last_or(SC.append(Nat, a, Con{s, Con{b0, t}}), 0), LK.last_or(t, LK.lnk(b0)), A.eq_of(tail, LK.last_or(SC.append(Nat, a, Con{s, Con{b0, t}}), 0), ht), LK.last_app(a, Con{s, Con{b0, t}}, 0))
      Equal.trans(U32, R.pick_end(U32.is_eq(LK.lnk(b0), 0), LK.last_or(a, 0), tail), tail, LK.last_or(SC.append(Nat, a, Con{b0, t}), 0), pick_f(U32.is_eq(LK.lnk(b0), 0), RL.lnk_nz(one, h1, b0, d, hd, hb), LK.last_or(a, 0), tail), Equal.trans(U32, tail, LK.last_or(t, LK.lnk(b0)), LK.last_or(SC.append(Nat, a, Con{b0, t}), 0), et, Equal.sym(U32, LK.last_or(SC.append(Nat, a, Con{b0, t}), 0), LK.last_or(t, LK.lnk(b0)), LK.last_app(a, Con{b0, t}, 0))))

# ---- lengths ----

def len_mid(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, a, Con{n, b})) == 1n+SC.length(Nat, SC.append(Nat, a, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(SC.length(Nat, SC.append(Nat, t, Con{n, b})), 1n+SC.length(Nat, SC.append(Nat, t, b)), len_mid(t, n, b))

# ---- the storage record ----

def dl_eq(-T: Data, +tag: U32, +fr: U32, +fe: U32, +c1: Nat, +c2: Nat, +h1: U32, +h2: U32, +t1: U32, +t2: U32, +d: Nat, +cap: U32, -v1: Array<Maybe<&2, T>>, +v2: AR.Tree<Maybe<&2, T>>, -p1: Array<U32>, +p2: AR.Tree<U32>, -n1: Array<U32>, +n2: AR.Tree<U32>, +ec: {c1 == c2 : Nat}, +eh: {h1 == h2 : U32}, +et: {t1 == t2 : U32}, +ev: {v1 == AR.thaw(Maybe<&2, T>, v2) : Array<Maybe<&2, T>>}, +ep: {p1 == AR.thaw(U32, p2) : Array<U32>}, +en: {n1 == AR.thaw(U32, n2) : Array<U32>}) -> {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, h2, t2, d, cap, AR.thaw(Maybe<&2, T>, v2), AR.thaw(U32, p2), AR.thaw(U32, n2)} : R.DList<T>}:
  +r0 = L.subst(Nat, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, z, h1, t1, d, cap, v1, p1, n1} : R.DList<T>}, c1, c2, ec, {==})
  +r1 = L.subst(U32, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, z, t1, d, cap, v1, p1, n1} : R.DList<T>}, h1, h2, eh, r0)
  +r2 = L.subst(U32, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, h2, z, d, cap, v1, p1, n1} : R.DList<T>}, t1, t2, et, r1)
  +r3 = L.subst(Array<Maybe<&2, T>>, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, h2, t2, d, cap, z, p1, n1} : R.DList<T>}, v1, AR.thaw(Maybe<&2, T>, v2), ev, r2)
  +r4 = L.subst(Array<U32>, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, h2, t2, d, cap, AR.thaw(Maybe<&2, T>, v2), z, n1} : R.DList<T>}, p1, AR.thaw(U32, p2), ep, r3)
  L.subst(Array<U32>, z => {R.DL{tag, fr, fe, c1, h1, t1, d, cap, v1, p1, n1} == R.DL{tag, fr, fe, c2, h2, t2, d, cap, AR.thaw(Maybe<&2, T>, v2), AR.thaw(U32, p2), z} : R.DList<T>}, n1, AR.thaw(U32, n2), en, r4)


# THEOREM (link_in): n (below 2^d) is stored and linked between a's last
# and b's first; the record's head and tail are those of a ++ n :: b
def link_ok(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pT: AR.Tree<U32>, +nT: AR.Tree<U32>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +pp: {AR.perfect(U32, d, pT) == True{} : Bool}, +pn: {AR.perfect(U32, d, nT) == True{} : Bool}, +tag: U32, +nf: U32, +nfr: U32, +head: U32, +tail: U32, +cap: U32, +a: List<&2, Nat>, +b: List<&2, Nat>, +nn: Nat, +hn: {Nat.is_lt(nn, SC.pow2(d)) == True{} : Bool}, +ha: {RL.lastlt(a, SC.pow2(d)) == True{} : Bool}, +hb: {RL.fstlt(b, SC.pow2(d)) == True{} : Bool}, +hh: {U32.is_eq(head, LK.fst_or(SC.append(Nat, a, b), 0)) == True{} : Bool}, +ht: {U32.is_eq(tail, LK.last_or(SC.append(Nat, a, b), 0)) == True{} : Bool}, +x: T) -> {R.link_in(~T, tag, U32.from_nat(nn), nf, nfr, SC.length(Nat, SC.append(Nat, a, b)), head, tail, d, cap, AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), AR.thaw(U32, nT), LK.last_or(a, 0), LK.fst_or(b, 0), x) == (R.DL{tag, nf, nfr, SC.length(Nat, SC.append(Nat, a, Con{nn, b})), LK.fst_or(SC.append(Nat, a, Con{nn, b}), 0), LK.last_or(SC.append(Nat, a, Con{nn, b}), 0), d, cap, AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, nn, Some{x})), AR.thaw(U32, RL.tu_first(d, AR.upd(U32, d, pT, nn, LK.last_or(a, 0)), b, LK.lnk(nn))), AR.thaw(U32, RL.tu_last(d, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0)), a, LK.lnk(nn)))}, I.H{tag, U32.from_nat(nn)}) : R.DList<T> & I.Handle}:
  +ev0 = fn_v(nn, d, hd, hn)
  +hi = fn_lt(nn, d, hd, hn)
  +ev = Equal.trans(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), U32.from_nat(nn), Some{x}), AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, UD.v(U32.from_nat(nn)), Some{x})), AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, nn, Some{x})), vset(T, d, hd, vT, pv, U32.from_nat(nn), hi, Some{x}), Equal.cong(Nat, Array<Maybe<&2, T>>, z => AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, z, Some{x})), UD.v(U32.from_nat(nn)), nn, ev0))
  +ep1 = Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, pT), U32.from_nat(nn), LK.last_or(a, 0)), AR.thaw(U32, AR.upd(U32, d, pT, UD.v(U32.from_nat(nn)), LK.last_or(a, 0))), AR.thaw(U32, AR.upd(U32, d, pT, nn, LK.last_or(a, 0))), UT.uset_a(d, RL.hd0(d, hd), pT, pp, U32.from_nat(nn), hi, LK.last_or(a, 0)), Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, pT, z, LK.last_or(a, 0))), UD.v(U32.from_nat(nn)), nn, ev0))
  +ep2 = RL.sn_first(one, h1, d, hd, AR.upd(U32, d, pT, nn, LK.last_or(a, 0)), UT.uset_p(d, pT, pp, nn, LK.last_or(a, 0)), b, hb, LK.lnk(nn))
  +ep = Equal.trans(Array<U32>, R.set_next(Array.set(U32, AR.thaw(U32, pT), U32.from_nat(nn), LK.last_or(a, 0)), LK.fst_or(b, 0), LK.lnk(nn)), R.set_next(AR.thaw(U32, AR.upd(U32, d, pT, nn, LK.last_or(a, 0))), LK.fst_or(b, 0), LK.lnk(nn)), AR.thaw(U32, RL.tu_first(d, AR.upd(U32, d, pT, nn, LK.last_or(a, 0)), b, LK.lnk(nn))), Equal.cong(Array<U32>, Array<U32>, z => R.set_next(z, LK.fst_or(b, 0), LK.lnk(nn)), Array.set(U32, AR.thaw(U32, pT), U32.from_nat(nn), LK.last_or(a, 0)), AR.thaw(U32, AR.upd(U32, d, pT, nn, LK.last_or(a, 0))), ep1), ep2)
  +en1 = Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, nT), U32.from_nat(nn), LK.fst_or(b, 0)), AR.thaw(U32, AR.upd(U32, d, nT, UD.v(U32.from_nat(nn)), LK.fst_or(b, 0))), AR.thaw(U32, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0))), UT.uset_a(d, RL.hd0(d, hd), nT, pn, U32.from_nat(nn), hi, LK.fst_or(b, 0)), Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, nT, z, LK.fst_or(b, 0))), UD.v(U32.from_nat(nn)), nn, ev0))
  +en2 = RL.sn_last(one, h1, d, hd, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0)), UT.uset_p(d, nT, pn, nn, LK.fst_or(b, 0)), a, ha, LK.lnk(nn))
  +en = Equal.trans(Array<U32>, R.set_next(Array.set(U32, AR.thaw(U32, nT), U32.from_nat(nn), LK.fst_or(b, 0)), LK.last_or(a, 0), LK.lnk(nn)), R.set_next(AR.thaw(U32, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0))), LK.last_or(a, 0), LK.lnk(nn)), AR.thaw(U32, RL.tu_last(d, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0)), a, LK.lnk(nn))), Equal.cong(Array<U32>, Array<U32>, z => R.set_next(z, LK.last_or(a, 0), LK.lnk(nn)), Array.set(U32, AR.thaw(U32, nT), U32.from_nat(nn), LK.fst_or(b, 0)), AR.thaw(U32, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0))), en1), en2)
  +e = dl_eq(T, tag, nf, nfr, 1n+SC.length(Nat, SC.append(Nat, a, b)), SC.length(Nat, SC.append(Nat, a, Con{nn, b})), R.pick_end(U32.is_eq(LK.last_or(a, 0), 0), LK.lnk(nn), head), LK.fst_or(SC.append(Nat, a, Con{nn, b}), 0), R.pick_end(U32.is_eq(LK.fst_or(b, 0), 0), LK.lnk(nn), tail), LK.last_or(SC.append(Nat, a, Con{nn, b}), 0), d, cap, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), U32.from_nat(nn), Some{x}), AR.upd(Maybe<&2, T>, d, vT, nn, Some{x}), R.set_next(Array.set(U32, AR.thaw(U32, pT), U32.from_nat(nn), LK.last_or(a, 0)), LK.fst_or(b, 0), LK.lnk(nn)), RL.tu_first(d, AR.upd(U32, d, pT, nn, LK.last_or(a, 0)), b, LK.lnk(nn)), R.set_next(Array.set(U32, AR.thaw(U32, nT), U32.from_nat(nn), LK.fst_or(b, 0)), LK.last_or(a, 0), LK.lnk(nn)), RL.tu_last(d, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0)), a, LK.lnk(nn)), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, Con{nn, b})), 1n+SC.length(Nat, SC.append(Nat, a, b)), len_mid(a, nn, b)), hd_in(one, h1, d, hd, a, b, nn, head, hh, ha), tl_in(one, h1, d, hd, a, b, nn, tail, ht, hb), ev, ep, en)
  Equal.cong(R.DList<T>, R.DList<T> & I.Handle, r => (r, I.H{tag, U32.from_nat(nn)}), R.DL{tag, nf, nfr, 1n+SC.length(Nat, SC.append(Nat, a, b)), R.pick_end(U32.is_eq(LK.last_or(a, 0), 0), LK.lnk(nn), head), R.pick_end(U32.is_eq(LK.fst_or(b, 0), 0), LK.lnk(nn), tail), d, cap, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), U32.from_nat(nn), Some{x}), R.set_next(Array.set(U32, AR.thaw(U32, pT), U32.from_nat(nn), LK.last_or(a, 0)), LK.fst_or(b, 0), LK.lnk(nn)), R.set_next(Array.set(U32, AR.thaw(U32, nT), U32.from_nat(nn), LK.fst_or(b, 0)), LK.last_or(a, 0), LK.lnk(nn))}, R.DL{tag, nf, nfr, SC.length(Nat, SC.append(Nat, a, Con{nn, b})), LK.fst_or(SC.append(Nat, a, Con{nn, b}), 0), LK.last_or(SC.append(Nat, a, Con{nn, b}), 0), d, cap, AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, vT, nn, Some{x})), AR.thaw(U32, RL.tu_first(d, AR.upd(U32, d, pT, nn, LK.last_or(a, 0)), b, LK.lnk(nn))), AR.thaw(U32, RL.tu_last(d, AR.upd(U32, d, nT, nn, LK.fst_or(b, 0)), a, LK.lnk(nn)))}, e)
