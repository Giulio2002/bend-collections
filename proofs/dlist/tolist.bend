import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../graph/ashift.bend as AS2
import ../graph/nbrops.bend as NO
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./core.bend as K
import ./alive.bend as AL
import ./reads.bend as RD

import ./nbrs.bend as NB

# to_list walks the prev links backwards from the tail.

def lsnoc(+t: List<&2, Nat>, +y: Nat, +x: Nat) -> {ST.ln(ST.lst_or(SC.append(Nat, t, Con{x, Nil{}}), y)) == ST.ln(x) : U32}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      lsnoc(r, z, x)

def lastl_snoc(+a: List<&2, Nat>, +x: Nat, +pv: U32) -> {LK.lastl(SC.append(Nat, a, Con{x, Nil{}}), pv) == ST.ln(x) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      lsnoc(t, y, x)

def vals_app(-T: Data, +a: List<&2, E.Item<T>>, +b: List<&2, E.Item<T>>) -> {DS.vals(T, SC.append(E.Item<T>, a, b)) == SC.append(T, DS.vals(T, a), DS.vals(T, b)) : List<&2, T>}:
  match a:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +v}, +t}:
      LL.cons_cong(T, v, DS.vals(T, SC.append(E.Item<T>, t, b)), SC.append(T, DS.vals(T, t), DS.vals(T, b)), vals_app(T, t, b))

def lst_lastl(+ord: List<&2, Nat>) -> {ST.lst(ord) == LK.lastl(ord, D.nil()) : U32}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

def wcur(~T: Data, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +acc: List<&2, T>, +at: U32) -> D.Cur<T>:
  D.C{AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), acc, at}

def get_at(-T: Data, +depth: Nat, +t: AR.Tree<T>, +x: Nat, +d: T, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(T, depth, t) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> {Array.get(T, AR.thaw(T, t), U32.from_nat(x)) == (AR.thaw(T, t), L.some_value(T, SC.nth(T, AR.slots(T, t), x), d)) : Array<T> & T}:
  +rx = F.id_nat(x, depth, hd, hx)
  AR.get(T, depth, t, U32.from_nat(x), L.some_value(T, SC.nth(T, AR.slots(T, t), x), d), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), hx),
    L.subst(Nat, z => {SC.nth(T, AR.slots(T, t), z) == Some{L.some_value(T, SC.nth(T, AR.slots(T, t), x), d)} : Maybe<&2, T>}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), AS2.tsat(T, depth, t, x, d, pf, hx)),
    pf)

# The value slot of a live id x holds Some of its value.
def slot_some(-T: Data, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +x: Nat, +pf: {AR.perfect(Maybe<&2, T>, depth, tv) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}, +hs: {ST.is_some(T, ST.vat(T, AR.slots(Maybe<&2, T>, tv), x)) == True{} : Bool}) -> {L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), x), None{}) == Some{AL.val_of(T, ST.vat(T, AR.slots(Maybe<&2, T>, tv), x), hs)} : Maybe<&2, T>}:
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ev = Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, m => ST.flat(T, m), SC.nth(Maybe<&2, T>, xs, x), Some{L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, xs, x), None{})}, AS2.tsat(Maybe<&2, T>, depth, tv, x, None{}, pf, hx))
  Equal.trans(Maybe<&2, T>, L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, xs, x), None{}), ST.vat(T, xs, x), Some{AL.val_of(T, ST.vat(T, xs, x), hs)},
    Equal.sym(Maybe<&2, T>, ST.vat(T, xs, x), L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, xs, x), None{}), ev),
    AL.some_val(T, ST.vat(T, xs, x), hs))

def alllt_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.alllt(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.alllt(a, n) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.and_intro(Nat.is_lt(y, n), ST.alllt(t, n), L.and_left(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h), alllt_l(t, b, n, L.and_right(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h)))

def alllt_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.alllt(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.alllt(b, n) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+y, +t}:
      alllt_r(t, b, n, L.and_right(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h))

# One step back from the link to a live x.
def step_back_ok(~T: Data, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +acc: List<&2, T>, +x: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfv: {AR.perfect(Maybe<&2, T>, depth, tv) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}, +hs: {ST.is_some(T, ST.vat(T, AR.slots(Maybe<&2, T>, tv), x)) == True{} : Bool}) -> {D.step_back(~T, wcur(~T, tv, tp, acc, ST.ln(x))) == wcur(~T, tv, tp, Con{AL.val_of(T, ST.vat(T, AR.slots(Maybe<&2, T>, tv), x), hs), acc}, ST.lat(AR.slots(U32, tp), x)) : D.Cur<T>}:
  +v = AL.val_of(T, ST.vat(T, AR.slots(Maybe<&2, T>, tv), x), hs)
  +es = F.slot_ln(x, depth, hd, hx)
  +e1 = Equal.cong(U32, D.Cur<T>, z => D.step_v(~T, AR.thaw(U32, tp), acc, ST.ln(x), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), z)), D.slot(ST.ln(x)), U32.from_nat(x), es)
  +e2 = Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.Cur<T>, r => D.step_v(~T, AR.thaw(U32, tp), acc, ST.ln(x), r), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), U32.from_nat(x)), (AR.thaw(Maybe<&2, T>, tv), L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), x), None{})), get_at(Maybe<&2, T>, depth, tv, x, None{}, hd, pfv, hx))
  +e3 = Equal.cong(Maybe<&2, T>, D.Cur<T>, m => D.step_m(~T, AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), acc, ST.ln(x), m), L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), x), None{}), Some{v}, slot_some(T, depth, tv, x, pfv, hx, hs))
  +e4 = Equal.cong(U32, D.Cur<T>, z => D.step_p(~T, AR.thaw(Maybe<&2, T>, tv), Con{v, acc}, Array.get(U32, AR.thaw(U32, tp), z)), D.slot(ST.ln(x)), U32.from_nat(x), es)
  +e5 = Equal.cong(Array<U32> & U32, D.Cur<T>, r => D.step_p(~T, AR.thaw(Maybe<&2, T>, tv), Con{v, acc}, r), Array.get(U32, AR.thaw(U32, tp), U32.from_nat(x)), (AR.thaw(U32, tp), ST.lat(AR.slots(U32, tp), x)), get_at(U32, depth, tp, x, 0, hd, pfp, hx))
  Equal.trans(D.Cur<T>, D.step_v(~T, AR.thaw(U32, tp), acc, ST.ln(x), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), D.slot(ST.ln(x)))), D.step_v(~T, AR.thaw(U32, tp), acc, ST.ln(x), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), U32.from_nat(x))), wcur(~T, tv, tp, Con{v, acc}, ST.lat(AR.slots(U32, tp), x)), e1,
    Equal.trans(D.Cur<T>, D.step_v(~T, AR.thaw(U32, tp), acc, ST.ln(x), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), U32.from_nat(x))), D.step_m(~T, AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), acc, ST.ln(x), L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), x), None{})), wcur(~T, tv, tp, Con{v, acc}, ST.lat(AR.slots(U32, tp), x)), e2,
      Equal.trans(D.Cur<T>, D.step_m(~T, AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), acc, ST.ln(x), L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), x), None{})), D.step_p(~T, AR.thaw(Maybe<&2, T>, tv), Con{v, acc}, Array.get(U32, AR.thaw(U32, tp), D.slot(ST.ln(x)))), wcur(~T, tv, tp, Con{v, acc}, ST.lat(AR.slots(U32, tp), x)), e3,
        Equal.trans(D.Cur<T>, D.step_p(~T, AR.thaw(Maybe<&2, T>, tv), Con{v, acc}, Array.get(U32, AR.thaw(U32, tp), D.slot(ST.ln(x)))), D.step_p(~T, AR.thaw(Maybe<&2, T>, tv), Con{v, acc}, Array.get(U32, AR.thaw(U32, tp), U32.from_nat(x))), wcur(~T, tv, tp, Con{v, acc}, ST.lat(AR.slots(U32, tp), x)), e4, e5))))

def lk_single_p(+x: Nat, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(Con{x, Nil{}}, pv, e, ps, ns) == True{} : Bool}) -> {ST.lat(ps, x) == pv : U32}:
  NB.ueq_true(ST.lat(ps, x), pv, L.and_left(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), e), True{}), h))

def walk_ok(~T: Data, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +ns: List<&2, U32>, +r: List<&2, Nat>, +acc: List<&2, T>, +e: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfv: {AR.perfect(Maybe<&2, T>, depth, tv) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +hl: {ST.alllt(SC.reverse(Nat, r), SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, AR.slots(Maybe<&2, T>, tv), SC.reverse(Nat, r)) == True{} : Bool}, +hk: {ST.lk(SC.reverse(Nat, r), D.nil(), e, AR.slots(U32, tp), ns) == True{} : Bool}) -> {D.walk(~T, SC.length(Nat, r), wcur(~T, tv, tp, acc, LK.lastl(SC.reverse(Nat, r), D.nil()))) == wcur(~T, tv, tp, SC.append(T, DS.vals(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), SC.reverse(Nat, r))), acc), D.nil()) : D.Cur<T>}:
  match r:
    case Nil{}:
      {==}
    case Con{+x, +rt}:
      +xs = AR.slots(Maybe<&2, T>, tv)
      +ps = AR.slots(U32, tp)
      +a1 = SC.reverse(Nat, rt)
      +ap = SC.append(Nat, a1, Con{x, Nil{}})
      +esn = LL.snoc_append(Nat, a1, x)
      +hl1 = L.subst(List<&2, Nat>, z => {ST.alllt(z, SC.pow2(depth)) == True{} : Bool}, SC.snoc(Nat, a1, x), ap, esn, hl)
      +ha1 = L.subst(List<&2, Nat>, z => {AL.alive(T, xs, z) == True{} : Bool}, SC.snoc(Nat, a1, x), ap, esn, ha)
      +hk1 = L.subst(List<&2, Nat>, z => {ST.lk(z, D.nil(), e, ps, ns) == True{} : Bool}, SC.snoc(Nat, a1, x), ap, esn, hk)
      +hk2 = L.subst(Bool, b => {b == True{} : Bool}, ST.lk(ap, D.nil(), e, ps, ns), Bool.and(ST.lk(a1, D.nil(), ST.ln(x), ps, ns), ST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns)), LK.lk_app(a1, Con{x, Nil{}}, D.nil(), e, ps, ns), hk1)
      +hka = L.and_left(ST.lk(a1, D.nil(), ST.ln(x), ps, ns), ST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns), hk2)
      +hkx = L.and_right(ST.lk(a1, D.nil(), ST.ln(x), ps, ns), ST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns), hk2)
      +hax = AL.alive_app_r(T, xs, a1, Con{x, Nil{}}, ha1)
      +hs = L.and_left(ST.is_some(T, ST.vat(T, xs, x)), True{}, hax)
      +hx = L.and_left(Nat.is_lt(x, SC.pow2(depth)), True{}, alllt_r(a1, Con{x, Nil{}}, SC.pow2(depth), hl1))
      +v = AL.val_of(T, ST.vat(T, xs, x), hs)
      +ih = walk_ok(~T, depth, tv, tp, ns, rt, Con{v, acc}, ST.ln(x), hd, pfv, pfp, alllt_l(a1, Con{x, Nil{}}, SC.pow2(depth), hl1), AL.alive_app(T, xs, a1, Con{x, Nil{}}, ha1), hka)
      +elast = Equal.trans(U32, LK.lastl(SC.snoc(Nat, a1, x), D.nil()), LK.lastl(ap, D.nil()), ST.ln(x), Equal.cong(List<&2, Nat>, U32, z => LK.lastl(z, D.nil()), SC.snoc(Nat, a1, x), ap, esn), lastl_snoc(a1, x, D.nil()))
      +vv = SC.append(T, DS.vals(T, ST.items(T, xs, a1)), Con{v, acc})
      +lhs = Equal.trans(D.Cur<T>, D.walk(~T, 1n+SC.length(Nat, rt), wcur(~T, tv, tp, acc, LK.lastl(SC.snoc(Nat, a1, x), D.nil()))), D.walk(~T, SC.length(Nat, rt), D.step_back(~T, wcur(~T, tv, tp, acc, ST.ln(x)))), wcur(~T, tv, tp, vv, D.nil()),
        Equal.cong(U32, D.Cur<T>, z => D.walk(~T, 1n+SC.length(Nat, rt), wcur(~T, tv, tp, acc, z)), LK.lastl(SC.snoc(Nat, a1, x), D.nil()), ST.ln(x), elast),
        Equal.trans(D.Cur<T>, D.walk(~T, SC.length(Nat, rt), D.step_back(~T, wcur(~T, tv, tp, acc, ST.ln(x)))), D.walk(~T, SC.length(Nat, rt), wcur(~T, tv, tp, Con{v, acc}, ST.lat(ps, x))), wcur(~T, tv, tp, vv, D.nil()),
          Equal.cong(D.Cur<T>, D.Cur<T>, c => D.walk(~T, SC.length(Nat, rt), c), D.step_back(~T, wcur(~T, tv, tp, acc, ST.ln(x))), wcur(~T, tv, tp, Con{v, acc}, ST.lat(ps, x)), step_back_ok(~T, depth, tv, tp, acc, x, hd, pfv, pfp, hx, hs)),
          Equal.trans(D.Cur<T>, D.walk(~T, SC.length(Nat, rt), wcur(~T, tv, tp, Con{v, acc}, ST.lat(ps, x))), D.walk(~T, SC.length(Nat, rt), wcur(~T, tv, tp, Con{v, acc}, LK.lastl(a1, D.nil()))), wcur(~T, tv, tp, vv, D.nil()),
            Equal.cong(U32, D.Cur<T>, z => D.walk(~T, SC.length(Nat, rt), wcur(~T, tv, tp, Con{v, acc}, z)), ST.lat(ps, x), LK.lastl(a1, D.nil()), lk_single_p(x, LK.lastl(a1, D.nil()), e, ps, ns, hkx)),
            ih)))
      +its = Equal.trans(List<&2, E.Item<T>>, ST.items(T, xs, SC.snoc(Nat, a1, x)), ST.items(T, xs, ap), SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}}),
        Equal.cong(List<&2, Nat>, List<&2, E.Item<T>>, z => ST.items(T, xs, z), SC.snoc(Nat, a1, x), ap, esn),
        Equal.trans(List<&2, E.Item<T>>, ST.items(T, xs, ap), SC.append(E.Item<T>, ST.items(T, xs, a1), ST.items(T, xs, Con{x, Nil{}})), SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}}),
          AL.items_app(T, xs, a1, Con{x, Nil{}}),
          Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a1), z), ST.items(T, xs, Con{x, Nil{}}), Con{E.Item{U32.from_nat(x), v}, Nil{}}, AL.itm_some(T, ST.vat(T, xs, x), x, Nil{}, hs))))
      +rhs = Equal.trans(List<&2, T>, SC.append(T, DS.vals(T, ST.items(T, xs, SC.snoc(Nat, a1, x))), acc), SC.append(T, DS.vals(T, SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}})), acc), vv,
        Equal.cong(List<&2, E.Item<T>>, List<&2, T>, z => SC.append(T, DS.vals(T, z), acc), ST.items(T, xs, SC.snoc(Nat, a1, x)), SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}}), its),
        Equal.trans(List<&2, T>, SC.append(T, DS.vals(T, SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}})), acc), SC.append(T, SC.append(T, DS.vals(T, ST.items(T, xs, a1)), Con{v, Nil{}}), acc), vv,
          Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, z, acc), DS.vals(T, SC.append(E.Item<T>, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}})), SC.append(T, DS.vals(T, ST.items(T, xs, a1)), Con{v, Nil{}}), vals_app(T, ST.items(T, xs, a1), Con{E.Item{U32.from_nat(x), v}, Nil{}})),
          LL.append_assoc(T, DS.vals(T, ST.items(T, xs, a1)), Con{v, Nil{}}, acc)))
      Equal.trans(D.Cur<T>, D.walk(~T, 1n+SC.length(Nat, rt), wcur(~T, tv, tp, acc, LK.lastl(SC.snoc(Nat, a1, x), D.nil()))), wcur(~T, tv, tp, vv, D.nil()), wcur(~T, tv, tp, SC.append(T, DS.vals(T, ST.items(T, xs, SC.snoc(Nat, a1, x))), acc), D.nil()),
        lhs,
        Equal.cong(List<&2, T>, D.Cur<T>, z => wcur(~T, tv, tp, z, D.nil()), vv, SC.append(T, DS.vals(T, ST.items(T, xs, SC.snoc(Nat, a1, x))), acc), Equal.sym(List<&2, T>, SC.append(T, DS.vals(T, ST.items(T, xs, SC.snoc(Nat, a1, x))), acc), vv, rhs)))


def tlfin(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, c: D.Cur<T>) -> D.DList<T> & List<&2, T>:
  D.tl_fin(~T, tag, U32.from_nat(fresh), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tn), c)

def lobs(~T: Data, r: D.DList<T> & List<&2, T>) -> D.DList<T> & E.Obs<T>:
  D.obs_list(~T, r)

def tlres(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +acc: List<&2, T>) -> D.DList<T> & List<&2, T>:
  (ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), acc)

def tolist_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ToList{}):
  +xs = AR.slots(Maybe<&2, T>, tv)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +r = SC.reverse(Nat, ord)
  +err = LL.spec_rev_rev(Nat, ord)
  +hl = L.subst(List<&2, Nat>, z => {ST.alllt(z, SC.pow2(depth)) == True{} : Bool}, ord, SC.reverse(Nat, r), Equal.sym(List<&2, Nat>, SC.reverse(Nat, r), ord, err), K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h)))
  +ha = L.subst(List<&2, Nat>, z => {AL.alive(T, xs, z) == True{} : Bool}, ord, SC.reverse(Nat, r), Equal.sym(List<&2, Nat>, SC.reverse(Nat, r), ord, err), AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +hk = L.subst(List<&2, Nat>, z => {ST.lk(z, D.nil(), D.nil(), ps, ns) == True{} : Bool}, ord, SC.reverse(Nat, r), Equal.sym(List<&2, Nat>, SC.reverse(Nat, r), ord, err), F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +w0 = walk_ok(~T, depth, tv, tp, ns, r, Nil{}, D.nil(), F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h), hl, ha, hk)
  +w1 = L.subst(List<&2, Nat>, z => {D.walk(~T, SC.length(Nat, r), wcur(~T, tv, tp, Nil{}, LK.lastl(z, D.nil()))) == wcur(~T, tv, tp, SC.append(T, DS.vals(T, ST.items(T, xs, z)), Nil{}), D.nil()) : D.Cur<T>}, SC.reverse(Nat, r), ord, err, w0)
  +w2 = L.subst(Nat, n => {D.walk(~T, n, wcur(~T, tv, tp, Nil{}, LK.lastl(ord, D.nil()))) == wcur(~T, tv, tp, SC.append(T, DS.vals(T, ST.items(T, xs, ord)), Nil{}), D.nil()) : D.Cur<T>}, SC.length(Nat, r), SC.length(Nat, ord), LL.length_rev(Nat, ord), w1)
  +w3 = L.subst(U32, z => {D.walk(~T, SC.length(Nat, ord), wcur(~T, tv, tp, Nil{}, z)) == wcur(~T, tv, tp, SC.append(T, DS.vals(T, ST.items(T, xs, ord)), Nil{}), D.nil()) : D.Cur<T>}, LK.lastl(ord, D.nil()), ST.lst(ord), Equal.sym(U32, ST.lst(ord), LK.lastl(ord, D.nil()), lst_lastl(ord)), w2)
  +vs = DS.vals(T, ST.items(T, xs, ord))
  +e1 = Equal.trans(D.DList<T> & List<&2, T>, tlfin(~T, tag, fresh, depth, tv, tp, tn, ord, D.walk(~T, SC.length(Nat, ord), wcur(~T, tv, tp, Nil{}, ST.lst(ord)))), tlfin(~T, tag, fresh, depth, tv, tp, tn, ord, wcur(~T, tv, tp, SC.append(T, vs, Nil{}), D.nil())), (ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), vs),
    Equal.cong(D.Cur<T>, D.DList<T> & List<&2, T>, c => tlfin(~T, tag, fresh, depth, tv, tp, tn, ord, c), D.walk(~T, SC.length(Nat, ord), wcur(~T, tv, tp, Nil{}, ST.lst(ord))), wcur(~T, tv, tp, SC.append(T, vs, Nil{}), D.nil()), w3),
    Equal.cong(List<&2, T>, D.DList<T> & List<&2, T>, z => tlres(~T, tag, fresh, depth, tv, tp, tn, ord, z), SC.append(T, vs, Nil{}), vs, LL.append_nil(T, vs)))
  K.mk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ToList{}, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.OList{vs},
    Equal.cong(D.DList<T> & List<&2, T>, D.DList<T> & E.Obs<T>, z => lobs(~T, z), tlfin(~T, tag, fresh, depth, tv, tp, tn, ord, D.walk(~T, SC.length(Nat, ord), wcur(~T, tv, tp, Nil{}, ST.lst(ord)))), (ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), vs), e1),
    h, {==}, K.same_fresh(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ToList{}))

