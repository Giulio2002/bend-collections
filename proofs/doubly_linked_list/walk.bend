import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../lib/array.bend as AR
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/doubly_linked_list.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/doubly_linked_list.bend as D
import ../../src/containers/internal/dlist_storage.bend as R
import ../../src/containers/types/doubly_linked_list.bend as E
import ../hash_table/table.bend as TB
import ../lru/state.bend as LST
import ../lru/meta.bend as MT
import ../lru/walk.bend as WK
import ./state.bend as ST
import ./rel.bend as RL
import ./vals.bend as VA
import ./link.bend as LN
import ./ok.bend as OK

# to_list: the walk back from the tail along the prev links.


# every id of back is below fr and live, and its prev is the next id of back
def rok(~T: Data, +pl: List<&2, U32>, back: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>) -> Bool:
  match back:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), Bool.and(U32.is_eq(TB.nth0(pl, x), LST.fst_or(r, 0)), rok(~T, pl, r, fr, vl)))

# the values of back prepended to acc, one by one
def racc(-T: Data, +vl: List<&2, Maybe<&2, T>>, back: List<&2, Nat>, acc: List<&2, T>) -> List<&2, T>:
  match back:
    case Nil{}:
      acc
    case Con{+x, r}:
      racc(T, vl, r, S.cons_some(T, S.val_of(T, vl, x), acc))

def cs_app(-T: Data, +m: Maybe<&2, T>, +xs: List<&2, T>, +acc: List<&2, T>) -> {SC.append(T, S.cons_some(T, m, xs), acc) == S.cons_some(T, m, SC.append(T, xs, acc)) : List<&2, T>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def ra_rapp(-T: Data, +vl: List<&2, Maybe<&2, T>>, +l: List<&2, Nat>, +b: List<&2, Nat>, +acc: List<&2, T>) -> {racc(T, vl, WK.rapp(l, b), acc) == racc(T, vl, b, SC.append(T, S.values(T, vl, l), acc)) : List<&2, T>}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(List<&2, T>, racc(T, vl, WK.rapp(r, Con{x, b}), acc), racc(T, vl, b, S.cons_some(T, S.val_of(T, vl, x), SC.append(T, S.values(T, vl, r), acc))), racc(T, vl, b, SC.append(T, S.cons_some(T, S.val_of(T, vl, x), S.values(T, vl, r)), acc)), ra_rapp(T, vl, r, Con{x, b}, acc), Equal.cong(List<&2, T>, List<&2, T>, z => racc(T, vl, b, z), S.cons_some(T, S.val_of(T, vl, x), SC.append(T, S.values(T, vl, r), acc)), SC.append(T, S.cons_some(T, S.val_of(T, vl, x), S.values(T, vl, r)), acc), Equal.sym(List<&2, T>, SC.append(T, S.cons_some(T, S.val_of(T, vl, x), S.values(T, vl, r)), acc), S.cons_some(T, S.val_of(T, vl, x), SC.append(T, S.values(T, vl, r), acc)), cs_app(T, S.val_of(T, vl, x), S.values(T, vl, r), acc))))

# a linked live list, reversed onto a back list, keeps its links backwards
def rok_app(~T: Data, +pl: List<&2, U32>, +nl: List<&2, U32>, +vl: List<&2, Maybe<&2, T>>, +l: List<&2, Nat>, +b: List<&2, Nat>, +fr: Nat, +p: U32, +q: U32, +hs: {ST.seg(pl, nl, l, p, q) == True{} : Bool}, +hl: {ST.slok(~T, l, fr, vl) == True{} : Bool}, +hb: {rok(~T, pl, b, fr, vl) == True{} : Bool}, +hp: {U32.is_eq(p, LST.fst_or(b, 0)) == True{} : Bool}) -> {rok(~T, pl, WK.rapp(l, b), fr, vl) == True{} : Bool}:
  match l:
    case Nil{}:
      hb
    case Con{+x, +r}:
      +ha = L.and_left(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(nl, x), LST.fst_or(r, q)), ST.seg(pl, nl, r, LST.lnk(x), q)), hs)
      +hc = L.and_right(U32.is_eq(TB.nth0(nl, x), LST.fst_or(r, q)), ST.seg(pl, nl, r, LST.lnk(x), q), L.and_right(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(nl, x), LST.fst_or(r, q)), ST.seg(pl, nl, r, LST.lnk(x), q)), hs))
      +hx = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, r, fr, vl), hl)
      +hlr = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, r, fr, vl), hl)
      +e0 = A.eq_of(TB.nth0(pl, x), p, ha)
      +hq = L.subst(U32, z => {U32.is_eq(z, LST.fst_or(b, 0)) == True{} : Bool}, p, TB.nth0(pl, x), Equal.sym(U32, TB.nth0(pl, x), p, e0), hp)
      +hb2 = L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), Bool.and(U32.is_eq(TB.nth0(pl, x), LST.fst_or(b, 0)), rok(~T, pl, b, fr, vl)), hx, L.and_intro(U32.is_eq(TB.nth0(pl, x), LST.fst_or(b, 0)), rok(~T, pl, b, fr, vl), hq, hb))
      rok_app(~T, pl, nl, vl, r, Con{x, b}, fr, LST.lnk(x), q, hc, hlr, hb2, A.eq_refl(LST.lnk(x)))

# ---- the walk ----



def step_live(-T: Data, +acc: List<&2, T>, +at: U32, +m: Maybe<&2, T>, +hm: {ST.some_b(T, m) == True{} : Bool}, -vals: Array<Maybe<&2, T>>, -prevs: Array<U32>) -> {R.step_m(~T, vals, prevs, acc, at, m) == R.step_p(~T, vals, S.cons_some(T, m, acc), Array.get(U32, prevs, R.slot(at))) : R.Cur<T>}:
  match m:
    case None{}:
      Empty.absurd({R.step_m(~T, vals, prevs, acc, at, None{}) == R.step_p(~T, vals, acc, Array.get(U32, prevs, R.slot(at))) : R.Cur<T>}, L.false_true(hm))
    case Some{v}:
      {==}

# one step: the value of x is prepended and the walk moves to x's prev
def wstep(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pT: AR.Tree<U32>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +pp: {AR.perfect(U32, d, pT) == True{} : Bool}, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(d)) == True{} : Bool}, +x: Nat, +r: List<&2, Nat>, +acc: List<&2, T>, +hx: {Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x)), Bool.and(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT)))) == True{} : Bool}) -> {R.step_back(~T, R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.lnk(x)}) == R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)} : R.Cur<T>}:
  +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x)), Bool.and(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT))), hx)
  +h2 = L.and_left(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT)), L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x)), Bool.and(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT))), hx))
  +hn = N.lt_le_trans(x, fr, SC.pow2(d), L.and_left(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x), h0), hfr)
  +es = RL.slot_lnk(one, h1, x, d, hd, hn)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, x, UD.v(R.slot(LST.lnk(x))), Equal.sym(Nat, UD.v(R.slot(LST.lnk(x))), x, es), hn)
  +e1 = Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, R.Cur<T>, rr => R.step_v(~T, AR.thaw(U32, pT), acc, LST.lnk(x), rr), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), R.slot(LST.lnk(x))), (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), x)), Equal.trans(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, vT), R.slot(LST.lnk(x))), (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), UD.v(R.slot(LST.lnk(x))))), (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), x)), LN.vget(T, d, hd, vT, pv, R.slot(LST.lnk(x)), hi), Equal.cong(Nat, Array<Maybe<&2, T>> & Maybe<&2, T>, z => (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), z)), UD.v(R.slot(LST.lnk(x))), x, es)))
  +e2 = step_live(T, acc, LST.lnk(x), S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), L.and_right(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x), h0), AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT))
  +e3 = Equal.cong(Array<U32> & U32, R.Cur<T>, rr => R.step_p(~T, AR.thaw(Maybe<&2, T>, vT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), rr), Array.get(U32, AR.thaw(U32, pT), R.slot(LST.lnk(x))), (AR.thaw(U32, pT), TB.nth0(AR.slots(U32, pT), x)), Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, pT), R.slot(LST.lnk(x))), (AR.thaw(U32, pT), TB.nth0(AR.slots(U32, pT), UD.v(R.slot(LST.lnk(x))))), (AR.thaw(U32, pT), TB.nth0(AR.slots(U32, pT), x)), MT.uget(d, RL.hd0(d, hd), pT, pp, R.slot(LST.lnk(x)), hi), Equal.cong(Nat, Array<U32> & U32, z => (AR.thaw(U32, pT), TB.nth0(AR.slots(U32, pT), z)), UD.v(R.slot(LST.lnk(x))), x, es)))
  +e4 = Equal.cong(U32, R.Cur<T>, z => R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), z}, TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0), A.eq_of(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0), h2))
  Equal.trans(R.Cur<T>, R.step_back(~T, R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.lnk(x)}), R.step_v(~T, AR.thaw(U32, pT), acc, LST.lnk(x), (AR.thaw(Maybe<&2, T>, vT), S.val_of(T, AR.slots(Maybe<&2, T>, vT), x))), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)}, e1, Equal.trans(R.Cur<T>, R.step_m(~T, AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.lnk(x), S.val_of(T, AR.slots(Maybe<&2, T>, vT), x)), R.step_p(~T, AR.thaw(Maybe<&2, T>, vT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), Array.get(U32, AR.thaw(U32, pT), R.slot(LST.lnk(x)))), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)}, e2, Equal.trans(R.Cur<T>, R.step_p(~T, AR.thaw(Maybe<&2, T>, vT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), Array.get(U32, AR.thaw(U32, pT), R.slot(LST.lnk(x)))), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), TB.nth0(AR.slots(U32, pT), x)}, R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)}, e3, e4)))

# THEOREM: the walk from the first id of back, for its length, prepends the
# values of back one by one
def walk(~T: Data, +one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 30n) == True{} : Bool}, +vT: AR.Tree<Maybe<&2, T>>, +pT: AR.Tree<U32>, +pv: {AR.perfect(Maybe<&2, T>, d, vT) == True{} : Bool}, +pp: {AR.perfect(U32, d, pT) == True{} : Bool}, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(d)) == True{} : Bool}, +back: List<&2, Nat>, +acc: List<&2, T>, +hr: {rok(~T, AR.slots(U32, pT), back, fr, AR.slots(Maybe<&2, T>, vT)) == True{} : Bool}) -> {R.walk(~T, SC.length(Nat, back), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.fst_or(back, 0)}) == R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), racc(T, AR.slots(Maybe<&2, T>, vT), back, acc), 0} : R.Cur<T>}:
  match back:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +ih = walk(~T, one, h1, d, hd, vT, pT, pv, pp, fr, hfr, r, S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), L.and_right(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT)), L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, AR.slots(Maybe<&2, T>, vT), x)), Bool.and(U32.is_eq(TB.nth0(AR.slots(U32, pT), x), LST.fst_or(r, 0)), rok(~T, AR.slots(U32, pT), r, fr, AR.slots(Maybe<&2, T>, vT))), hr)))
      Equal.trans(R.Cur<T>, R.walk(~T, SC.length(Nat, r), R.step_back(~T, R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.lnk(x)})), R.walk(~T, SC.length(Nat, r), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)}), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), racc(T, AR.slots(Maybe<&2, T>, vT), r, S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc)), 0}, Equal.cong(R.Cur<T>, R.Cur<T>, c => R.walk(~T, SC.length(Nat, r), c), R.step_back(~T, R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), acc, LST.lnk(x)}), R.C{AR.thaw(Maybe<&2, T>, vT), AR.thaw(U32, pT), S.cons_some(T, S.val_of(T, AR.slots(Maybe<&2, T>, vT), x), acc), LST.fst_or(r, 0)}, wstep(~T, one, h1, d, hd, vT, pT, pv, pp, fr, hfr, x, r, acc, hr)), ih)
