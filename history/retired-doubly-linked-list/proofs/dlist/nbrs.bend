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

# next and prev: a link read from the arena is the spec's neighbour.

def ueq_true(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  NO.is_eq_eq(a, b, h)

# The handle a link denotes, against the spec's handle of the linked id.
def HR(+tag: U32, +pv: U32, pm: Maybe<&2, U32>) -> Type:
  {D.handle(tag, pv) == DS.handle(tag, pm) : Maybe<&2, E.Handle>}

def hr_nil(+tag: U32) -> HR(tag, D.nil(), None{}):
  {==}

def hr_ln(+tag: U32, +x: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> HR(tag, ST.ln(x), Some{U32.from_nat(x)}):
  +e0 = F.ln_ne_nil(x, depth, hd, hx)
  Equal.trans(Maybe<&2, E.Handle>, D.handle_go(tag, ST.ln(x), U32.is_eq(ST.ln(x), D.nil())), D.handle_go(tag, ST.ln(x), False{}), Some{E.H{tag, U32.from_nat(x)}},
    Equal.cong(Bool, Maybe<&2, E.Handle>, b => D.handle_go(tag, ST.ln(x), b), U32.is_eq(ST.ln(x), D.nil()), False{}, e0),
    Equal.cong(U32, Maybe<&2, E.Handle>, z => Some{E.H{tag, z}}, D.slot(ST.ln(x)), U32.from_nat(x), F.slot_ln(x, depth, hd, hx)))

def items_cons(-T: Data, +xs: List<&2, Maybe<&2, T>>, +x: Nat, +t: List<&2, Nat>, +h: {AL.alive(T, xs, Con{x, t}) == True{} : Bool}) -> {ST.items(T, xs, Con{x, t}) == Con{E.Item{U32.from_nat(x), AL.val_of(T, ST.vat(T, xs, x), L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), h))}, ST.items(T, xs, t)} : List<&2, E.Item<T>>}:
  AL.itm_some(T, ST.vat(T, xs, x), x, ST.items(T, xs, t), L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), h))

# the handle of the first item after a live head
def first_hr(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +t: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(t, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, t) == True{} : Bool}) -> HR(tag, ST.hd_or(t, D.nil()), DS.first_id(T, ST.items(T, xs, t))):
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      L.subst(List<&2, E.Item<T>>, z => HR(tag, ST.ln(y), DS.first_id(T, z)), Con{E.Item{U32.from_nat(y), AL.val_of(T, ST.vat(T, xs, y), L.and_left(ST.is_some(T, ST.vat(T, xs, y)), AL.alive(T, xs, r), ha))}, ST.items(T, xs, r)}, ST.items(T, xs, Con{y, r}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{y, r}), Con{E.Item{U32.from_nat(y), AL.val_of(T, ST.vat(T, xs, y), L.and_left(ST.is_some(T, ST.vat(T, xs, y)), AL.alive(T, xs, r), ha))}, ST.items(T, xs, r)}, items_cons(T, xs, y, r, ha)),
        hr_ln(tag, y, depth, hd, IT.lt_head(y, r, SC.pow2(depth), hl)))

# ---- following next / prev links along the order ----

def or_false_true(+b: Bool, +h: {Bool.or(False{}, b) == True{} : Bool}) -> {b == True{} : Bool}:
  h

def lmem_nil(+n: Nat, +h: {ST.lmem(n, Nil{}) == True{} : Bool}) -> Empty:
  L.false_true(h)

def NxIH(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +t: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +x: Nat) -> Type:
  @+hl: {ST.alllt(t, SC.pow2(depth)) == True{} : Bool} -> @+ha: {AL.alive(T, xs, t) == True{} : Bool} -> @+hk: {ST.lk(t, ST.ln(x), D.nil(), ps, ns) == True{} : Bool} -> @+hm: {ST.lmem(U32.to_nat(i), t) == True{} : Bool} -> HR(tag, ST.lat(ns, U32.to_nat(i)), DS.next_of(T, ST.items(T, xs, t), i))

def nx_c(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +x: Nat, +t: List<&2, Nat>, +pv: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(Con{x, t}, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, Con{x, t}) == True{} : Bool}, +hk: {ST.lk(Con{x, t}, pv, D.nil(), ps, ns) == True{} : Bool}, +hm: {ST.lmem(U32.to_nat(i), Con{x, t}) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(x, U32.to_nat(i)) == c : Bool}, ih: NxIH(T, tag, xs, t, ps, ns, i, depth, x)) -> HR(tag, ST.lat(ns, U32.to_nat(i)), DS.pickm(c, DS.first_id(T, ST.items(T, xs, t)), DS.next_of(T, ST.items(T, xs, t), i))):
  match c:
    case True{}:
      +en = IT.eq_nat_true(x, U32.to_nat(i), ec)
      +hk2 = L.and_left(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns), L.and_right(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns)), hk))
      +el = ueq_true(ST.lat(ns, x), ST.hd_or(t, D.nil()), hk2)
      L.subst(Nat, z => HR(tag, ST.lat(ns, z), DS.first_id(T, ST.items(T, xs, t))), x, U32.to_nat(i), en,
        L.subst(U32, z => HR(tag, z, DS.first_id(T, ST.items(T, xs, t))), ST.hd_or(t, D.nil()), ST.lat(ns, x), Equal.sym(U32, ST.lat(ns, x), ST.hd_or(t, D.nil()), el),
          first_hr(T, tag, xs, t, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha))))
    case False{}:
      +hm2 = L.subst(Bool, b => {Bool.or(b, ST.lmem(U32.to_nat(i), t)) == True{} : Bool}, Nat.is_eq(x, U32.to_nat(i)), False{}, ec, hm)
      +hkt = L.and_right(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns), L.and_right(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns)), hk))
      ih(IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha), hkt, hm2)

def nx_lemma(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +ord: List<&2, Nat>, +pv: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, ord) == True{} : Bool}, +hk: {ST.lk(ord, pv, D.nil(), ps, ns) == True{} : Bool}, +hm: {ST.lmem(U32.to_nat(i), ord) == True{} : Bool}) -> HR(tag, ST.lat(ns, U32.to_nat(i)), DS.next_of(T, ST.items(T, xs, ord), i)):
  match ord:
    case Nil{}:
      Empty.absurd(HR(tag, ST.lat(ns, U32.to_nat(i)), DS.next_of(T, ST.items(T, xs, Nil{}), i)), lmem_nil(U32.to_nat(i), hm))
    case Con{+x, +t}:
      +hx = IT.lt_head(x, t, SC.pow2(depth), hl)
      +ex = IT.ueq(x, i, depth, hd, hx)
      +vx = AL.val_of(T, ST.vat(T, xs, x), L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha))
      L.subst(List<&2, E.Item<T>>, z => HR(tag, ST.lat(ns, U32.to_nat(i)), DS.next_of(T, z, i)), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, ST.items(T, xs, Con{x, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{x, t}), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, items_cons(T, xs, x, t, ha)),
        L.subst(Bool, b => HR(tag, ST.lat(ns, U32.to_nat(i)), DS.pickm(b, DS.first_id(T, ST.items(T, xs, t)), DS.next_of(T, ST.items(T, xs, t), i))), Nat.is_eq(x, U32.to_nat(i)), U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), Nat.is_eq(x, U32.to_nat(i)), ex),
          nx_c(T, tag, xs, x, t, pv, ps, ns, i, depth, hd, hl, ha, hk, hm, Nat.is_eq(x, U32.to_nat(i)), {==}, hl2 => ha2 => hk2 => hm2 => nx_lemma(T, tag, xs, t, ST.ln(x), ps, ns, i, depth, hd, hl2, ha2, hk2, hm2))))

def PvIH(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +t: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +x: Nat) -> Type:
  @+hl: {ST.alllt(t, SC.pow2(depth)) == True{} : Bool} -> @+ha: {AL.alive(T, xs, t) == True{} : Bool} -> @+hk: {ST.lk(t, ST.ln(x), D.nil(), ps, ns) == True{} : Bool} -> @+hr: {D.handle(tag, ST.ln(x)) == DS.handle(tag, Some{U32.from_nat(x)}) : Maybe<&2, E.Handle>} -> @+hm: {ST.lmem(U32.to_nat(i), t) == True{} : Bool} -> HR(tag, ST.lat(ps, U32.to_nat(i)), DS.prev_of(T, ST.items(T, xs, t), i, Some{U32.from_nat(x)}))

def pv_c(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +x: Nat, +t: List<&2, Nat>, +pv: U32, +pm: Maybe<&2, U32>, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(Con{x, t}, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, Con{x, t}) == True{} : Bool}, +hk: {ST.lk(Con{x, t}, pv, D.nil(), ps, ns) == True{} : Bool}, +hr: {D.handle(tag, pv) == DS.handle(tag, pm) : Maybe<&2, E.Handle>}, +hm: {ST.lmem(U32.to_nat(i), Con{x, t}) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(x, U32.to_nat(i)) == c : Bool}, ih: PvIH(T, tag, xs, t, ps, ns, i, depth, x)) -> HR(tag, ST.lat(ps, U32.to_nat(i)), DS.pickm(c, pm, DS.prev_of(T, ST.items(T, xs, t), i, Some{U32.from_nat(x)}))):
  match c:
    case True{}:
      +en = IT.eq_nat_true(x, U32.to_nat(i), ec)
      +hk1 = L.and_left(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns)), hk)
      +el = ueq_true(ST.lat(ps, x), pv, hk1)
      L.subst(Nat, z => HR(tag, ST.lat(ps, z), pm), x, U32.to_nat(i), en,
        L.subst(U32, z => HR(tag, z, pm), pv, ST.lat(ps, x), Equal.sym(U32, ST.lat(ps, x), pv, el), hr))
    case False{}:
      +hm2 = L.subst(Bool, b => {Bool.or(b, ST.lmem(U32.to_nat(i), t)) == True{} : Bool}, Nat.is_eq(x, U32.to_nat(i)), False{}, ec, hm)
      +hkt = L.and_right(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns), L.and_right(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, D.nil())), ST.lk(t, ST.ln(x), D.nil(), ps, ns)), hk))
      ih(IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha), hkt, hr_ln(tag, x, depth, hd, IT.lt_head(x, t, SC.pow2(depth), hl)), hm2)

def pv_lemma(-T: Data, +tag: U32, +xs: List<&2, Maybe<&2, T>>, +ord: List<&2, Nat>, +pv: U32, +pm: Maybe<&2, U32>, +ps: List<&2, U32>, +ns: List<&2, U32>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, ord) == True{} : Bool}, +hk: {ST.lk(ord, pv, D.nil(), ps, ns) == True{} : Bool}, +hr: {D.handle(tag, pv) == DS.handle(tag, pm) : Maybe<&2, E.Handle>}, +hm: {ST.lmem(U32.to_nat(i), ord) == True{} : Bool}) -> HR(tag, ST.lat(ps, U32.to_nat(i)), DS.prev_of(T, ST.items(T, xs, ord), i, pm)):
  match ord:
    case Nil{}:
      Empty.absurd(HR(tag, ST.lat(ps, U32.to_nat(i)), DS.prev_of(T, ST.items(T, xs, Nil{}), i, pm)), lmem_nil(U32.to_nat(i), hm))
    case Con{+x, +t}:
      +hx = IT.lt_head(x, t, SC.pow2(depth), hl)
      +ex = IT.ueq(x, i, depth, hd, hx)
      +vx = AL.val_of(T, ST.vat(T, xs, x), L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha))
      L.subst(List<&2, E.Item<T>>, z => HR(tag, ST.lat(ps, U32.to_nat(i)), DS.prev_of(T, z, i, pm)), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, ST.items(T, xs, Con{x, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{x, t}), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, items_cons(T, xs, x, t, ha)),
        L.subst(Bool, b => HR(tag, ST.lat(ps, U32.to_nat(i)), DS.pickm(b, pm, DS.prev_of(T, ST.items(T, xs, t), i, Some{U32.from_nat(x)}))), Nat.is_eq(x, U32.to_nat(i)), U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), Nat.is_eq(x, U32.to_nat(i)), ex),
          pv_c(T, tag, xs, x, t, pv, pm, ps, ns, i, depth, hd, hl, ha, hk, hr, hm, Nat.is_eq(x, U32.to_nat(i)), {==}, hl2 => ha2 => hk2 => hr2 => hm2 => pv_lemma(T, tag, xs, t, ST.ln(x), Some{U32.from_nat(x)}, ps, ns, i, depth, hd, hl2, ha2, hk2, hr2, hm2))))

# ---- the step ----

def live_of(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +v: T, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}) -> {ST.lmem(U32.to_nat(i), ord) == True{} : Bool}:
  +xs = AR.slots(Maybe<&2, T>, tv)
  +n = U32.to_nat(i)
  +hb = L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, z)), ST.lmem(z, ord)) == True{} : Bool}, Nat.add(n, 0n), n, N.add_zero(n), K.lv_get(T, fresh, xs, 0n, ord, F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h), n, hi))
  L.subst(Maybe<&2, T>, m => {ST.beq(ST.is_some(T, m), ST.lmem(n, ord)) == True{} : Bool}, ST.vat(T, xs, n), Some{v}, Equal.trans(Maybe<&2, T>, ST.vat(T, xs, n), RD.xv(~T, tv, i), Some{v}, RD.vat_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi), em), hb)

def read_l(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +t: AR.Tree<U32>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +pt: {AR.perfect(U32, depth, t) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, t), i) == (AR.thaw(U32, t), ST.lat(AR.slots(U32, t), U32.to_nat(i))) : Array<U32> & U32}:
  AR.get(U32, depth, t, i, ST.lat(AR.slots(U32, t), U32.to_nat(i)), N.le_lt_trans(depth, 31n, 32n, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.lt_succ(31n)), RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi), AS2.tsat(U32, depth, t, U32.to_nat(i), 0, pt, RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)), pt)

def sel(-T: Data, after: Bool, +its: List<&2, E.Item<T>>, +i: U32) -> Maybe<&2, U32>:
  match after:
    case True{}:
      DS.next_of(T, its, i)
    case False{}:
      DS.prev_of(T, its, i, None{})

def nfin(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +r: Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  (ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), r)

def done_h(+r: Maybe<&2, E.Handle>) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>:
  Done{r}

def nfin_eq(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, after: Bool, m: Maybe<&2, T>, +em: {RD.xv(~T, tv, i) == m : Maybe<&2, T>}) -> {D.nbr_fin(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, m) == nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, m), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match after m:
    case True{} None{}:
      {==}
    case False{} None{}:
      {==}
    case True{} Some{v}:
      +hm = live_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, v, em)
      Equal.trans(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.nbr_n(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), Array.get(U32, AR.thaw(U32, tn), i)), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(D.handle(tag, ST.lat(AR.slots(U32, tn), U32.to_nat(i))))), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(DS.handle(tag, DS.next_of(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))),
        Equal.cong(Array<U32> & U32, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.nbr_n(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), r), Array.get(U32, AR.thaw(U32, tn), i), (AR.thaw(U32, tn), ST.lat(AR.slots(U32, tn), U32.to_nat(i))), read_l(~T, tag, fresh, depth, tv, tp, tn, ord, tn, i, h, F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi)),
        Equal.cong(Maybe<&2, E.Handle>, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, z => nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(z)), D.handle(tag, ST.lat(AR.slots(U32, tn), U32.to_nat(i))), DS.handle(tag, DS.next_of(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)),
          nx_lemma(T, tag, AR.slots(Maybe<&2, T>, tv), ord, D.nil(), AR.slots(U32, tp), AR.slots(U32, tn), i, depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h)), AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h), hm)))
    case False{} Some{v}:
      +hm = live_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, v, em)
      Equal.trans(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.nbr_p(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tn), Array.get(U32, AR.thaw(U32, tp), i)), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(D.handle(tag, ST.lat(AR.slots(U32, tp), U32.to_nat(i))))), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(DS.handle(tag, DS.prev_of(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i, None{})))),
        Equal.cong(Array<U32> & U32, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.nbr_p(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tn), r), Array.get(U32, AR.thaw(U32, tp), i), (AR.thaw(U32, tp), ST.lat(AR.slots(U32, tp), U32.to_nat(i))), read_l(~T, tag, fresh, depth, tv, tp, tn, ord, tp, i, h, F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi)),
        Equal.cong(Maybe<&2, E.Handle>, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, z => nfin(~T, tag, fresh, depth, tv, tp, tn, ord, done_h(z)), D.handle(tag, ST.lat(AR.slots(U32, tp), U32.to_nat(i))), DS.handle(tag, DS.prev_of(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i, None{})),
          pv_lemma(T, tag, AR.slots(Maybe<&2, T>, tv), ord, D.nil(), None{}, AR.slots(U32, tp), AR.slots(U32, tn), i, depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h)), AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h), hr_nil(tag), hm)))

def nbr_eq(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, after: Bool, ok: Bool, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == ok : Bool}, same: Bool) -> {D.nbr_checked(~T, after, ok, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, same) == nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, same, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))) : D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>}:
  match ok same:
    case True{} False{}:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      Equal.cong(Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, m => nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, m), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))), None{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, RD.getv_ok_false(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)))
    case True{} True{}:
      +hi = RD.hi_ok(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)
      Equal.trans(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.nbr_read(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i)), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, RD.xv(~T, tv, i)), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))),
        Equal.trans(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.nbr_read(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i)), D.nbr_read(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i))), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, RD.xv(~T, tv, i)), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))),
          Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, r => D.nbr_read(~T, after, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, r), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), (AR.thaw(Maybe<&2, T>, tv), RD.xv(~T, tv, i)), RD.read_v(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)),
          nfin_eq(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, after, RD.xv(~T, tv, i), {==})),
        Equal.cong(Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, m => nfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.nbr(DS.check(T, True{}, m), DS.handle(tag, sel(T, after, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)))), RD.xv(~T, tv, i), DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), RD.xv(~T, tv, i), RD.getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))))

def nobs(~T: Data, r: D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> D.DList<T> & E.Obs<T>:
  D.obs_nbr(~T, r)

def next_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Next{E.H{l, i}}):
  +its = ST.items(T, AR.slots(Maybe<&2, T>, tv), ord)
  +r = DS.nbr(DS.check(T, U32.is_eq(l, tag), DS.getv(T, its, i)), DS.handle(tag, DS.next_of(T, its, i)))
  K.mk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Next{E.H{l, i}}, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ONbr{r},
    Equal.cong(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.DList<T> & E.Obs<T>, z => nobs(~T, z), D.nbr_checked(~T, True{}, U32.is_lt(i, U32.from_nat(fresh)), tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, U32.is_eq(l, tag)), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, r),
      nbr_eq(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h, True{}, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))),
    h, {==}, K.same_fresh(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Next{E.H{l, i}}))

def prev_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Prev{E.H{l, i}}):
  +its = ST.items(T, AR.slots(Maybe<&2, T>, tv), ord)
  +r = DS.nbr(DS.check(T, U32.is_eq(l, tag), DS.getv(T, its, i)), DS.handle(tag, DS.prev_of(T, its, i, None{})))
  K.mk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Prev{E.H{l, i}}, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ONbr{r},
    Equal.cong(D.DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>, D.DList<T> & E.Obs<T>, z => nobs(~T, z), D.nbr_checked(~T, False{}, U32.is_lt(i, U32.from_nat(fresh)), tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, U32.is_eq(l, tag)), nfin(~T, tag, fresh, depth, tv, tp, tn, ord, r),
      nbr_eq(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h, False{}, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))),
    h, {==}, K.same_fresh(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Prev{E.H{l, i}}))
