import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../graph/ashift.bend as AS2
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

# length and get, and the handle validation every handle operation shares.
import ./reads.bend as RD
import ./nbrs.bend as NB

# set and remove.

# ---- list facts ----

def upd_upd(-A: Data, +xs: List<&2, A>, +n: Nat, +a: A, +b: A) -> {SC.update(A, SC.update(A, xs, n, a), n, b) == SC.update(A, xs, n, b) : List<&2, A>}:
  match xs n:
    case Nil{} n0:
      {==}
    case Con{+h, +t} 0n:
      {==}
    case Con{+h, +t} 1n+p:
      LL.cons_cong(A, h, SC.update(A, SC.update(A, t, p, a), p, b), SC.update(A, t, p, b), upd_upd(A, t, p, a, b))

def upd_self(-A: Data, +xs: List<&2, A>, +n: Nat, +y: A, +h: {SC.nth(A, xs, n) == Some{y} : Maybe<&2, A>}) -> {SC.update(A, xs, n, y) == xs : List<&2, A>}:
  match xs n:
    case Nil{} n0:
      {==}
    case Con{+hh, +t} 0n:
      Equal.cong(A, List<&2, A>, z => Con{z, t}, y, hh, Equal.sym(A, hh, y, IT.eq_some(A, hh, y, h)))
    case Con{+hh, +t} 1n+p:
      LL.cons_cong(A, hh, SC.update(A, t, p, y), t, upd_self(A, t, p, y, h))

# ---- the model under a value update ----

def items_frame(-T: Data, +xs: List<&2, Maybe<&2, T>>, +ys: List<&2, Nat>, +n: Nat, +m: Maybe<&2, T>, +h: {ST.lmem(n, ys) == False{} : Bool}) -> {ST.items(T, SC.update(Maybe<&2, T>, xs, n, m), ys) == ST.items(T, xs, ys) : List<&2, E.Item<T>>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = LK.or_false_l(Nat.is_eq(y, n), ST.lmem(n, t), h)
      +ht = LK.or_false_r(Nat.is_eq(y, n), ST.lmem(n, t), h)
      Equal.trans(List<&2, E.Item<T>>, ST.itm(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), y), y, ST.items(T, SC.update(Maybe<&2, T>, xs, n, m), t)), ST.itm(T, ST.vat(T, xs, y), y, ST.items(T, SC.update(Maybe<&2, T>, xs, n, m), t)), ST.items(T, xs, Con{y, t}),
        Equal.cong(Maybe<&2, T>, List<&2, E.Item<T>>, z => ST.itm(T, z, y, ST.items(T, SC.update(Maybe<&2, T>, xs, n, m), t)), ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), y), ST.vat(T, xs, y), LK.vat_other(T, xs, n, m, y, SH.ne_flip(y, n, hy))),
        Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => ST.itm(T, ST.vat(T, xs, y), y, z), ST.items(T, SC.update(Maybe<&2, T>, xs, n, m), t), ST.items(T, xs, t), items_frame(T, xs, t, n, m, ht)))

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

def SvIH(-T: Data, +xs: List<&2, Maybe<&2, T>>, +t: List<&2, Nat>, +i: U32, +x: T, +depth: Nat) -> Type:
  @+hl: {ST.alllt(t, SC.pow2(depth)) == True{} : Bool} -> @+hnd: {ST.nodup(t) == True{} : Bool} -> @+ha: {AL.alive(T, xs, t) == True{} : Bool} -> @+hm: {ST.lmem(U32.to_nat(i), t) == True{} : Bool} -> {ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), t) == DS.setv(T, ST.items(T, xs, t), i, x) : List<&2, E.Item<T>>}

def setv_c(-T: Data, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +t: List<&2, Nat>, +i: U32, +x: T, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(Con{p, t}, SC.pow2(depth)) == True{} : Bool}, +hnd: {ST.nodup(Con{p, t}) == True{} : Bool}, +ha: {AL.alive(T, xs, Con{p, t}) == True{} : Bool}, +hm: {ST.lmem(U32.to_nat(i), Con{p, t}) == True{} : Bool}, +hn: {Nat.is_lt(U32.to_nat(i), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(p, U32.to_nat(i)) == c : Bool}, ih: SvIH(T, xs, t, i, x, depth)) -> {ST.itm(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), p), p, ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), t)) == DS.pick(T, c, Con{E.Item{U32.from_nat(p), x}, ST.items(T, xs, t)}, Con{E.Item{U32.from_nat(p), AL.val_of(T, ST.vat(T, xs, p), L.and_left(ST.is_some(T, ST.vat(T, xs, p)), AL.alive(T, xs, t), ha))}, DS.setv(T, ST.items(T, xs, t), i, x)}) : List<&2, E.Item<T>>}:
  match c:
    case True{}:
      +n = U32.to_nat(i)
      +xs2 = SC.update(Maybe<&2, T>, xs, n, Some{x})
      +en = IT.eq_nat_true(p, n, ec)
      +hpt = not_true(ST.lmem(p, t), L.and_left(Bool.not(ST.lmem(p, t)), ST.nodup(t), hnd))
      +hnt = L.subst(Nat, z => {ST.lmem(z, t) == False{} : Bool}, p, n, en, hpt)
      +ev = L.subst(Nat, z => {ST.vat(T, xs2, z) == Some{x} : Maybe<&2, T>}, n, p, Equal.sym(Nat, p, n, en), LK.vat_same(T, xs, n, Some{x}, hn))
      Equal.trans(List<&2, E.Item<T>>, ST.itm(T, ST.vat(T, xs2, p), p, ST.items(T, xs2, t)), ST.itm(T, Some{x}, p, ST.items(T, xs2, t)), Con{E.Item{U32.from_nat(p), x}, ST.items(T, xs, t)},
        Equal.cong(Maybe<&2, T>, List<&2, E.Item<T>>, z => ST.itm(T, z, p, ST.items(T, xs2, t)), ST.vat(T, xs2, p), Some{x}, ev),
        LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(p), x}, ST.items(T, xs2, t), ST.items(T, xs, t), items_frame(T, xs, t, n, Some{x}, hnt)))
    case False{}:
      +n = U32.to_nat(i)
      +xs2 = SC.update(Maybe<&2, T>, xs, n, Some{x})
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, p)), AL.alive(T, xs, t), ha)
      +hm2 = L.subst(Bool, b => {Bool.or(b, ST.lmem(n, t)) == True{} : Bool}, Nat.is_eq(p, n), False{}, ec, hm)
      Equal.trans(List<&2, E.Item<T>>, ST.itm(T, ST.vat(T, xs2, p), p, ST.items(T, xs2, t)), ST.itm(T, ST.vat(T, xs, p), p, ST.items(T, xs2, t)), Con{E.Item{U32.from_nat(p), AL.val_of(T, ST.vat(T, xs, p), hy)}, DS.setv(T, ST.items(T, xs, t), i, x)},
        Equal.cong(Maybe<&2, T>, List<&2, E.Item<T>>, z => ST.itm(T, z, p, ST.items(T, xs2, t)), ST.vat(T, xs2, p), ST.vat(T, xs, p), LK.vat_other(T, xs, n, Some{x}, p, SH.ne_flip(p, n, ec))),
        Equal.trans(List<&2, E.Item<T>>, ST.itm(T, ST.vat(T, xs, p), p, ST.items(T, xs2, t)), Con{E.Item{U32.from_nat(p), AL.val_of(T, ST.vat(T, xs, p), hy)}, ST.items(T, xs2, t)}, Con{E.Item{U32.from_nat(p), AL.val_of(T, ST.vat(T, xs, p), hy)}, DS.setv(T, ST.items(T, xs, t), i, x)},
          AL.itm_some(T, ST.vat(T, xs, p), p, ST.items(T, xs2, t), hy),
          LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(p), AL.val_of(T, ST.vat(T, xs, p), hy)}, ST.items(T, xs2, t), DS.setv(T, ST.items(T, xs, t), i, x),
            ih(IT.lt_tail(p, t, SC.pow2(depth), hl), L.and_right(Bool.not(ST.lmem(p, t)), ST.nodup(t), hnd), L.and_right(ST.is_some(T, ST.vat(T, xs, p)), AL.alive(T, xs, t), ha), hm2))))

def items_setv(-T: Data, +xs: List<&2, Maybe<&2, T>>, +ord: List<&2, Nat>, +i: U32, +x: T, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(ord, SC.pow2(depth)) == True{} : Bool}, +hnd: {ST.nodup(ord) == True{} : Bool}, +ha: {AL.alive(T, xs, ord) == True{} : Bool}, +hm: {ST.lmem(U32.to_nat(i), ord) == True{} : Bool}, +hn: {Nat.is_lt(U32.to_nat(i), SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), ord) == DS.setv(T, ST.items(T, xs, ord), i, x) : List<&2, E.Item<T>>}:
  match ord:
    case Nil{}:
      Empty.absurd({ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), Nil{}) == DS.setv(T, ST.items(T, xs, Nil{}), i, x) : List<&2, E.Item<T>>}, NB.lmem_nil(U32.to_nat(i), hm))
    case Con{+p, +t}:
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, p)), AL.alive(T, xs, t), ha)
      +vp = AL.val_of(T, ST.vat(T, xs, p), hy)
      +eu = IT.ueq(p, i, depth, hd, IT.lt_head(p, t, SC.pow2(depth), hl))
      L.subst(List<&2, E.Item<T>>, z => {ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), Con{p, t}) == DS.setv(T, z, i, x) : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(p), vp}, ST.items(T, xs, t)}, ST.items(T, xs, Con{p, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{p, t}), Con{E.Item{U32.from_nat(p), vp}, ST.items(T, xs, t)}, AL.itm_some(T, ST.vat(T, xs, p), p, ST.items(T, xs, t), hy)),
        L.subst(Bool, b => {ST.items(T, SC.update(Maybe<&2, T>, xs, U32.to_nat(i), Some{x}), Con{p, t}) == DS.pick(T, b, Con{E.Item{U32.from_nat(p), x}, ST.items(T, xs, t)}, Con{E.Item{U32.from_nat(p), vp}, DS.setv(T, ST.items(T, xs, t), i, x)}) : List<&2, E.Item<T>>}, Nat.is_eq(p, U32.to_nat(i)), U32.is_eq(U32.from_nat(p), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(p), i), Nat.is_eq(p, U32.to_nat(i)), eu),
          setv_c(T, xs, p, t, i, x, depth, hd, hl, hnd, ha, hm, hn, Nat.is_eq(p, U32.to_nat(i)), {==}, hl2 => hn2 => ha2 => hm2 => items_setv(T, xs, t, i, x, depth, hd, hl2, hn2, ha2, hm2, hn))))

# ---- lv under a value update that keeps liveness ----

def lv_pos(-T: Data, +xs: List<&2, Maybe<&2, T>>, +n: Nat, +m: Maybe<&2, T>, +p: Nat, +hs: {ST.is_some(T, m) == ST.is_some(T, ST.vat(T, xs, n)) : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(n, p) == c : Bool}) -> {ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), p)) == ST.is_some(T, ST.vat(T, xs, p)) : Bool}:
  match c:
    case True{}:
      +en = IT.eq_nat_true(n, p, ec)
      L.subst(Nat, z => {ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), z)) == ST.is_some(T, ST.vat(T, xs, z)) : Bool}, n, p, en,
        Equal.trans(Bool, ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), n)), ST.is_some(T, m), ST.is_some(T, ST.vat(T, xs, n)),
          Equal.cong(Maybe<&2, T>, Bool, z => ST.is_some(T, z), ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), n), m, LK.vat_same(T, xs, n, m, hn)), hs))
    case False{}:
      Equal.cong(Maybe<&2, T>, Bool, z => ST.is_some(T, z), ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), p), ST.vat(T, xs, p), LK.vat_other(T, xs, n, m, p, ec))

def lv_upd(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +ord: List<&2, Nat>, +n: Nat, +m: Maybe<&2, T>, +hs: {ST.is_some(T, m) == ST.is_some(T, ST.vat(T, xs, n)) : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.lv(T, k, SC.update(Maybe<&2, T>, xs, n, m), p, ord) == ST.lv(T, k, xs, p, ord) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +k1:
      +es = lv_pos(T, xs, n, m, p, hs, hn, Nat.is_eq(n, p), {==})
      Equal.trans(Bool, Bool.and(ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), p)), ST.lmem(p, ord)), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, n, m), 1n+p, ord)), Bool.and(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, n, m), 1n+p, ord)), ST.lv(T, 1n+k1, xs, p, ord),
        Equal.cong(Bool, Bool, b => Bool.and(ST.beq(b, ST.lmem(p, ord)), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, n, m), 1n+p, ord)), ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, m), p)), ST.is_some(T, ST.vat(T, xs, p)), es),
        Equal.cong(Bool, Bool, b => Bool.and(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), b), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, n, m), 1n+p, ord), ST.lv(T, k1, xs, 1n+p, ord), lv_upd(T, k1, xs, 1n+p, ord, n, m, hs, hn)))


# ---- set ----

def SRT(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, ok: Bool, same: Bool) -> D.DList<T> & E.Obs<T>:
  D.obs_unit(~T, D.set_checked(~T, ok, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, x, same))

def SSP(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, same: Bool) -> DS.Model<T> & E.Obs<T>:
  DS.set_at(T, DS.check(T, same, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i)), tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i, x)

def tv1(~T: Data, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +i: U32, +x: T) -> AR.Tree<Maybe<&2, T>>:
  AR.upd(Maybe<&2, T>, depth, tv, U32.to_nat(i), Some{x})

def sfin(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> D.DList<T> & E.Obs<T>:
  D.obs_unit(~T, D.set_fin(~T, tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), i, x, r))

# the live / stale cases after the swap
def sstale(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, vals: Array<Maybe<&2, T>>) -> D.DList<T> & E.Obs<T>:
  (D.DL{tag, U32.from_nat(fresh), 0, SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), vals, AR.thaw(U32, tp), AR.thaw(U32, tn)}, E.OUnit{Fail{E.StaleHandle{}}})

def sst_m(~T: Data, +tag: U32, +fresh: Nat, +ord: List<&2, Nat>, +xs: List<&2, Maybe<&2, T>>) -> DS.Model<T> & E.Obs<T>:
  (DS.DM{tag, fresh, ST.items(T, xs, ord)}, E.OUnit{Fail{E.StaleHandle{}}})

def sdone(~T: Data, +tag: U32, +fresh: Nat, +its: List<&2, E.Item<T>>) -> DS.Model<T> & E.Obs<T>:
  (DS.DM{tag, fresh, its}, E.OUnit{Done{Unit{}}})

def set_none(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +em: {RD.xv(~T, tv, i) == None{} : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), None{})), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n):
  +xs = AR.slots(Maybe<&2, T>, tv)
  +n = U32.to_nat(i)
  +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)
  +hd32 = N.le_lt_trans(depth, 31n, 32n, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.lt_succ(31n))
  +pf1 = AR.upd_perfect(Maybe<&2, T>, depth, tv, n, Some{x}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +hlen = AR.len_lt(Maybe<&2, T>, depth, tv, n, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hn)
  +es1 = AR.upd_slots(Maybe<&2, T>, depth, tv, n, Some{x}, hn, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +egv = RD.getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)
  +t2 = AR.upd(Maybe<&2, T>, depth, tv1(~T, depth, tv, i, x), n, None{})
  +hx1 = Equal.trans(Maybe<&2, Maybe<&2, T>>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), n), SC.nth(Maybe<&2, T>, SC.update(Maybe<&2, T>, xs, n, Some{x}), n), Some{Some{x}},
    Equal.cong(List<&2, Maybe<&2, T>>, Maybe<&2, Maybe<&2, T>>, z => SC.nth(Maybe<&2, T>, z, n), AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), SC.update(Maybe<&2, T>, xs, n, Some{x}), es1),
    LL.nth_update_same(Maybe<&2, T>, xs, n, Some{x}, hlen))
  +eset = AR.set(Maybe<&2, T>, depth, tv1(~T, depth, tv, i, x), i, None{}, Some{x}, hd32, hn, hx1, pf1)
  +hnth = Equal.trans(Maybe<&2, Maybe<&2, T>>, SC.nth(Maybe<&2, T>, xs, n), Some{RD.xv(~T, tv, i)}, Some{None{}}, AS2.tsat(Maybe<&2, T>, depth, tv, n, None{}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hn), Equal.cong(Maybe<&2, T>, Maybe<&2, Maybe<&2, T>>, z => Some{z}, RD.xv(~T, tv, i), None{}, em))
  +es2 = Equal.trans(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), n, None{}), xs,
    AR.upd_slots(Maybe<&2, T>, depth, tv1(~T, depth, tv, i, x), n, None{}, hn, pf1),
    Equal.trans(List<&2, Maybe<&2, T>>, SC.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), n, None{}), SC.update(Maybe<&2, T>, SC.update(Maybe<&2, T>, xs, n, Some{x}), n, None{}), xs,
      Equal.cong(List<&2, Maybe<&2, T>>, List<&2, Maybe<&2, T>>, z => SC.update(Maybe<&2, T>, z, n, None{}), AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), SC.update(Maybe<&2, T>, xs, n, Some{x}), es1),
      Equal.trans(List<&2, Maybe<&2, T>>, SC.update(Maybe<&2, T>, SC.update(Maybe<&2, T>, xs, n, Some{x}), n, None{}), SC.update(Maybe<&2, T>, xs, n, None{}), xs, upd_upd(Maybe<&2, T>, xs, n, Some{x}, None{}), upd_self(Maybe<&2, T>, xs, n, None{}, hnth))))
  +g2 = F.good_mk(~T, tag, fresh, depth, t2, tp, tn, ord, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), AR.upd_perfect(Maybe<&2, T>, depth, tv1(~T, depth, tv, i, x), n, None{}, pf1), F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, h),
    L.subst(List<&2, Maybe<&2, T>>, z => {ST.lv(T, fresh, z, 0n, ord) == True{} : Bool}, xs, AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), xs, es2), F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h)), F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  K.gmk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), None{})), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n, ST.Sh{tag, fresh, depth, t2, tp, tn, ord}, E.OUnit{Fail{E.StaleHandle{}}},
    Equal.cong(Array<Maybe<&2, T>>, D.DList<T> & E.Obs<T>, z => sstale(~T, tag, fresh, depth, tv, tp, tn, ord, z), Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), i, None{}), AR.thaw(Maybe<&2, T>, t2), eset),
    g2,
    Equal.trans(DS.Model<T> & E.Obs<T>, (ST.model(~T, ST.Sh{tag, fresh, depth, t2, tp, tn, ord}), E.OUnit{Fail{E.StaleHandle{}}}), (ST.model(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), E.OUnit{Fail{E.StaleHandle{}}}), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}),
      Equal.cong(List<&2, Maybe<&2, T>>, DS.Model<T> & E.Obs<T>, z => sst_m(~T, tag, fresh, ord, z), AR.slots(Maybe<&2, T>, t2), xs, es2),
      Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => DS.set_at(T, DS.check(T, True{}, mm), tag, fresh, ST.items(T, xs, ord), i, x), None{}, DS.getv(T, ST.items(T, xs, ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), None{}, Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), RD.xv(~T, tv, i), None{}, egv, em)))),
    N.le_add_right(fresh, 0n))

def set_some(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, +v: T, +em: {RD.xv(~T, tv, i) == Some{v} : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), Some{v})), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n):
  +xs = AR.slots(Maybe<&2, T>, tv)
  +n = U32.to_nat(i)
  +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)
  +hd32 = N.le_lt_trans(depth, 31n, 32n, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.lt_succ(31n))
  +pf1 = AR.upd_perfect(Maybe<&2, T>, depth, tv, n, Some{x}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +hlen = AR.len_lt(Maybe<&2, T>, depth, tv, n, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hn)
  +es1 = AR.upd_slots(Maybe<&2, T>, depth, tv, n, Some{x}, hn, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +egv = RD.getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)
  +hm = NB.live_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi, v, em)
  +hs = Equal.trans(Bool, ST.is_some(T, Some{x}), ST.is_some(T, Some{v}), ST.is_some(T, ST.vat(T, xs, n)), {==}, Equal.cong(Maybe<&2, T>, Bool, z => ST.is_some(T, z), Some{v}, ST.vat(T, xs, n), Equal.sym(Maybe<&2, T>, ST.vat(T, xs, n), Some{v}, Equal.trans(Maybe<&2, T>, ST.vat(T, xs, n), RD.xv(~T, tv, i), Some{v}, RD.vat_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi), em))))
  +hlv = L.subst(List<&2, Maybe<&2, T>>, z => {ST.lv(T, fresh, z, 0n, ord) == True{} : Bool}, SC.update(Maybe<&2, T>, xs, n, Some{x}), AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), SC.update(Maybe<&2, T>, xs, n, Some{x}), es1),
    Equal.trans(Bool, ST.lv(T, fresh, SC.update(Maybe<&2, T>, xs, n, Some{x}), 0n, ord), ST.lv(T, fresh, xs, 0n, ord), True{}, lv_upd(T, fresh, xs, 0n, ord, n, Some{x}, hs, hlen), F.g_lv(~T, tag, fresh, depth, tv, tp, tn, ord, h)))
  +g2 = F.good_mk(~T, tag, fresh, depth, tv1(~T, depth, tv, i, x), tp, tn, ord, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), pf1, F.g_tp(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_tn(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, h), hlv, F.g_lk(~T, tag, fresh, depth, tv, tp, tn, ord, h))
  +eit = Equal.trans(List<&2, E.Item<T>>, ST.items(T, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), ord), ST.items(T, SC.update(Maybe<&2, T>, xs, n, Some{x}), ord), DS.setv(T, ST.items(T, xs, ord), i, x),
    Equal.cong(List<&2, Maybe<&2, T>>, List<&2, E.Item<T>>, z => ST.items(T, z, ord), AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), SC.update(Maybe<&2, T>, xs, n, Some{x}), es1),
    items_setv(T, xs, ord, i, x, depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), K.alllt_mono(ord, fresh, SC.pow2(depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), F.g_lt(~T, tag, fresh, depth, tv, tp, tn, ord, h)), F.g_nd(~T, tag, fresh, depth, tv, tp, tn, ord, h), AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, ord, h), hm, hlen))
  K.gmk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), Some{v})), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n, ST.Sh{tag, fresh, depth, tv1(~T, depth, tv, i, x), tp, tn, ord}, E.OUnit{Done{Unit{}}},
    {==}, g2,
    Equal.trans(DS.Model<T> & E.Obs<T>, (ST.model(~T, ST.Sh{tag, fresh, depth, tv1(~T, depth, tv, i, x), tp, tn, ord}), E.OUnit{Done{Unit{}}}), sdone(~T, tag, fresh, DS.setv(T, ST.items(T, xs, ord), i, x)), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}),
      Equal.cong(List<&2, E.Item<T>>, DS.Model<T> & E.Obs<T>, z => sdone(~T, tag, fresh, z), ST.items(T, AR.slots(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), ord), DS.setv(T, ST.items(T, xs, ord), i, x), eit),
      Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => DS.set_at(T, DS.check(T, True{}, mm), tag, fresh, ST.items(T, xs, ord), i, x), Some{v}, DS.getv(T, ST.items(T, xs, ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), Some{v}, Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, xs, ord), i), RD.xv(~T, tv, i), Some{v}, egv, em)))),
    N.le_add_right(fresh, 0n))

def set_m(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}, m: Maybe<&2, T>, +em: {RD.xv(~T, tv, i) == m : Maybe<&2, T>}) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), m)), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n):
  match m:
    case None{}:
      set_none(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, h, hi, em)
    case Some{v}:
      set_some(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, h, hi, v, em)

def set_core(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, ok: Bool, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == ok : Bool}, same: Bool) -> K.GCore(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, SRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, ok, same), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, same), 0n):
  match ok same:
    case True{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, SRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}, False{}), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, False{}), 0n, h, E.OUnit{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} False{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, SRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, False{}, False{}), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, False{}), 0n, h, E.OUnit{Fail{E.ForeignHandle{}}}, {==}, {==})
    case False{} True{}:
      K.gsame(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, SRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, False{}, True{}), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n, h, E.OUnit{Fail{E.StaleHandle{}}}, {==},
        Equal.cong(Maybe<&2, T>, DS.Model<T> & E.Obs<T>, mm => DS.set_at(T, DS.check(T, True{}, mm), tag, fresh, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i, x), None{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, RD.getv_ok_false(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok))))
    case True{} True{}:
      +hi = RD.hi_ok(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)
      +hn = RD.hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)
      +esw = AR.swap(Maybe<&2, T>, depth, tv, i, Some{x}, RD.xv(~T, tv, i), N.le_lt_trans(depth, 31n, 32n, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.lt_succ(31n)), hn, AS2.tsat(Maybe<&2, T>, depth, tv, U32.to_nat(i), None{}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hn), F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))
      K.gconv(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, SRT(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}, True{}), sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), RD.xv(~T, tv, i))), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), SSP(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, True{}), 0n,
        Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.DList<T> & E.Obs<T>, r => sfin(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, r), (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), RD.xv(~T, tv, i)), Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, Some{x}), Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i, Some{x}), (AR.thaw(Maybe<&2, T>, tv1(~T, depth, tv, i, x)), RD.xv(~T, tv, i)), esw)),
        {==},
        set_m(~T, tag, fresh, depth, tv, tp, tn, ord, i, x, h, hi, RD.xv(~T, tv, i), {==}))

def set_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +x: T, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Set{E.H{l, i}, x}):
  set_core(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))
