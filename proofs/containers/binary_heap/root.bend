import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/binary_heap.bend as S
import ./idx.bend as IX
import ./slots.bend as SL
import ./vals.bend as V
import ./multiset.bend as M

# The root of a heap-ordered block is its minimum, and the block's multiset
# has as many elements as the block has occupied slots. These are the two
# facts the public operations need on top of the sift laws: `peek` and `pop`
# observe slot 0, and `length` observes the cached size.
#
# `low_all(ss, k, x)` is "x is not larger than any of the slots [0, k)". It is
# a Bool conjunction rather than a quantifier because a function-typed
# hypothesis is a linear Type in Bend and could not be used twice.

def low_all(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, n: Nat, +x: A) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(SL.mle(~A, ~cmp, Some{x}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, m, x))

# ---- the root is below every slot ----

def mle_mid(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +a: A, m: Maybe<&2, A>, b: Maybe<&2, A>, +y: A, +hm: {m == Some{y} : Maybe<&2, A>}, +h1: {SL.mle(~A, ~cmp, Some{a}, m) == True{} : Bool}, +h2: {SL.mle(~A, ~cmp, m, b) == True{} : Bool}) -> {SL.mle(~A, ~cmp, Some{a}, b) == True{} : Bool}:
  SL.mle_trans(~A, ~cmp, ~o, Some{a}, y, b,
    L.subst(Maybe<&2, A>, z => {SL.mle(~A, ~cmp, Some{a}, z) == True{} : Bool}, m, Some{y}, hm, h1),
    L.subst(Maybe<&2, A>, z => {SL.mle(~A, ~cmp, z, b) == True{} : Bool}, m, Some{y}, hm, h2))

def root_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +root: A, +c: Nat, b: Maybe<&2, A>, sig: Sigma<&1, &1, A, v => {SL.slot(~A, ss, IX.par(c)) == Some{v} : Maybe<&2, A>}>, +h1: {SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, ss, IX.par(c))) == True{} : Bool}, +h2: {SL.mle(~A, ~cmp, SL.slot(~A, ss, IX.par(c)), b) == True{} : Bool}) -> {SL.mle(~A, ~cmp, Some{root}, b) == True{} : Bool}:
  match sig:
    case Tuple{+y, hy}:
      mle_mid(~A, ~cmp, ~o, root, SL.slot(~A, ss, IX.par(c)), b, y, hy, h1, h2)

# Walking up the parent chain: the fuel is an upper bound on the index, and
# the parent of a positive index is strictly smaller.
def root_le(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, fuel: Nat, +root: A, j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +hjf: {Nat.is_le(j, fuel) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, ss, j)) == True{} : Bool}:
  match fuel j:
    case _ 0n:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, ss, 0n), Some{root}, h0) : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      O.le_refl(~A, ~cmp, ~o, root)
    case 0n 1n+p:
      Empty.absurd({SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, ss, 1n+p)) == True{} : Bool}, L.true_not_false(Nat.is_le(1n+p, 0n), hjf, {==}))
    case 1n+ +f 1n+ +p:
      +hpn = N.lt_trans(IX.par(1n+p), 1n+p, n, IX.par_lt(1n+p, {==}), hj)
      root_at(~A, ~cmp, ~o, ss, root, 1n+p, SL.slot(~A, ss, 1n+p),
        SL.slot_some(~A, SL.slot(~A, ss, IX.par(1n+p)), SL.lay_at(~A, ss, n, IX.par(1n+p), hlay, hpn)),
        root_le(~A, ~cmp, ~o, ss, n, f, root, IX.par(1n+p), hpn,
          N.lt_succ_le(IX.par(1n+p), f, N.lt_le_trans(IX.par(1n+p), 1n+p, 1n+f, IX.par_lt(1n+p, {==}), hjf)),
          hho, hlay, h0),
        SL.ho_at(~A, ~cmp, ss, n, 1n+p, hho, hj))

def low_all_mk(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, k: Nat, +root: A, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {low_all(~A, ~cmp, ss, k, root) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, m, root),
        root_le(~A, ~cmp, ~o, ss, n, m, root, m, N.succ_le_lt(m, n, hk), N.le_refl(m), hho, hlay, h0),
        low_all_mk(~A, ~cmp, ~o, ss, n, m, root, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hho, hlay, h0))

# ---- from slots to the multiset ----

def all_ge_cons(~A: Data, ~cmp: A -> A -> Cmp, +z: A, m: Maybe<&2, A>, +xs: List<&2, A>, +hm: {SL.mle(~A, ~cmp, Some{z}, m) == True{} : Bool}, +ih: {S.all_ge(~A, ~cmp, z, xs) == True{} : Bool}) -> {S.all_ge(~A, ~cmp, z, V.cons_slot(~A, m, xs)) == True{} : Bool}:
  match m:
    case None{}:
      ih
    case Some{+v}:
      L.and_intro(S.le(~A, ~cmp, z, v), S.all_ge(~A, ~cmp, z, xs), hm, ih)

def all_ge_vals(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, n: Nat, +z: A, +h: {low_all(~A, ~cmp, ss, n, z) == True{} : Bool}) -> {S.all_ge(~A, ~cmp, z, V.vals(~A, ss, n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      all_ge_cons(~A, ~cmp, z, SL.slot(~A, ss, m), V.vals(~A, ss, m),
        L.and_left(SL.mle(~A, ~cmp, Some{z}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, m, z), h),
        all_ge_vals(~A, ~cmp, ss, m, z, L.and_right(SL.mle(~A, ~cmp, Some{z}, SL.slot(~A, ss, m)), low_all(~A, ~cmp, ss, m, z), h)))

def all_ge_msort(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, xs: List<&2, A>, +h: {S.all_ge(~A, ~cmp, z, xs) == True{} : Bool}) -> {S.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, S.all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, t))), Bool.and(S.le(~A, ~cmp, z, x), S.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, t))), M.all_ge_ins(~A, ~cmp, ~o, z, x, V.msort(~A, ~cmp, t))) : {_ == True{} : Bool}
      L.and_intro(S.le(~A, ~cmp, z, x), S.all_ge(~A, ~cmp, z, V.msort(~A, ~cmp, t)),
        L.and_left(S.le(~A, ~cmp, z, x), S.all_ge(~A, ~cmp, z, t), h),
        all_ge_msort(~A, ~cmp, ~o, z, t, L.and_right(S.le(~A, ~cmp, z, x), S.all_ge(~A, ~cmp, z, t), h)))

# x is not larger than any slot of [0, k) => it comes first in the multiset.
def front(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +k: Nat, +z: A, +h: {low_all(~A, ~cmp, ss, k, z) == True{} : Bool}) -> {S.ins(~A, ~cmp, z, V.msort(~A, ~cmp, V.vals(~A, ss, k))) == Con{z, V.msort(~A, ~cmp, V.vals(~A, ss, k))} : List<&2, A>}:
  M.ins_min(~A, ~cmp, ~o, z, V.msort(~A, ~cmp, V.vals(~A, ss, k)),
    all_ge_msort(~A, ~cmp, ~o, z, V.vals(~A, ss, k), all_ge_vals(~A, ~cmp, ss, k, z, h)))

# ---- the multiset has one element per occupied slot ----

def length_ins_c(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +h: A, +t: List<&2, A>, +b: Bool, +e: {S.le(~A, ~cmp, x, h) == b : Bool}, +ih: {SC.length(A, S.ins(~A, ~cmp, x, t)) == 1n+SC.length(A, t) : Nat}) -> {SC.length(A, S.ins(~A, ~cmp, x, Con{h, t})) == 2n+SC.length(A, t) : Nat}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{x, Con{h, t}}, M.ins_cons(~A, ~cmp, x, h, t, True{}, e)) : {SC.length(A, _) == 2n+SC.length(A, t) : Nat}
      {==}
    case False{}:
      %Equal.sym(List<&2, A>, S.ins(~A, ~cmp, x, Con{h, t}), Con{h, S.ins(~A, ~cmp, x, t)}, M.ins_cons(~A, ~cmp, x, h, t, False{}, e)) : {SC.length(A, _) == 2n+SC.length(A, t) : Nat}
      N.succ_cong(SC.length(A, S.ins(~A, ~cmp, x, t)), 1n+SC.length(A, t), ih)

def length_ins(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +xs: List<&2, A>) -> {SC.length(A, S.ins(~A, ~cmp, x, xs)) == 1n+SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      length_ins_c(~A, ~cmp, x, h, t, S.le(~A, ~cmp, x, h), {==}, length_ins(~A, ~cmp, x, t))

def msort_length(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> {SC.length(A, V.msort(~A, ~cmp, xs)) == SC.length(A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, SC.length(A, S.ins(~A, ~cmp, x, V.msort(~A, ~cmp, t))), 1n+SC.length(A, V.msort(~A, ~cmp, t)), 1n+SC.length(A, t),
        length_ins(~A, ~cmp, x, V.msort(~A, ~cmp, t)),
        N.succ_cong(SC.length(A, V.msort(~A, ~cmp, t)), SC.length(A, t), msort_length(~A, ~cmp, t)))

def vals_length_c(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, s: Maybe<&2, A>, +es: {SL.slot(~A, ss, m) == s : Maybe<&2, A>}, +hs: {Maybe.is_some(&2, A, SL.slot(~A, ss, m)) == True{} : Bool}, +ih: {SC.length(A, V.vals(~A, ss, m)) == m : Nat}) -> {SC.length(A, V.vals(~A, ss, 1n+m)) == 1n+m : Nat}:
  match s:
    case None{}:
      Empty.absurd({SC.length(A, V.vals(~A, ss, 1n+m)) == 1n+m : Nat}, L.false_true(L.subst(Maybe<&2, A>, z => {Maybe.is_some(&2, A, z) == True{} : Bool}, SL.slot(~A, ss, m), None{}, es, hs)))
    case Some{+v}:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, ss, m), Some{v}, es) : {SC.length(A, V.cons_slot(~A, _, V.vals(~A, ss, m))) == 1n+m : Nat}
      N.succ_cong(SC.length(A, V.vals(~A, ss, m)), m, ih)

def vals_length(~A: Data, +ss: List<&2, Maybe<&2, A>>, n: Nat, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}) -> {SC.length(A, V.vals(~A, ss, n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      vals_length_c(~A, ss, m, SL.slot(~A, ss, m), {==},
        L.and_left(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), hlay),
        vals_length(~A, ss, m, L.and_right(Maybe.is_some(&2, A, SL.slot(~A, ss, m)), SL.lay(~A, ss, m), hlay)))

def model_length(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}) -> {SC.length(A, V.msort(~A, ~cmp, V.vals(~A, ss, n))) == n : Nat}:
  Equal.trans(Nat, SC.length(A, V.msort(~A, ~cmp, V.vals(~A, ss, n))), SC.length(A, V.vals(~A, ss, n)), n,
    msort_length(~A, ~cmp, V.vals(~A, ss, n)),
    vals_length(~A, ss, n, hlay))

# ---- taking one element out of the multiset ----
#
# The mirror of vals.ins_set: emptying slot i removes exactly its value from
# the sorted multiset. This is what makes the root observable: it is the
# element the sorted multiset starts with.

def ins_del_cons(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), s: Maybe<&2, A>, +old: A, +xs: List<&2, A>, +ys: List<&2, A>, +ih: {V.msort(~A, ~cmp, xs) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, ys)) : List<&2, A>}) -> {V.msort(~A, ~cmp, V.cons_slot(~A, s, xs)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.cons_slot(~A, s, ys))) : List<&2, A>}:
  match s:
    case None{}:
      ih
    case Some{+w}:
      Equal.trans(List<&2, A>, S.ins(~A, ~cmp, w, V.msort(~A, ~cmp, xs)), S.ins(~A, ~cmp, w, S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, ys))), S.ins(~A, ~cmp, old, S.ins(~A, ~cmp, w, V.msort(~A, ~cmp, ys))),
        Equal.cong(List<&2, A>, List<&2, A>, zs => S.ins(~A, ~cmp, w, zs), V.msort(~A, ~cmp, xs), S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, ys)), ih),
        M.ins_comm(~A, ~cmp, ~o, w, old, V.msort(~A, ~cmp, ys)))

def ins_del_top(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +old: A, +ei: {i == m : Nat}, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 1n+m))) : List<&2, A>}:
  %ei : {V.msort(~A, ~cmp, V.vals(~A, ss, 1n+_)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 1n+_))) : List<&2, A>}
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.cons_slot(~A, SL.slot(~A, ss, i), V.vals(~A, ss, i))), S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, ss, i))), S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 1n+i))),
    Equal.cong(Maybe<&2, A>, List<&2, A>, ms => V.msort(~A, ~cmp, V.cons_slot(~A, ms, V.vals(~A, ss, i))), SL.slot(~A, ss, i), Some{old}, hold),
    Equal.cong(List<&2, A>, List<&2, A>, zs => S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, zs)), V.vals(~A, ss, i), V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 1n+i),
      Equal.trans(List<&2, A>, V.vals(~A, ss, i), V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), i), V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 1n+i),
        Equal.sym(List<&2, A>, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), i), V.vals(~A, ss, i), V.vals_above(~A, ss, i, None{}, i, N.le_refl(i))),
        Equal.cong(Maybe<&2, A>, List<&2, A>, ms => V.cons_slot(~A, ms, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), i)), None{}, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, None{}), i),
          Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, None{}), i), None{}, SL.slot_same(~A, ss, i, None{}, V.slot_in_range(~A, ss, i, old, hold)))))))

def ins_del(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, n: Nat, +i: Nat, +old: A, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hold: {SL.slot(~A, ss, i) == Some{old} : Maybe<&2, A>}, b: Bool, +eb: {Nat.is_eq(i, N.pred(n)) == b : Bool}) -> {V.msort(~A, ~cmp, V.vals(~A, ss, n)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), n))) : List<&2, A>}:
  match n b:
    case 0n _:
      Empty.absurd({V.msort(~A, ~cmp, V.vals(~A, ss, 0n)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), 0n))) : List<&2, A>}, N.lt_zero_absurd(i, hi))
    case 1n+m True{}:
      ins_del_top(~A, ~cmp, ss, m, i, old, N.eq_from_is_eq(i, m, eb), hold)
    case 1n+ +m False{}:
      +hi2 = N.lt_or_eq(i, m, N.lt_succ_le(i, m, hi), eb)
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, i, None{}), m), SL.slot(~A, ss, m), SL.slot_other(~A, ss, i, m, None{}, N.is_eq_lt(i, m, hi2))) : {V.msort(~A, ~cmp, V.vals(~A, ss, 1n+m)) == S.ins(~A, ~cmp, old, V.msort(~A, ~cmp, V.cons_slot(~A, _, V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), m)))) : List<&2, A>}
      ins_del_cons(~A, ~cmp, ~o, SL.slot(~A, ss, m), old, V.vals(~A, ss, m), V.vals(~A, SC.update(Maybe<&2, A>, ss, i, None{}), m),
        ins_del(~A, ~cmp, ~o, ss, m, i, old, hi2, hold, Nat.is_eq(i, N.pred(m)), {==}))

# ---- the sorted multiset of a heap-ordered block starts with its root ----

def low_del_at(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, j: Nat, +root: A, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), j)) == True{} : Bool}:
  match j:
    case 0n:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), 0n), None{}, SL.slot_same(~A, ss, 0n, None{}, V.slot_in_range(~A, ss, 0n, root, h0))) : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      SL.mle_none_r(~A, ~cmp, Some{root})
    case 1n+ +p:
      %Equal.sym(Maybe<&2, A>, SL.slot(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), 1n+p), SL.slot(~A, ss, 1n+p), SL.slot_other(~A, ss, 0n, 1n+p, None{}, {==})) : {SL.mle(~A, ~cmp, Some{root}, _) == True{} : Bool}
      root_le(~A, ~cmp, ~o, ss, n, 1n+p, root, 1n+p, hjn, N.le_refl(1n+p), hho, hlay, h0)

def low_del(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, k: Nat, +root: A, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {low_all(~A, ~cmp, SC.update(Maybe<&2, A>, ss, 0n, None{}), k, root) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(SL.mle(~A, ~cmp, Some{root}, SL.slot(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), m)), low_all(~A, ~cmp, SC.update(Maybe<&2, A>, ss, 0n, None{}), m, root),
        low_del_at(~A, ~cmp, ~o, ss, n, m, root, N.succ_le_lt(m, n, hk), hho, hlay, h0),
        low_del(~A, ~cmp, ~o, ss, n, m, root, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), hho, hlay, h0))

def head_root(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ss: List<&2, Maybe<&2, A>>, +n: Nat, +root: A, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, ss, n) == True{} : Bool}, +hlay: {SL.lay(~A, ss, n) == True{} : Bool}, +h0: {SL.slot(~A, ss, 0n) == Some{root} : Maybe<&2, A>}) -> {V.msort(~A, ~cmp, V.vals(~A, ss, n)) == Con{root, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), n))} : List<&2, A>}:
  Equal.trans(List<&2, A>, V.msort(~A, ~cmp, V.vals(~A, ss, n)), S.ins(~A, ~cmp, root, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), n))), Con{root, V.msort(~A, ~cmp, V.vals(~A, SC.update(Maybe<&2, A>, ss, 0n, None{}), n))},
    ins_del(~A, ~cmp, ~o, ss, n, 0n, root, hn, h0, Nat.is_eq(0n, N.pred(n)), {==}),
    front(~A, ~cmp, ~o, SC.update(Maybe<&2, A>, ss, 0n, None{}), n, root, low_del(~A, ~cmp, ~o, ss, n, n, root, N.le_refl(n), hho, hlay, h0)))
