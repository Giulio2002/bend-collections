import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import ../../src/doubly_linked_list.bend as D
import ../dlist/state.bend as DST
import ../dlist/links.bend as LK
import ../dlist/split.bend as SP
import ../dlist/retarget.bend as RT
import ../dlist/facts.bend as DF
import ../dlist/items.bend as IT
import ../dlist/mut.bend as MU
import ../graph/shift.bend as SH
import ./state.bend as ST
import ./table.bend as TB
import ../../spec/lru_fast.bend as S

# List facts for the LRU shadow: the ghost orders, the free chain, and the
# folds of the invariant over appended orders and under frame updates.

# ---- Nat equality is symmetric ----

def eq_sym_c(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_eq(a, b) == c : Bool}) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match c:
    case True{}:
      +e = IT.eq_nat_true(a, b, ec)
      L.subst(Nat, z => {Nat.is_eq(a, z) == Nat.is_eq(z, a) : Bool}, a, b, e, {==})
    case False{}:
      Equal.trans(Bool, Nat.is_eq(a, b), False{}, Nat.is_eq(b, a), ec, Equal.sym(Bool, Nat.is_eq(b, a), False{}, SH.ne_flip(a, b, ec)))

def eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  eq_sym_c(a, b, Nat.is_eq(a, b), {==})

# ---- nodup under moving an element to the front ----

def or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def lmem_front(+i: Nat, +a: List<&2, Nat>, +s: Nat, +c: List<&2, Nat>) -> {DST.lmem(i, SC.append(Nat, a, Con{s, c})) == DST.lmem(i, Con{s, SC.append(Nat, a, c)}) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, i), DST.lmem(i, SC.append(Nat, t, Con{s, c}))), Bool.or(Nat.is_eq(x, i), Bool.or(Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c)))), Bool.or(Nat.is_eq(s, i), Bool.or(Nat.is_eq(x, i), DST.lmem(i, SC.append(Nat, t, c)))),
        Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, i), z), DST.lmem(i, SC.append(Nat, t, Con{s, c})), Bool.or(Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c))), lmem_front(i, t, s, c)),
        or_swap(Nat.is_eq(x, i), Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c))))

def and_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def not_or(a: Bool, +b: Bool) -> {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and4_swap(a: Bool, b: Bool, c: Bool, +d: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(Bool.and(a, c), Bool.and(b, d)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def nodup_front(+a: List<&2, Nat>, +s: Nat, +c: List<&2, Nat>) -> {DST.nodup(SC.append(Nat, a, Con{s, c})) == DST.nodup(Con{s, SC.append(Nat, a, c)}) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = SC.append(Nat, t, c)
      Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, SC.append(Nat, t, Con{s, c}))), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
        Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, SC.append(Nat, t, Con{s, c}))), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})),
          Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), DST.nodup(SC.append(Nat, t, Con{s, c}))), DST.lmem(x, SC.append(Nat, t, Con{s, c})), DST.lmem(x, Con{s, r}), lmem_front(x, t, s, c)),
          Equal.cong(Bool, Bool, z => Bool.and(Bool.not(DST.lmem(x, Con{s, r})), z), DST.nodup(SC.append(Nat, t, Con{s, c})), DST.nodup(Con{s, r}), nodup_front(t, s, c))),
        Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})), Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
          Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.not(DST.lmem(x, Con{s, r})), Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), not_or(Nat.is_eq(s, x), DST.lmem(x, r))),
          Equal.trans(Bool, Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
            and4_swap(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r)), Bool.not(DST.lmem(s, r)), DST.nodup(r)),
            Equal.trans(Bool, Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
              Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Bool.not(z), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Nat.is_eq(s, x), Nat.is_eq(x, s), eq_sym(s, x)),
              Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), Bool.not(DST.lmem(s, Con{x, r})), Equal.sym(Bool, Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), not_or(Nat.is_eq(x, s), DST.lmem(s, r))))))))

# ---- removing a slot from the order and pushing it on the free list ----

def nodup_rm(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +h: {DST.nodup(SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl)) == True{} : Bool}) -> {DST.nodup(SC.append(Nat, SC.append(Nat, a, b), Con{s, fl})) == True{} : Bool}:
  +h1 = L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl), SC.append(Nat, a, Con{s, SC.append(Nat, b, fl)}), LL.append_assoc(Nat, a, Con{s, b}, fl), h)
  +h2 = L.subst(Bool, z => {z == True{} : Bool}, DST.nodup(SC.append(Nat, a, Con{s, SC.append(Nat, b, fl)})), DST.nodup(Con{s, SC.append(Nat, a, SC.append(Nat, b, fl))}), nodup_front(a, s, SC.append(Nat, b, fl)), h1)
  +h3 = L.subst(List<&2, Nat>, z => {DST.nodup(Con{s, z}) == True{} : Bool}, SC.append(Nat, a, SC.append(Nat, b, fl)), SC.append(Nat, SC.append(Nat, a, b), fl), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, a, b), fl), SC.append(Nat, a, SC.append(Nat, b, fl)), LL.append_assoc(Nat, a, b, fl)), h2)
  L.subst(Bool, z => {z == True{} : Bool}, DST.nodup(Con{s, SC.append(Nat, SC.append(Nat, a, b), fl)}), DST.nodup(SC.append(Nat, SC.append(Nat, a, b), Con{s, fl})), Equal.sym(Bool, DST.nodup(SC.append(Nat, SC.append(Nat, a, b), Con{s, fl})), DST.nodup(Con{s, SC.append(Nat, SC.append(Nat, a, b), fl)}), nodup_front(SC.append(Nat, a, b), s, fl)), h3)

# the removed slot is not in what is left of the order
def notin_rm(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {DST.lmem(s, SC.append(Nat, a, b)) == False{} : Bool}:
  +h1 = L.subst(Bool, z => {z == True{} : Bool}, DST.nodup(SC.append(Nat, a, Con{s, b})), DST.nodup(Con{s, SC.append(Nat, a, b)}), nodup_front(a, s, b), h)
  TB.not_false(DST.lmem(s, SC.append(Nat, a, b)), L.and_left(Bool.not(DST.lmem(s, SC.append(Nat, a, b))), DST.nodup(SC.append(Nat, a, b)), h1))

def and_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_pick(+a: Bool, +b: Bool, +c: Bool, +h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {Bool.and(a, c) == True{} : Bool}:
  L.and_intro(a, c, L.and_left(a, Bool.and(b, c), h), L.and_right(b, c, L.and_right(a, Bool.and(b, c), h)))

# ---- the per-slot predicates over an appended order ----

def occ_app(-V: Data, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +c: List<&2, Nat>) -> {ST.all_occ(V, es, SC.append(Nat, a, c)) == Bool.and(ST.all_occ(V, es, a), ST.all_occ(V, es, c)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Bool, Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, es, SC.append(Nat, r, c))), Bool.and(ST.is_occ(V, ST.sat(V, es, x)), Bool.and(ST.all_occ(V, es, r), ST.all_occ(V, es, c))), Bool.and(Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, es, r)), ST.all_occ(V, es, c)),
        Equal.cong(Bool, Bool, z => Bool.and(ST.is_occ(V, ST.sat(V, es, x)), z), ST.all_occ(V, es, SC.append(Nat, r, c)), Bool.and(ST.all_occ(V, es, r), ST.all_occ(V, es, c)), occ_app(V, es, r, c)),
        and_assoc(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, es, r), ST.all_occ(V, es, c)))

def am_app(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +c: List<&2, Nat>) -> {ST.all_mapped(t, ks, SC.append(Nat, a, c)) == Bool.and(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, c)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Bool, Bool.and(ST.mapped(t, ST.kat(ks, x), x), ST.all_mapped(t, ks, SC.append(Nat, r, c))), Bool.and(ST.mapped(t, ST.kat(ks, x), x), Bool.and(ST.all_mapped(t, ks, r), ST.all_mapped(t, ks, c))), Bool.and(Bool.and(ST.mapped(t, ST.kat(ks, x), x), ST.all_mapped(t, ks, r)), ST.all_mapped(t, ks, c)),
        Equal.cong(Bool, Bool, z => Bool.and(ST.mapped(t, ST.kat(ks, x), x), z), ST.all_mapped(t, ks, SC.append(Nat, r, c)), Bool.and(ST.all_mapped(t, ks, r), ST.all_mapped(t, ks, c)), am_app(t, ks, r, c)),
        and_assoc(ST.mapped(t, ST.kat(ks, x), x), ST.all_mapped(t, ks, r), ST.all_mapped(t, ks, c)))

def occ_cut(-V: Data, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.all_occ(V, es, SC.append(Nat, a, b)) == True{} : Bool}:
  +h1 = L.subst(Bool, z => {z == True{} : Bool}, ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})), Bool.and(ST.all_occ(V, es, a), Bool.and(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, b))), occ_app(V, es, a, Con{s, b}), h)
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.all_occ(V, es, a), ST.all_occ(V, es, b)), ST.all_occ(V, es, SC.append(Nat, a, b)), Equal.sym(Bool, ST.all_occ(V, es, SC.append(Nat, a, b)), Bool.and(ST.all_occ(V, es, a), ST.all_occ(V, es, b)), occ_app(V, es, a, b)),
    and_pick(ST.all_occ(V, es, a), ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, b), h1))

def am_cut(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.all_mapped(t, ks, SC.append(Nat, a, b)) == True{} : Bool}:
  +h1 = L.subst(Bool, z => {z == True{} : Bool}, ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})), Bool.and(ST.all_mapped(t, ks, a), Bool.and(ST.mapped(t, ST.kat(ks, s), s), ST.all_mapped(t, ks, b))), am_app(t, ks, a, Con{s, b}), h)
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, b)), ST.all_mapped(t, ks, SC.append(Nat, a, b)), Equal.sym(Bool, ST.all_mapped(t, ks, SC.append(Nat, a, b)), Bool.and(ST.all_mapped(t, ks, a), ST.all_mapped(t, ks, b)), am_app(t, ks, a, b)),
    and_pick(ST.all_mapped(t, ks, a), ST.mapped(t, ST.kat(ks, s), s), ST.all_mapped(t, ks, b), h1))

# ---- frames: updating a slot outside the order changes nothing it reads ----

def fk_frame(+xs: List<&2, Nat>, +ns: List<&2, U32>, +j: Nat, +v: U32, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.fk(xs, SC.update(U32, ns, j, v)) == ST.fk(xs, ns) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(Bool, Bool.and(U32.is_eq(DST.lat(SC.update(U32, ns, j, v), x), DST.hd_or(t, D.nil())), ST.fk(t, SC.update(U32, ns, j, v))), Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, SC.update(U32, ns, j, v))), Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), ST.fk(t, ns)),
        Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(z, DST.hd_or(t, D.nil())), ST.fk(t, SC.update(U32, ns, j, v))), DST.lat(SC.update(U32, ns, j, v), x), DST.lat(ns, x), LK.lat_other(ns, j, v, x, SH.ne_flip(x, j, hx))),
        Equal.cong(Bool, Bool, z => Bool.and(U32.is_eq(DST.lat(ns, x), DST.hd_or(t, D.nil())), z), ST.fk(t, SC.update(U32, ns, j, v)), ST.fk(t, ns), fk_frame(t, ns, j, v, ht)))

def fk_frame_nupd(+xs: List<&2, Nat>, +ns: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +h: {SP.disj(a, xs) == True{} : Bool}) -> {ST.fk(xs, RT.nupd(ns, a, v)) == ST.fk(xs, ns) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      fk_frame(xs, ns, DST.lst_or(t, x), v, RT.last_notin(t, x, xs, h))

def sat_other(-V: Data, +es: List<&2, F.Slot<V>>, +j: Nat, +v: F.Slot<V>, +x: Nat, +ne: {Nat.is_eq(j, x) == False{} : Bool}) -> {ST.sat(V, SC.update(F.Slot<V>, es, j, v), x) == ST.sat(V, es, x) : F.Slot<V>}:
  Equal.cong(Maybe<&2, F.Slot<V>>, F.Slot<V>, m => ST.sat_m(V, m), SC.nth(F.Slot<V>, SC.update(F.Slot<V>, es, j, v), x), SC.nth(F.Slot<V>, es, x), LL.nth_update_other(F.Slot<V>, es, j, x, v, ne))

def kat_other(+ks: List<&2, String>, +j: Nat, +k: String, +x: Nat, +ne: {Nat.is_eq(j, x) == False{} : Bool}) -> {ST.kat(SC.update(String, ks, j, k), x) == ST.kat(ks, x) : String}:
  Equal.cong(Maybe<&2, String>, String, m => L.some_value(String, m, ""), SC.nth(String, SC.update(String, ks, j, k), x), SC.nth(String, ks, x), LL.nth_update_other(String, ks, j, x, k, ne))

def occ_frame(-V: Data, +es: List<&2, F.Slot<V>>, +j: Nat, +v: F.Slot<V>, +xs: List<&2, Nat>, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.all_occ(V, SC.update(F.Slot<V>, es, j, v), xs) == ST.all_occ(V, es, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(Bool, Bool.and(ST.is_occ(V, ST.sat(V, SC.update(F.Slot<V>, es, j, v), x)), ST.all_occ(V, SC.update(F.Slot<V>, es, j, v), t)), Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, SC.update(F.Slot<V>, es, j, v), t)), Bool.and(ST.is_occ(V, ST.sat(V, es, x)), ST.all_occ(V, es, t)),
        Equal.cong(F.Slot<V>, Bool, z => Bool.and(ST.is_occ(V, z), ST.all_occ(V, SC.update(F.Slot<V>, es, j, v), t)), ST.sat(V, SC.update(F.Slot<V>, es, j, v), x), ST.sat(V, es, x), sat_other(V, es, j, v, x, SH.ne_flip(x, j, hx))),
        Equal.cong(Bool, Bool, z => Bool.and(ST.is_occ(V, ST.sat(V, es, x)), z), ST.all_occ(V, SC.update(F.Slot<V>, es, j, v), t), ST.all_occ(V, es, t), occ_frame(V, es, j, v, t, ht)))

def ents_frame_e(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +j: Nat, +v: F.Slot<V>, +xs: List<&2, Nat>, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.ents(V, ks, SC.update(F.Slot<V>, es, j, v), xs) == ST.ents(V, ks, es, xs) : List<&2, S.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(ks, x), ST.sat(V, SC.update(F.Slot<V>, es, j, v), x), ST.ents(V, ks, SC.update(F.Slot<V>, es, j, v), t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), ST.ents(V, ks, SC.update(F.Slot<V>, es, j, v), t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), ST.ents(V, ks, es, t)),
        Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, x), z, ST.ents(V, ks, SC.update(F.Slot<V>, es, j, v), t)), ST.sat(V, SC.update(F.Slot<V>, es, j, v), x), ST.sat(V, es, x), sat_other(V, es, j, v, x, SH.ne_flip(x, j, hx))),
        Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), z), ST.ents(V, ks, SC.update(F.Slot<V>, es, j, v), t), ST.ents(V, ks, es, t), ents_frame_e(V, ks, es, j, v, t, ht)))

def ents_frame_k(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +j: Nat, +k: String, +xs: List<&2, Nat>, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.ents(V, SC.update(String, ks, j, k), es, xs) == ST.ents(V, ks, es, xs) : List<&2, S.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(SC.update(String, ks, j, k), x), ST.sat(V, es, x), ST.ents(V, SC.update(String, ks, j, k), es, t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), ST.ents(V, SC.update(String, ks, j, k), es, t)), ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), ST.ents(V, ks, es, t)),
        Equal.cong(String, List<&2, S.Ent<V>>, z => ST.ent_at(V, z, ST.sat(V, es, x), ST.ents(V, SC.update(String, ks, j, k), es, t)), ST.kat(SC.update(String, ks, j, k), x), ST.kat(ks, x), kat_other(ks, j, k, x, SH.ne_flip(x, j, hx))),
        Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, x), ST.sat(V, es, x), z), ST.ents(V, SC.update(String, ks, j, k), es, t), ST.ents(V, ks, es, t), ents_frame_k(V, ks, es, j, k, t, ht)))

def keys_frame(+ks: List<&2, String>, +j: Nat, +k: String, +xs: List<&2, Nat>, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.keys_at(SC.update(String, ks, j, k), xs) == ST.keys_at(ks, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(List<&2, String>, Con{ST.kat(SC.update(String, ks, j, k), x), ST.keys_at(SC.update(String, ks, j, k), t)}, Con{ST.kat(ks, x), ST.keys_at(SC.update(String, ks, j, k), t)}, Con{ST.kat(ks, x), ST.keys_at(ks, t)},
        Equal.cong(String, List<&2, String>, z => Con{z, ST.keys_at(SC.update(String, ks, j, k), t)}, ST.kat(SC.update(String, ks, j, k), x), ST.kat(ks, x), kat_other(ks, j, k, x, SH.ne_flip(x, j, hx))),
        Equal.cong(List<&2, String>, List<&2, String>, z => Con{ST.kat(ks, x), z}, ST.keys_at(SC.update(String, ks, j, k), t), ST.keys_at(ks, t), keys_frame(ks, j, k, t, ht)))

def am_frame_k(+tb: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +j: Nat, +k: String, +xs: List<&2, Nat>, +hj: {DST.lmem(j, xs) == False{} : Bool}) -> {ST.all_mapped(tb, SC.update(String, ks, j, k), xs) == ST.all_mapped(tb, ks, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = LK.or_false_l(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      +ht = LK.or_false_r(Nat.is_eq(x, j), DST.lmem(j, t), hj)
      Equal.trans(Bool, Bool.and(ST.mapped(tb, ST.kat(SC.update(String, ks, j, k), x), x), ST.all_mapped(tb, SC.update(String, ks, j, k), t)), Bool.and(ST.mapped(tb, ST.kat(ks, x), x), ST.all_mapped(tb, SC.update(String, ks, j, k), t)), Bool.and(ST.mapped(tb, ST.kat(ks, x), x), ST.all_mapped(tb, ks, t)),
        Equal.cong(String, Bool, z => Bool.and(ST.mapped(tb, z, x), ST.all_mapped(tb, SC.update(String, ks, j, k), t)), ST.kat(SC.update(String, ks, j, k), x), ST.kat(ks, x), kat_other(ks, j, k, x, SH.ne_flip(x, j, hx))),
        Equal.cong(Bool, Bool, z => Bool.and(ST.mapped(tb, ST.kat(ks, x), x), z), ST.all_mapped(tb, SC.update(String, ks, j, k), t), ST.all_mapped(tb, ks, t), am_frame_k(tb, ks, j, k, t, ht)))

# the slot is in neither part of the order around it
def notin_r_c(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {DST.lmem(s, b) == False{} : Bool}:
  LK.or_false_r(DST.lmem(s, a), DST.lmem(s, b), L.subst(Bool, z => {z == False{} : Bool}, DST.lmem(s, SC.append(Nat, a, b)), Bool.or(DST.lmem(s, a), DST.lmem(s, b)), SP.lmem_app(s, a, b), notin_rm(a, s, b, h)))
