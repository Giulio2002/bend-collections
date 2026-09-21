import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import ../dlist/state.bend as DST
import ../dlist/items.bend as IT
import ../dlist/facts.bend as DF
import ../../reference/lru/src/cache.bend as C
import ../../reference/lru/proofs/invariants.bend as Inv
import ../../reference/lru/proofs/native_map.bend as Native
import ../../reference/lru/proofs/map_insert.bend as MI
import ../../reference/lru/proofs/map_populated.bend as Pop
import ../../reference/lru/proofs/map_routing.bend as R
import ../../reference/lru/proofs/map_set_frame.bend as SetFrame
import ../../reference/lru/proofs/map_set_critbit.bend as SetCrit
import ../../reference/lru/proofs/map_set_membership.bend as SetMem
import ../../reference/lru/proofs/map_delete_frame.bend as DelFrame
import ../../reference/lru/proofs/map_delete_critbit.bend as DelCrit
import ../../reference/lru/proofs/map_delete_populated.bend as DelPop
import ../../reference/lru/proofs/map_delete_membership.bend as DelMem
import ../../reference/lru/proofs/map_delete.bend as MDel
import ../../reference/lru/proofs/map_key_presence.bend as Presence
import ../../reference/lru/proofs/map_key_membership.bend as KeyMem
import ../../reference/lru/proofs/cache_delete_membership.bend as CDM
import ../../reference/lru/proofs/recency_unique.bend as RU
import ../../reference/lru/proofs/recency_membership.bend as RM
import ../../reference/lru/proofs/canonical_string.bend as CS
import ../../reference/lru/proofs/lookup_refinement.bend as LR
import ../dlist/split.bend as SP
import ../dlist/links.bend as LK
import ../graph/shift.bend as SH
import ../dlist/nbrs.bend as NB
import ./state.bend as ST

# The key table of the indexed LRU: a native Map<&2, Maybe<U32>> from key to
# slot, always holding Some. Everything here reuses the retained crit-bit Map
# theory of reference/lru (lookup after set/delete, critbit and populated
# preservation, key membership); nothing re-proves the Map.

def lk(+t: Map<&2, Maybe<&2, U32>>, +q: String) -> Maybe<&2, U32>:
  MI.lookup(Maybe<&2, U32>, None{}, t, q)

def mpair(+t: Map<&2, Maybe<&2, U32>>, +m: Maybe<&2, U32>) -> Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>:
  (t, m)

def get_eta(p: Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>) -> {p == mpair(Native.lookup_map(Maybe<&2, U32>, p), MI.value(Maybe<&2, U32>, p)) : Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>}:
  match p:
    case Tuple{m, v}:
      {==}

# The runtime's Map.get returns the unchanged table and the lookup.
def get_pair(+t: Map<&2, Maybe<&2, U32>>, +q: String) -> {Map.get(Maybe<&2, U32>, None{}, t, q) == mpair(t, lk(t, q)) : Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>}:
  Equal.trans(Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, t, q), mpair(Native.lookup_map(Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, t, q)), lk(t, q)), mpair(t, lk(t, q)),
    get_eta(Map.get(Maybe<&2, U32>, None{}, t, q)),
    Equal.cong(Map<&2, Maybe<&2, U32>>, Map<&2, Maybe<&2, U32>> & Maybe<&2, U32>, z => mpair(z, lk(t, q)), Native.lookup_map(Maybe<&2, U32>, Map.get(Maybe<&2, U32>, None{}, t, q)), t, Native.lookup_preserves_map(Maybe<&2, U32>, None{}, t, q)))

def different_of(+a: String, +b: String, +h: {String.eq(a, b) == False{} : Bool}) -> DelFrame.different(a, b):
  e => DelMem.distinct(a, b, h, e)

# ---- keys of the live slots ----

def kmem_app(+ks: List<&2, String>, +a: List<&2, Nat>, +c: List<&2, Nat>, +q: String) -> {Inv.member(ST.keys_at(ks, SC.append(Nat, a, c)), q) == Bool.or(Inv.member(ST.keys_at(ks, a), q), Inv.member(ST.keys_at(ks, c), q)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(Bool, Bool.or(String.eq(ST.kat(ks, s), q), Inv.member(ST.keys_at(ks, SC.append(Nat, t, c)), q)), Bool.or(String.eq(ST.kat(ks, s), q), Bool.or(Inv.member(ST.keys_at(ks, t), q), Inv.member(ST.keys_at(ks, c), q))), Bool.or(Bool.or(String.eq(ST.kat(ks, s), q), Inv.member(ST.keys_at(ks, t), q)), Inv.member(ST.keys_at(ks, c), q)),
        Equal.cong(Bool, Bool, z => Bool.or(String.eq(ST.kat(ks, s), q), z), Inv.member(ST.keys_at(ks, SC.append(Nat, t, c)), q), Bool.or(Inv.member(ST.keys_at(ks, t), q), Inv.member(ST.keys_at(ks, c), q)), kmem_app(ks, t, c, q)),
        SP.or_assoc(String.eq(ST.kat(ks, s), q), Inv.member(ST.keys_at(ks, t), q), Inv.member(ST.keys_at(ks, c), q)))

# a key other than slot s's that is a key of a ++ [s] ++ b is a key of a ++ b
def kmem_cut(+ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +q: String, +hne: {String.eq(ST.kat(ks, s), q) == False{} : Bool}, +h: {Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q) == True{} : Bool}) -> {Inv.member(ST.keys_at(ks, SC.append(Nat, a, b)), q) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Bool.or(Inv.member(ST.keys_at(ks, a), q), Bool.or(String.eq(ST.kat(ks, s), q), Inv.member(ST.keys_at(ks, b), q))), Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q), True{}, Equal.sym(Bool, Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q), Bool.or(Inv.member(ST.keys_at(ks, a), q), Bool.or(String.eq(ST.kat(ks, s), q), Inv.member(ST.keys_at(ks, b), q))), kmem_app(ks, a, Con{s, b}, q)), h)
  +h2 = L.subst(Bool, z => {Bool.or(Inv.member(ST.keys_at(ks, a), q), Bool.or(z, Inv.member(ST.keys_at(ks, b), q))) == True{} : Bool}, String.eq(ST.kat(ks, s), q), False{}, hne, h1)
  Equal.trans(Bool, Inv.member(ST.keys_at(ks, SC.append(Nat, a, b)), q), Bool.or(Inv.member(ST.keys_at(ks, a), q), Inv.member(ST.keys_at(ks, b), q)), True{}, kmem_app(ks, a, b, q), h2)

# the keys of ord ++ [s] are those of ord and the key of s
def kmem_snoc(+ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +q: String) -> {Inv.member(ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}})), q) == Bool.or(Inv.member(ST.keys_at(ks, ord), q), Bool.or(String.eq(ST.kat(ks, s), q), False{})) : Bool}:
  kmem_app(ks, ord, Con{s, Nil{}}, q)

# ---- no live key equals q ----

def none_key(+ks: List<&2, String>, xs: List<&2, Nat>, +q: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+s, t}:
      Bool.and(Bool.not(String.eq(ST.kat(ks, s), q)), none_key(ks, t, q))

# no slot of xs is the one m names
def nomap(+m: Maybe<&2, U32>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+s, t}:
      Bool.and(Bool.not(ST.mapped_m(m, s)), nomap(m, t))

def not_false(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

def not_of_false(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, b, Equal.sym(Bool, b, False{}, h), {==})

def nk_elem_c(+t: Map<&2, Maybe<&2, U32>>, +k: String, +s: Nat, +q: String, +m: Maybe<&2, U32>, +hm: {lk(t, q) == m : Maybe<&2, U32>}, +hmap: {ST.mapped(t, k, s) == True{} : Bool}, +hno: {ST.mapped_m(m, s) == False{} : Bool}, c: Bool, +ec: {String.eq(k, q) == c : Bool}) -> {String.eq(k, q) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      +ek = RU.equal_boolean(k, q, ec)
      +e1 = Equal.trans(Maybe<&2, U32>, lk(t, k), lk(t, q), m, Equal.cong(String, Maybe<&2, U32>, z => lk(t, z), k, q, ek), hm)
      +e2 = L.subst(Maybe<&2, U32>, z => {ST.mapped_m(z, s) == True{} : Bool}, lk(t, k), m, e1, hmap)
      Empty.absurd({String.eq(k, q) == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, ST.mapped_m(m, s), True{}, Equal.sym(Bool, ST.mapped_m(m, s), False{}, hno), e2)))

def nk_elem(+t: Map<&2, Maybe<&2, U32>>, +k: String, +s: Nat, +q: String, +m: Maybe<&2, U32>, +hm: {lk(t, q) == m : Maybe<&2, U32>}, +hmap: {ST.mapped(t, k, s) == True{} : Bool}, +hno: {ST.mapped_m(m, s) == False{} : Bool}) -> {String.eq(k, q) == False{} : Bool}:
  nk_elem_c(t, k, s, q, m, hm, hmap, hno, String.eq(k, q), {==})

def nk_all(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +xs: List<&2, Nat>, +q: String, +m: Maybe<&2, U32>, +hm: {lk(t, q) == m : Maybe<&2, U32>}, +hmap: {ST.all_mapped(t, ks, xs) == True{} : Bool}, +hno: {nomap(m, xs) == True{} : Bool}) -> {none_key(ks, xs, q) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      L.and_intro(Bool.not(String.eq(ST.kat(ks, s), q)), none_key(ks, r, q),
        not_of_false(String.eq(ST.kat(ks, s), q), nk_elem(t, ST.kat(ks, s), s, q, m, hm, L.and_left(ST.mapped(t, ST.kat(ks, s), s), ST.all_mapped(t, ks, r), hmap), not_false(ST.mapped_m(m, s), L.and_left(Bool.not(ST.mapped_m(m, s)), nomap(m, r), hno)))),
        nk_all(t, ks, r, q, m, hm, L.and_right(ST.mapped(t, ST.kat(ks, s), s), ST.all_mapped(t, ks, r), hmap), L.and_right(Bool.not(ST.mapped_m(m, s)), nomap(m, r), hno)))

def nomap_none(+xs: List<&2, Nat>) -> {nomap(None{}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      nomap_none(r)

def nomap_some(+s0: Nat, +xs: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +h0: {Nat.is_lt(s0, SC.pow2(depth)) == True{} : Bool}, +hl: {DST.alllt(xs, SC.pow2(depth)) == True{} : Bool}, +hn: {DST.lmem(s0, xs) == False{} : Bool}) -> {nomap(Some{U32.from_nat(s0)}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      +hs = IT.lt_head(s, r, SC.pow2(depth), hl)
      +e = Equal.trans(Bool, U32.is_eq(U32.from_nat(s0), U32.from_nat(s)), Nat.is_eq(s0, U32.to_nat(U32.from_nat(s))), Nat.is_eq(s0, s), IT.ueq(s0, U32.from_nat(s), depth, hd, h0), Equal.cong(Nat, Bool, z => Nat.is_eq(s0, z), U32.to_nat(U32.from_nat(s)), s, DF.id_nat(s, depth, hd, hs)))
      +ne = SH.ne_flip(s, s0, LK.or_false_l(Nat.is_eq(s, s0), DST.lmem(s0, r), hn))
      L.and_intro(Bool.not(U32.is_eq(U32.from_nat(s0), U32.from_nat(s))), nomap(Some{U32.from_nat(s0)}, r),
        not_of_false(U32.is_eq(U32.from_nat(s0), U32.from_nat(s)), Equal.trans(Bool, U32.is_eq(U32.from_nat(s0), U32.from_nat(s)), Nat.is_eq(s0, s), False{}, e, ne)),
        nomap_some(s0, r, depth, hd, h0, IT.lt_tail(s, r, SC.pow2(depth), hl), LK.or_false_r(Nat.is_eq(s, s0), DST.lmem(s0, r), hn)))

# ---- locating the slot of a present key ----

def or_true_l(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, b) == True{} : Bool}, True{}, a, Equal.sym(Bool, a, True{}, h), {==})

def or_true_r(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def pick_nat(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# the first live slot whose key is q
def firstk(+ks: List<&2, String>, ord: List<&2, Nat>, +q: String) -> Nat:
  match ord:
    case Nil{}:
      0n
    case Con{+s, t}:
      pick_nat(String.eq(ST.kat(ks, s), q), s, firstk(ks, t, q))

def FkIH(+ks: List<&2, String>, +t: List<&2, Nat>, +q: String) -> Type:
  @hm: {Inv.member(ST.keys_at(ks, t), q) == True{} : Bool} -> {Bool.and(DST.lmem(firstk(ks, t, q), t), String.eq(ST.kat(ks, firstk(ks, t, q)), q)) == True{} : Bool}

def fk_c(+ks: List<&2, String>, +s: Nat, +t: List<&2, Nat>, +q: String, c: Bool, +ec: {String.eq(ST.kat(ks, s), q) == c : Bool}, +h: {Bool.or(c, Inv.member(ST.keys_at(ks, t), q)) == True{} : Bool}, ih: FkIH(ks, t, q)) -> {Bool.and(DST.lmem(pick_nat(c, s, firstk(ks, t, q)), Con{s, t}), String.eq(ST.kat(ks, pick_nat(c, s, firstk(ks, t, q))), q)) == True{} : Bool}:
  match c:
    case True{}:
      L.and_intro(Bool.or(Nat.is_eq(s, s), DST.lmem(s, t)), String.eq(ST.kat(ks, s), q), or_true_l(Nat.is_eq(s, s), DST.lmem(s, t), N.is_eq_refl(s)), ec)
    case False{}:
      +r = ih(h)
      L.and_intro(Bool.or(Nat.is_eq(s, firstk(ks, t, q)), DST.lmem(firstk(ks, t, q), t)), String.eq(ST.kat(ks, firstk(ks, t, q)), q),
        or_true_r(Nat.is_eq(s, firstk(ks, t, q)), DST.lmem(firstk(ks, t, q), t), L.and_left(DST.lmem(firstk(ks, t, q), t), String.eq(ST.kat(ks, firstk(ks, t, q)), q), r)),
        L.and_right(DST.lmem(firstk(ks, t, q), t), String.eq(ST.kat(ks, firstk(ks, t, q)), q), r))

def fk_ok(+ks: List<&2, String>, +ord: List<&2, Nat>, +q: String, +h: {Inv.member(ST.keys_at(ks, ord), q) == True{} : Bool}) -> {Bool.and(DST.lmem(firstk(ks, ord, q), ord), String.eq(ST.kat(ks, firstk(ks, ord, q)), q)) == True{} : Bool}:
  match ord:
    case Nil{}:
      Empty.absurd({Bool.and(DST.lmem(0n, Nil{}), String.eq(ST.kat(ks, 0n), q)) == True{} : Bool}, L.false_true(h))
    case Con{+s, +t}:
      fk_c(ks, s, t, q, String.eq(ST.kat(ks, s), q), {==}, h, hm => fk_ok(ks, t, q, hm))

def AmIH(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +r: List<&2, Nat>, +s: Nat) -> Type:
  @hm: {ST.all_mapped(t, ks, r) == True{} : Bool} -> @hl: {DST.lmem(s, r) == True{} : Bool} -> {ST.mapped(t, ST.kat(ks, s), s) == True{} : Bool}

def am_c(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +x: Nat, +r: List<&2, Nat>, +s: Nat, +hm: {ST.all_mapped(t, ks, Con{x, r}) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(x, s) == c : Bool}, +hl: {Bool.or(c, DST.lmem(s, r)) == True{} : Bool}, ih: AmIH(t, ks, r, s)) -> {ST.mapped(t, ST.kat(ks, s), s) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {ST.mapped(t, ST.kat(ks, z), z) == True{} : Bool}, x, s, IT.eq_nat_true(x, s, ec), L.and_left(ST.mapped(t, ST.kat(ks, x), x), ST.all_mapped(t, ks, r), hm))
    case False{}:
      ih(L.and_right(ST.mapped(t, ST.kat(ks, x), x), ST.all_mapped(t, ks, r), hm), hl)

# a live slot's key is mapped to it
def am_at(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +hm: {ST.all_mapped(t, ks, ord) == True{} : Bool}, +hl: {DST.lmem(s, ord) == True{} : Bool}) -> {ST.mapped(t, ST.kat(ks, s), s) == True{} : Bool}:
  match ord:
    case Nil{}:
      Empty.absurd({ST.mapped(t, ST.kat(ks, s), s) == True{} : Bool}, L.false_true(hl))
    case Con{+x, +r}:
      am_c(t, ks, x, r, s, hm, Nat.is_eq(x, s), {==}, hl, hm2 => hl2 => am_at(t, ks, r, s, hm2, hl2))

def some_mapped(+x: U32, +s: Nat, +h: {ST.mapped_m(Some{x}, s) == True{} : Bool}) -> {x == U32.from_nat(s) : U32}:
  NB.ueq_true(x, U32.from_nat(s), h)

# A present key's slot is the first live slot with that key.
def locate(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +ord: List<&2, Nat>, +q: String, +x: U32, +hx: {lk(t, q) == Some{x} : Maybe<&2, U32>}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}, +hmap: {ST.all_mapped(t, ks, ord) == True{} : Bool}) -> {x == U32.from_nat(firstk(ks, ord, q)) : U32}:
  +s1 = firstk(ks, ord, q)
  +hmem = Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, U32>, t), q), Maybe.is_some(&2, U32, lk(t, q)), True{}, Equal.sym(Bool, Maybe.is_some(&2, U32, lk(t, q)), Inv.member(Map.keys(&2, Maybe<&2, U32>, t), q), Presence.lookup_presence(U32, t, q, crit, pop)), Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), lk(t, q), Some{x}, hx))
  +hk = fk_ok(ks, ord, q, KeyMem.included_member(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord), q, incl, hmem))
  +ek = RU.equal_boolean(ST.kat(ks, s1), q, L.and_right(DST.lmem(s1, ord), String.eq(ST.kat(ks, s1), q), hk))
  +hm1 = am_at(t, ks, ord, s1, hmap, L.and_left(DST.lmem(s1, ord), String.eq(ST.kat(ks, s1), q), hk))
  +e1 = Equal.trans(Maybe<&2, U32>, lk(t, ST.kat(ks, s1)), lk(t, q), Some{x}, Equal.cong(String, Maybe<&2, U32>, z => lk(t, z), ST.kat(ks, s1), q, ek), hx)
  some_mapped(x, s1, L.subst(Maybe<&2, U32>, z => {ST.mapped_m(z, s1) == True{} : Bool}, lk(t, ST.kat(ks, s1)), Some{x}, e1, hm1))

# ---- deleting the key of a live slot ----

def wo_ne_c(+ks: List<&2, String>, +k: String, +x: String, +h: {Inv.member(C.without(ks, k), x) == True{} : Bool}, c: Bool, +ec: {String.eq(x, k) == c : Bool}) -> {String.eq(x, k) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      +e = RU.equal_boolean(x, k, ec)
      +h2 = L.subst(String, z => {Inv.member(C.without(ks, k), z) == True{} : Bool}, x, k, e, h)
      Empty.absurd({String.eq(x, k) == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Inv.member(C.without(ks, k), k), True{}, Equal.sym(Bool, Inv.member(C.without(ks, k), k), False{}, RU.filtering_removes_target(ks, k)), h2)))

def wo_ne(+ks: List<&2, String>, +k: String, +x: String, +h: {Inv.member(C.without(ks, k), x) == True{} : Bool}) -> {String.eq(x, k) == False{} : Bool}:
  wo_ne_c(ks, k, x, h, String.eq(x, k), {==})

def wo_mem(+ks: List<&2, String>, +k: String, +x: String, +h: {Inv.member(C.without(ks, k), x) == True{} : Bool}) -> {Inv.member(ks, x) == True{} : Bool}:
  Equal.trans(Bool, Inv.member(ks, x), Inv.member(C.without(ks, k), x), True{}, Equal.sym(Bool, Inv.member(C.without(ks, k), x), Inv.member(ks, x), RM.filter_other(ks, k, x, wo_ne(ks, k, x, h))), h)

def idel_go(+xs: List<&2, String>, +t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hsub: {Inv.included(xs, Map.keys(&2, Maybe<&2, U32>, Map.del(&2, Maybe<&2, U32>, t, ST.kat(ks, s)))) == True{} : Bool}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, SC.append(Nat, a, Con{s, b}))) == True{} : Bool}) -> {Inv.included(xs, ST.keys_at(ks, SC.append(Nat, a, b))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +k = ST.kat(ks, s)
      +K = Map.keys(&2, Maybe<&2, U32>, t)
      +K2 = Map.keys(&2, Maybe<&2, U32>, Map.del(&2, Maybe<&2, U32>, t, k))
      +hm = L.and_left(Inv.member(K2, x), Inv.included(r, K2), hsub)
      +hw = Equal.trans(Bool, Inv.member(C.without(K, k), x), Inv.member(K2, x), True{}, Equal.sym(Bool, Inv.member(K2, x), Inv.member(C.without(K, k), x), DelMem.filter_keys(U32, t, k, x, crit, pop)), hm)
      +hy = KeyMem.included_member(K, ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), x, incl, wo_mem(K, k, x, hw))
      L.and_intro(Inv.member(ST.keys_at(ks, SC.append(Nat, a, b)), x), Inv.included(r, ST.keys_at(ks, SC.append(Nat, a, b))),
        kmem_cut(ks, a, s, b, x, CS.symmetric_false(x, k, wo_ne(K, k, x, hw)), hy),
        idel_go(r, t, ks, a, s, b, L.and_right(Inv.member(K2, x), Inv.included(r, K2), hsub), crit, pop, incl))

def incl_del(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, SC.append(Nat, a, Con{s, b}))) == True{} : Bool}) -> {Inv.included(Map.keys(&2, Maybe<&2, U32>, Map.del(&2, Maybe<&2, U32>, t, ST.kat(ks, s))), ST.keys_at(ks, SC.append(Nat, a, b))) == True{} : Bool}:
  idel_go(Map.keys(&2, Maybe<&2, U32>, Map.del(&2, Maybe<&2, U32>, t, ST.kat(ks, s))), t, ks, a, s, b, CDM.included_self(Map.keys(&2, Maybe<&2, U32>, Map.del(&2, Maybe<&2, U32>, t, ST.kat(ks, s)))), crit, pop, incl)

def am_del(+t: Map<&2, Maybe<&2, U32>>, +k: String, +ks: List<&2, String>, +xs: List<&2, Nat>, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +hnk: {none_key(ks, xs, k) == True{} : Bool}, +hmap: {ST.all_mapped(t, ks, xs) == True{} : Bool}) -> {ST.all_mapped(Map.del(&2, Maybe<&2, U32>, t, k), ks, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      +ks1 = ST.kat(ks, s)
      +hne = not_false(String.eq(ks1, k), L.and_left(Bool.not(String.eq(ks1, k)), none_key(ks, r, k), hnk))
      +efr = DelFrame.other_lookup_unchanged(U32, t, k, ks1, R.critbit_certificate(Maybe<&2, U32>, t, crit), different_of(ks1, k, hne))
      L.and_intro(ST.mapped(Map.del(&2, Maybe<&2, U32>, t, k), ks1, s), ST.all_mapped(Map.del(&2, Maybe<&2, U32>, t, k), ks, r),
        L.subst(Maybe<&2, U32>, z => {ST.mapped_m(z, s) == True{} : Bool}, lk(t, ks1), lk(Map.del(&2, Maybe<&2, U32>, t, k), ks1), Equal.sym(Maybe<&2, U32>, lk(Map.del(&2, Maybe<&2, U32>, t, k), ks1), lk(t, ks1), efr), L.and_left(ST.mapped(t, ks1, s), ST.all_mapped(t, ks, r), hmap)),
        am_del(t, k, ks, r, crit, L.and_right(Bool.not(String.eq(ks1, k)), none_key(ks, r, k), hnk), L.and_right(ST.mapped(t, ks1, s), ST.all_mapped(t, ks, r), hmap)))

# ---- setting the key of a fresh slot ----

def am_set(+t: Map<&2, Maybe<&2, U32>>, +k: String, +v: Maybe<&2, U32>, +ks: List<&2, String>, +xs: List<&2, Nat>, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +hnk: {none_key(ks, xs, k) == True{} : Bool}, +hmap: {ST.all_mapped(t, ks, xs) == True{} : Bool}) -> {ST.all_mapped(Map.set(&2, Maybe<&2, U32>, t, k, v), ks, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      +ks1 = ST.kat(ks, s)
      +hne = not_false(String.eq(ks1, k), L.and_left(Bool.not(String.eq(ks1, k)), none_key(ks, r, k), hnk))
      +efr = SetFrame.other_lookup_unchanged(U32, t, k, v, ks1, hne, crit)
      L.and_intro(ST.mapped(Map.set(&2, Maybe<&2, U32>, t, k, v), ks1, s), ST.all_mapped(Map.set(&2, Maybe<&2, U32>, t, k, v), ks, r),
        L.subst(Maybe<&2, U32>, z => {ST.mapped_m(z, s) == True{} : Bool}, lk(t, ks1), lk(Map.set(&2, Maybe<&2, U32>, t, k, v), ks1), Equal.sym(Maybe<&2, U32>, lk(Map.set(&2, Maybe<&2, U32>, t, k, v), ks1), lk(t, ks1), efr), L.and_left(ST.mapped(t, ks1, s), ST.all_mapped(t, ks, r), hmap)),
        am_set(t, k, v, ks, r, crit, L.and_right(Bool.not(String.eq(ks1, k)), none_key(ks, r, k), hnk), L.and_right(ST.mapped(t, ks1, s), ST.all_mapped(t, ks, r), hmap)))

def iset_c(+x0: String, +r: List<&2, String>, +t: Map<&2, Maybe<&2, U32>>, +k: String, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +hks: {ST.kat(ks, s) == k : String}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}, c: Bool, +ec: {String.eq(x0, k) == c : Bool}, +hor: {Bool.or(c, Inv.member(Map.keys(&2, Maybe<&2, U32>, t), x0)) == True{} : Bool}, +ih: {Inv.included(r, ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))) == True{} : Bool}) -> {Inv.included(Con{x0, r}, ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))) == True{} : Bool}:
  match c:
    case True{}:
      +ex = RU.equal_boolean(x0, k, ec)
      +hk = L.subst(String, z => {String.eq(z, x0) == True{} : Bool}, x0, ST.kat(ks, s), Equal.trans(String, x0, k, ST.kat(ks, s), ex, Equal.sym(String, ST.kat(ks, s), k, hks)), LR.string_reflexive(x0))
      L.and_intro(Inv.member(ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}})), x0), Inv.included(r, ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))),
        Equal.trans(Bool, Inv.member(ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}})), x0), Bool.or(Inv.member(ST.keys_at(ks, ord), x0), Bool.or(String.eq(ST.kat(ks, s), x0), False{})), True{}, kmem_snoc(ks, ord, s, x0),
          or_true_r(Inv.member(ST.keys_at(ks, ord), x0), Bool.or(String.eq(ST.kat(ks, s), x0), False{}), or_true_l(String.eq(ST.kat(ks, s), x0), False{}, hk))),
        ih)
    case False{}:
      L.and_intro(Inv.member(ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}})), x0), Inv.included(r, ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))),
        Equal.trans(Bool, Inv.member(ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}})), x0), Bool.or(Inv.member(ST.keys_at(ks, ord), x0), Bool.or(String.eq(ST.kat(ks, s), x0), False{})), True{}, kmem_snoc(ks, ord, s, x0),
          or_true_l(Inv.member(ST.keys_at(ks, ord), x0), Bool.or(String.eq(ST.kat(ks, s), x0), False{}), KeyMem.included_member(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord), x0, incl, hor))),
        ih)

def iset_go(+xs: List<&2, String>, +t: Map<&2, Maybe<&2, U32>>, +k: String, +x: U32, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +hks: {ST.kat(ks, s) == k : String}, +hsub: {Inv.included(xs, Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, k, Some{x}))) == True{} : Bool}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}) -> {Inv.included(xs, ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x0, +r}:
      +K2 = Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, k, Some{x}))
      +hm = L.and_left(Inv.member(K2, x0), Inv.included(r, K2), hsub)
      +hor = Equal.trans(Bool, Bool.or(String.eq(x0, k), Inv.member(Map.keys(&2, Maybe<&2, U32>, t), x0)), Inv.member(K2, x0), True{}, Equal.sym(Bool, Inv.member(K2, x0), Bool.or(String.eq(x0, k), Inv.member(Map.keys(&2, Maybe<&2, U32>, t), x0)), SetMem.membership(U32, t, k, x, x0, crit, pop)), hm)
      iset_c(x0, r, t, k, ks, ord, s, hks, incl, String.eq(x0, k), {==}, hor,
        iset_go(r, t, k, x, ks, ord, s, hks, L.and_right(Inv.member(K2, x0), Inv.included(r, K2), hsub), crit, pop, incl))

def incl_set(+t: Map<&2, Maybe<&2, U32>>, +k: String, +x: U32, +ks: List<&2, String>, +ord: List<&2, Nat>, +s: Nat, +hks: {ST.kat(ks, s) == k : String}, +crit: {Inv.critbit(Maybe<&2, U32>, t) == True{} : Bool}, +pop: {Pop.populated(U32, t) == True{} : Bool}, +incl: {Inv.included(Map.keys(&2, Maybe<&2, U32>, t), ST.keys_at(ks, ord)) == True{} : Bool}) -> {Inv.included(Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, k, Some{x})), ST.keys_at(ks, SC.append(Nat, ord, Con{s, Nil{}}))) == True{} : Bool}:
  iset_go(Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, k, Some{x})), t, k, x, ks, ord, s, hks, CDM.included_self(Map.keys(&2, Maybe<&2, U32>, Map.set(&2, Maybe<&2, U32>, t, k, Some{x}))), crit, pop, incl)
