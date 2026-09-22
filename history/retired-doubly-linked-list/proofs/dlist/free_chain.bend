import Base
import ./mu0.bend as MU0
import ./retarget.bend as RT
import ../lib/u32.bend as U
import ../graph/shift.bend as SH
import ../../types/doubly_linked_list.bend as E
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ./state.bend as ST
import ./links.bend as LK
import ./split.bend as SP
import ./reuse_insert.bend as RI

# The free chain is singly linked through retired slots of the DLL's next
# arena. This is a proof-only list of slot IDs, never a runtime list.
def links(ids: List<&2, Nat>, +ns: List<&2, U32>) -> Bool:
  match ids:
    case Nil{}:
      True{}
    case Con{+i, +rest}:
      Bool.and(U32.is_eq(ST.lat(ns, i), ST.hd(rest)), links(rest, ns))

def frame(+ids: List<&2, Nat>, +ns: List<&2, U32>, +i: Nat, +v: U32, +dead: {ST.lmem(i, ids) == False{} : Bool}) -> {links(ids, SC.update(U32, ns, i, v)) == links(ids, ns) : Bool}:
  match ids:
    case Nil{}:
      {==}
    case Con{+j, +rest}:
      +hne = LK.or_false_l(Nat.is_eq(j, i), ST.lmem(i, rest), dead)
      +hrt = LK.or_false_r(Nat.is_eq(j, i), ST.lmem(i, rest), dead)
      %Equal.sym(U32, ST.lat(SC.update(U32, ns, i, v), j), ST.lat(ns, j), LK.lat_other(ns, i, v, j, SH.ne_flip(j, i, hne))) : {Bool.and(U32.is_eq(_, ST.hd(rest)), links(rest, SC.update(U32, ns, i, v))) == links(Con{j, rest}, ns) : Bool}
      %Equal.sym(Bool, links(rest, SC.update(U32, ns, i, v)), links(rest, ns), frame(rest, ns, i, v, hrt)) : {Bool.and(U32.is_eq(ST.lat(ns, j), ST.hd(rest)), _) == links(Con{j, rest}, ns) : Bool}
      {==}

def prepend(+ids: List<&2, Nat>, +ns: List<&2, U32>, +i: Nat, +dead: {ST.lmem(i, ids) == False{} : Bool}, +hi: {Nat.is_lt(i, SC.length(U32, ns)) == True{} : Bool}, +h: {links(ids, ns) == True{} : Bool}) -> {links(Con{i, ids}, SC.update(U32, ns, i, ST.hd(ids))) == True{} : Bool}:
  +tail = Equal.trans(Bool, links(ids, SC.update(U32, ns, i, ST.hd(ids))), links(ids, ns), True{}, frame(ids, ns, i, ST.hd(ids), dead), h)
  +head = Equal.cong(U32, Bool, z => U32.is_eq(z, ST.hd(ids)), ST.lat(SC.update(U32, ns, i, ST.hd(ids)), i), ST.hd(ids), LK.lat_same(ns, i, ST.hd(ids), hi))
  L.and_intro(U32.is_eq(ST.lat(SC.update(U32, ns, i, ST.hd(ids)), i), ST.hd(ids)), links(ids, SC.update(U32, ns, i, ST.hd(ids))), Equal.trans(Bool, U32.is_eq(ST.lat(SC.update(U32, ns, i, ST.hd(ids)), i), ST.hd(ids)), U32.is_eq(ST.hd(ids), ST.hd(ids)), True{}, head, RT.eq_self(ST.hd(ids), ST.hd(ids), {==})), tail)

type Shadow<-T: Data> is Data:
  Pool{live: ST.Shadow<T>, free: List<&2, Nat>}

def real(~T: Data, sh: Shadow<T>) -> D.DList<T>:
  Pool{live, free} = sh
  RI.real_with_free(~T, live, ST.hd(free))

def entries(~T: Data, m: DS.Model<T>) -> List<&2, E.Item<T>>:
  DS.DM{tag, fresh, items} = m
  items

def model(~T: Data, sh: Shadow<T>) -> List<&2, T>:
  Pool{live, free} = sh
  DS.vals(T, entries(~T, ST.model(~T, live)))


def good_parts(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +free: List<&2, Nat>) -> Bool:
  Bool.and(ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}),
    Bool.and(ST.alllt(free, fresh),
      Bool.and(ST.nodup(free),
        Bool.and(SP.disj(ord, free),
          Bool.and(links(free, AR.slots(U32, tn)), Nat.is_eq(Nat.add(SC.length(Nat, ord), SC.length(Nat, free)), fresh))))))

def good(~T: Data, sh: Shadow<T>) -> Bool:
  Pool{ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, free} = sh
  good_parts(~T, tag, fresh, depth, tv, tp, tn, ord, free)

def initial(~T: Data) -> Shadow<T>:
  Pool{ST.initial(~T, 0), Nil{}}

def new_good(~T: Data) -> {good(~T, initial(~T)) == True{} : Bool}:
  {==}

def new_real(~T: Data) -> {real(~T, initial(~T)) == D.new(~T, 0) : D.DList<T>}:
  {==}

# Relinking the last live node cannot touch the disjoint retired chain.
def last_not_free(+rest: List<&2, Nat>, +x: Nat, +free: List<&2, Nat>, +hx: {ST.lmem(x, free) == False{} : Bool}, +hd: {SP.disj(rest, free) == True{} : Bool}) -> {ST.lmem(ST.lst_or(rest, x), free) == False{} : Bool}:
  match rest:
    case Nil{}:
      hx
    case Con{+y, +tail}:
      last_not_free(tail, y, free, MU0.not_true(ST.lmem(y, free), L.and_left(Bool.not(ST.lmem(y, free)), SP.disj(tail, free), hd)), L.and_right(Bool.not(ST.lmem(y, free)), SP.disj(tail, free), hd))

def frame_live_tail(+free: List<&2, Nat>, +ns: List<&2, U32>, +live: List<&2, Nat>, +v: U32, +disjoint: {SP.disj(live, free) == True{} : Bool}) -> {links(free, RT.nupd(ns, live, v)) == links(free, ns) : Bool}:
  match live:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      frame(free, ns, ST.lst_or(rest, x), v, last_not_free(rest, x, free, MU0.not_true(ST.lmem(x, free), L.and_left(Bool.not(ST.lmem(x, free)), SP.disj(rest, free), disjoint)), L.and_right(Bool.not(ST.lmem(x, free)), SP.disj(rest, free), disjoint)))

# The remaining free chain survives both writes made by insertion: initialize
# the reused node, then point the previous live node at it.
def reuse_links(+free: List<&2, Nat>, +ns: List<&2, U32>, +i: Nat, +next: U32, +live_prefix: List<&2, Nat>, +dead: {ST.lmem(i, free) == False{} : Bool}, +disjoint: {SP.disj(live_prefix, free) == True{} : Bool}, +h: {links(free, ns) == True{} : Bool}) -> {links(free, RT.nupd(SC.update(U32, ns, i, next), live_prefix, ST.ln(i))) == True{} : Bool}:
  Equal.trans(Bool, links(free, RT.nupd(SC.update(U32, ns, i, next), live_prefix, ST.ln(i))), links(free, SC.update(U32, ns, i, next)), True{}, frame_live_tail(free, SC.update(U32, ns, i, next), live_prefix, ST.ln(i), disjoint), Equal.trans(Bool, links(free, SC.update(U32, ns, i, next)), links(free, ns), True{}, frame(free, ns, i, next, dead), h))

def disjoint_drop(+a: List<&2, Nat>, +i: Nat, +b: List<&2, Nat>, +h: {SP.disj(a, Con{i, b}) == True{} : Bool}) -> {SP.disj(a, b) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hxb = LK.or_false_r(Nat.is_eq(i, x), ST.lmem(x, b), MU0.not_true(ST.lmem(x, Con{i, b}), L.and_left(Bool.not(ST.lmem(x, Con{i, b})), SP.disj(rest, Con{i, b}), h)))
      L.and_intro(Bool.not(ST.lmem(x, b)), SP.disj(rest, b), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(x, b), Equal.sym(Bool, ST.lmem(x, b), False{}, hxb), {==}), disjoint_drop(rest, i, b, L.and_right(Bool.not(ST.lmem(x, Con{i, b})), SP.disj(rest, Con{i, b}), h)))

def disjoint_insert(+a: List<&2, Nat>, +b: List<&2, Nat>, +i: Nat, +free: List<&2, Nat>, +hi: {ST.lmem(i, free) == False{} : Bool}, +h: {SP.disj(SC.append(Nat, a, b), free) == True{} : Bool}) -> {SP.disj(SC.append(Nat, a, Con{i, b}), free) == True{} : Bool}:
  match a:
    case Nil{}:
      L.and_intro(Bool.not(ST.lmem(i, free)), SP.disj(b, free), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(i, free), Equal.sym(Bool, ST.lmem(i, free), False{}, hi), {==}), h)
    case Con{+x, +rest}:
      L.and_intro(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, Con{i, b}), free), L.and_left(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, b), free), h), disjoint_insert(rest, b, i, free, hi, L.and_right(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, b), free), h)))

def disjoint_prefix(+a: List<&2, Nat>, +b: List<&2, Nat>, +free: List<&2, Nat>, +h: {SP.disj(SC.append(Nat, a, b), free) == True{} : Bool}) -> {SP.disj(a, free) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      L.and_intro(Bool.not(ST.lmem(x, free)), SP.disj(rest, free), L.and_left(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, b), free), h), disjoint_prefix(rest, b, free, L.and_right(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, b), free), h)))

def disjoint_cut(+a: List<&2, Nat>, +i: Nat, +b: List<&2, Nat>, +free: List<&2, Nat>, +h: {SP.disj(SC.append(Nat, a, Con{i, b}), free) == True{} : Bool}) -> {SP.disj(SC.append(Nat, a, b), free) == True{} : Bool}:
  match a:
    case Nil{}:
      L.and_right(Bool.not(ST.lmem(i, free)), SP.disj(b, free), h)
    case Con{+x, +rest}:
      L.and_intro(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, b), free), L.and_left(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, Con{i, b}), free), h), disjoint_cut(rest, i, b, free, L.and_right(Bool.not(ST.lmem(x, free)), SP.disj(SC.append(Nat, rest, Con{i, b}), free), h)))

def removed_absent(+a: List<&2, Nat>, +i: Nat, +b: List<&2, Nat>, +h: {ST.nodup(SC.append(Nat, a, Con{i, b})) == True{} : Bool}) -> {ST.lmem(i, SC.append(Nat, a, b)) == False{} : Bool}:
  +ha = SP.disj_mem(a, Con{i, b}, i, SP.nodup_disj(a, Con{i, b}, h), L.subst(Bool, z => {Bool.or(z, ST.lmem(i, b)) == True{} : Bool}, True{}, Nat.is_eq(i, i), Equal.sym(Bool, Nat.is_eq(i, i), True{}, N.is_eq_refl(i)), {==}))
  +hb = MU0.not_true(ST.lmem(i, b), L.and_left(Bool.not(ST.lmem(i, b)), ST.nodup(b), SP.nodup_app_r(a, Con{i, b}, h)))
  Equal.trans(Bool, ST.lmem(i, SC.append(Nat, a, b)), Bool.or(ST.lmem(i, a), ST.lmem(i, b)), False{}, SP.lmem_app(i, a, b), SP.or_ff(ST.lmem(i, a), ST.lmem(i, b), ha, hb))
