import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/balanced_search_tree.bend as B
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ../balanced_search_tree/sorted.bend as SO
import ../balanced_search_tree/tree.bend as T
import ../balanced_search_tree/steps.bend as ST
import ../balanced_search_tree/api.bend as API

# Graph representation facts: the adjacency map's entry list, with every
# neighbour set replaced by its abstraction, is the spec's adjacency list.
# All ordered-map facts come from the checked U32 instance of
# proofs/balanced_search_tree/api.bend.

def sabs(s: B.OrdMap<U32, Unit>) -> List<&2, BE.Entry<U32, Unit>>:
  ST.abs(~U32, ~U32.cmp, Unit, s)

def sinv(s: B.OrdMap<U32, Unit>) -> Bool:
  ST.inv(~U32, ~U32.cmp, Unit, s)

def aabs(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>) -> List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>:
  ST.abs(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj)

def ainv(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>) -> Bool:
  ST.inv(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj)

def amap(xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{BE.Entry{k, s}, t}:
      Con{BE.Entry{k, sabs(s)}, amap(t)}

def mapM(m: Maybe<&2, B.OrdMap<U32, Unit>>) -> Maybe<&2, List<&2, BE.Entry<U32, Unit>>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{sabs(s)}

# Every neighbour set satisfies the ordered-map invariant.
def allinv(xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{BE.Entry{k, s}, t}:
      Bool.and(sinv(s), allinv(t))

def allM(m: Maybe<&2, B.OrdMap<U32, Unit>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      sinv(s)

# ---- abstraction commutes with the finite-map operations ----

def amap_find_c(+k: U32, +k2: U32, +s: B.OrdMap<U32, Unit>, +t: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, c: Cmp, +ec: {U32.cmp(k, k2) == c : Cmp}, +ih: {S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(t)) == mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t)) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}) -> {S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(Con{BE.Entry{k2, s}, t})) == mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, Con{BE.Entry{k2, s}, t})) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  match c:
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), EQ{}, ec) : {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, _, BE.Entry{k2, sabs(s)}, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(t))) == mapM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}
      {==}
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), LT{}, ec) : {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, _, BE.Entry{k2, sabs(s)}, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(t))) == mapM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}
      ih
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), GT{}, ec) : {S.find_at(U32, List<&2, BE.Entry<U32, Unit>>, _, BE.Entry{k2, sabs(s)}, S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(t))) == mapM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}
      ih

def amap_find(+k: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {S.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(xs)) == mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs)) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s}, +t}:
      amap_find_c(k, k2, s, t, U32.cmp(k, k2), {==}, amap_find(k, t))

def amap_ins_c(+k: U32, +s: B.OrdMap<U32, Unit>, +k2: U32, +s2: B.OrdMap<U32, Unit>, +t: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, c: Cmp, +ec: {U32.cmp(k, k2) == c : Cmp}, +ih: {amap(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t)) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(t)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}) -> {amap(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, Con{BE.Entry{k2, s2}, t})) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(Con{BE.Entry{k2, s2}, t})) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), LT{}, ec) : {amap(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == S.ins_at(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, _, k, sabs(s), BE.Entry{k2, sabs(s2)}, amap(t), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(t))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), EQ{}, ec) : {amap(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == S.ins_at(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, _, k, sabs(s), BE.Entry{k2, sabs(s2)}, amap(t), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(t))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), GT{}, ec) : {amap(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == S.ins_at(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, _, k, sabs(s), BE.Entry{k2, sabs(s2)}, amap(t), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(t))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}
      LL.cons_cong(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, BE.Entry{k2, sabs(s2)}, amap(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(t)), ih)

def amap_ins(+k: U32, +s: B.OrdMap<U32, Unit>, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {amap(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, xs)) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, sabs(s), amap(xs)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s2}, +t}:
      amap_ins_c(k, s, k2, s2, t, U32.cmp(k, k2), {==}, amap_ins(k, s, t))

def amap_keep(b: Bool, +k2: U32, +s2: B.OrdMap<U32, Unit>, +r1: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +r2: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +e: {amap(r1) == r2 : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}) -> {amap(S.keep_at(U32, B.OrdMap<U32, Unit>, b, BE.Entry{k2, s2}, r1)) == S.keep_at(U32, List<&2, BE.Entry<U32, Unit>>, b, BE.Entry{k2, sabs(s2)}, r2) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match b:
    case True{}:
      LL.cons_cong(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, BE.Entry{k2, sabs(s2)}, amap(r1), r2, e)
    case False{}:
      e

def amap_del(+k: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {amap(S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs)) == S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(xs)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s2}, +t}:
      amap_keep(S.keep(U32.cmp(k, k2)), k2, s2, S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t), S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, k, amap(t)), amap_del(k, t))

def keys_amap(+xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {GS.keys(List<&2, BE.Entry<U32, Unit>>, amap(xs)) == GS.keys(B.OrdMap<U32, Unit>, xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      LL.cons_cong(U32, k, GS.keys(List<&2, BE.Entry<U32, Unit>>, amap(t)), GS.keys(B.OrdMap<U32, Unit>, t), keys_amap(t))

def keys_eq(-V: Data, +xs: List<&2, BE.Entry<U32, V>>) -> {G.keys(V, xs) == GS.keys(V, xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      LL.cons_cong(U32, BE.key(U32, V, e), G.keys(V, t), GS.keys(V, t), keys_eq(V, t))

# Neighbour listing of a set: src keys of to_list against spec keys.
def nkeys(+s: B.OrdMap<U32, Unit>) -> {G.keys(Unit, B.to_list(U32, Unit, s)) == GS.keys(Unit, sabs(s)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, G.keys(Unit, B.to_list(U32, Unit, s)), G.keys(Unit, sabs(s)), GS.keys(Unit, sabs(s)),
    Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, U32>, z => G.keys(Unit, z), B.to_list(U32, Unit, s), sabs(s), API.to_list_ok(~U32, ~U32.cmp, Unit, s)),
    keys_eq(Unit, sabs(s)))

def is_some_mapM(+m: Maybe<&2, B.OrdMap<U32, Unit>>) -> {S.is_some(List<&2, BE.Entry<U32, Unit>>, mapM(m)) == S.is_some(B.OrdMap<U32, Unit>, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      {==}

# ---- edge listing ----

def keep_eq(b: Bool, +x: E.Edge, +r1: List<&2, E.Edge>, +r2: List<&2, E.Edge>, +e: {r1 == r2 : List<&2, E.Edge>}) -> {G.keep_if(b, x, r1) == GS.keep_if(b, x, r2) : List<&2, E.Edge>}:
  match b:
    case True{}:
      LL.cons_cong(E.Edge, x, r1, r2, e)
    case False{}:
      e

def out_eq(+d: Bool, +u: U32, +ws: List<&2, U32>) -> {G.out_edges(d, u, ws) == GS.out_edges(d, u, ws) : List<&2, E.Edge>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      keep_eq(Bool.or(d, Cmp.is_lt(U32.cmp(u, w))), E.Edge{u, w}, G.out_edges(d, u, t), GS.out_edges(d, u, t), out_eq(d, u, t))

def edges_ok(+d: Bool, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {G.edges_go(d, xs) == GS.all_edges(d, amap(xs)) : List<&2, E.Edge>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+u, +s}, +t}:
      Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, G.out_edges(d, u, G.keys(Unit, B.to_list(U32, Unit, s))), G.edges_go(d, t)), SC.append(E.Edge, GS.out_edges(d, u, GS.keys(Unit, sabs(s))), G.edges_go(d, t)), SC.append(E.Edge, GS.out_edges(d, u, GS.keys(Unit, sabs(s))), GS.all_edges(d, amap(t))),
        Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, z, G.edges_go(d, t)), G.out_edges(d, u, G.keys(Unit, B.to_list(U32, Unit, s))), GS.out_edges(d, u, GS.keys(Unit, sabs(s))),
          Equal.trans(List<&2, E.Edge>, G.out_edges(d, u, G.keys(Unit, B.to_list(U32, Unit, s))), G.out_edges(d, u, GS.keys(Unit, sabs(s))), GS.out_edges(d, u, GS.keys(Unit, sabs(s))),
            Equal.cong(List<&2, U32>, List<&2, E.Edge>, z => G.out_edges(d, u, z), G.keys(Unit, B.to_list(U32, Unit, s)), GS.keys(Unit, sabs(s)), nkeys(s)),
            out_eq(d, u, GS.keys(Unit, sabs(s))))),
        Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, GS.out_edges(d, u, GS.keys(Unit, sabs(s))), z), G.edges_go(d, t), GS.all_edges(d, amap(t)), edges_ok(d, t)))

# ---- the all-sets invariant ----

def allinv_find_c(+k: U32, +k2: U32, +s: B.OrdMap<U32, Unit>, +t: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, c: Cmp, +ec: {U32.cmp(k, k2) == c : Cmp}, +a: {allinv(Con{BE.Entry{k2, s}, t}) == True{} : Bool}, +ih: {allM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t)) == True{} : Bool}) -> {allM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, Con{BE.Entry{k2, s}, t})) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), EQ{}, ec) : {allM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) == True{} : Bool}
      L.and_left(sinv(s), allinv(t), a)
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), LT{}, ec) : {allM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) == True{} : Bool}
      ih
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), GT{}, ec) : {allM(S.find_at(U32, B.OrdMap<U32, Unit>, _, BE.Entry{k2, s}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t))) == True{} : Bool}
      ih

def allinv_find(+k: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +a: {allinv(xs) == True{} : Bool}) -> {allM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s}, +t}:
      allinv_find_c(k, k2, s, t, U32.cmp(k, k2), {==}, a, allinv_find(k, t, L.and_right(sinv(s), allinv(t), a)))

def allinv_ins_c(+k: U32, +s: B.OrdMap<U32, Unit>, +k2: U32, +s2: B.OrdMap<U32, Unit>, +t: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, c: Cmp, +ec: {U32.cmp(k, k2) == c : Cmp}, +i: {sinv(s) == True{} : Bool}, +a: {allinv(Con{BE.Entry{k2, s2}, t}) == True{} : Bool}, +ih: {allinv(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t)) == True{} : Bool}) -> {allinv(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, Con{BE.Entry{k2, s2}, t})) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), LT{}, ec) : {allinv(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == True{} : Bool}
      L.and_intro(sinv(s), allinv(Con{BE.Entry{k2, s2}, t}), i, a)
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), EQ{}, ec) : {allinv(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == True{} : Bool}
      L.and_intro(sinv(s), allinv(t), i, L.and_right(sinv(s2), allinv(t), a))
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(k, k2), GT{}, ec) : {allinv(S.ins_at(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _, k, s, BE.Entry{k2, s2}, t, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t))) == True{} : Bool}
      L.and_intro(sinv(s2), allinv(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, t)), L.and_left(sinv(s2), allinv(t), a), ih)

def allinv_ins(+k: U32, +s: B.OrdMap<U32, Unit>, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +i: {sinv(s) == True{} : Bool}, +a: {allinv(xs) == True{} : Bool}) -> {allinv(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, s, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(sinv(s), True{}, i, {==})
    case Con{BE.Entry{+k2, +s2}, +t}:
      allinv_ins_c(k, s, k2, s2, t, U32.cmp(k, k2), {==}, i, a, allinv_ins(k, s, t, i, L.and_right(sinv(s2), allinv(t), a)))

def allinv_keep(b: Bool, +k2: U32, +s2: B.OrdMap<U32, Unit>, +r: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +i: {sinv(s2) == True{} : Bool}, +a: {allinv(r) == True{} : Bool}) -> {allinv(S.keep_at(U32, B.OrdMap<U32, Unit>, b, BE.Entry{k2, s2}, r)) == True{} : Bool}:
  match b:
    case True{}:
      L.and_intro(sinv(s2), allinv(r), i, a)
    case False{}:
      a

def allinv_del(+k: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +a: {allinv(xs) == True{} : Bool}) -> {allinv(S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s2}, +t}:
      allinv_keep(S.keep(U32.cmp(k, k2)), k2, s2, S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, t), L.and_left(sinv(s2), allinv(t), a), allinv_del(k, t, L.and_right(sinv(s2), allinv(t), a)))

# The set at key k, known present, satisfies the invariant.
def some_inv(+xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +k: U32, +s: B.OrdMap<U32, Unit>, +a: {allinv(xs) == True{} : Bool}, +f: {S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs) == Some{s} : Maybe<&2, B.OrdMap<U32, Unit>>}) -> {sinv(s) == True{} : Bool}:
  L.subst(Maybe<&2, B.OrdMap<U32, Unit>>, z => {allM(z) == True{} : Bool}, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, k, xs), Some{s}, f, allinv_find(k, xs, a))

# ---- removing a vertex from every set (G.strip) ----

def sdel_abs(+s: B.OrdMap<U32, Unit>, +w: U32, +i: {sinv(s) == True{} : Bool}) -> {sabs(G.sdel(s, w)) == GS.sdel(w, sabs(s)) : List<&2, BE.Entry<U32, Unit>>}:
  Pair.fst({sabs(G.sdel(s, w)) == S.del(~U32, ~U32.cmp, Unit, w, sabs(s)) : List<&2, BE.Entry<U32, Unit>>}, {sinv(G.sdel(s, w)) == True{} : Bool}, API.remove_ok(~U32, ~U32.cmp, ~O.u32_order, Unit, s, w, i))

def sdel_inv(+s: B.OrdMap<U32, Unit>, +w: U32, +i: {sinv(s) == True{} : Bool}) -> {sinv(G.sdel(s, w)) == True{} : Bool}:
  Pair.snd({sabs(G.sdel(s, w)) == S.del(~U32, ~U32.cmp, Unit, w, sabs(s)) : List<&2, BE.Entry<U32, Unit>>}, {sinv(G.sdel(s, w)) == True{} : Bool}, API.remove_ok(~U32, ~U32.cmp, ~O.u32_order, Unit, s, w, i))

def smap(+w: U32, xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{BE.Entry{k, s}, t}:
      Con{BE.Entry{k, G.sdel(s, w)}, smap(w, t)}

def smap_app(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +ys: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {smap(w, SC.append(BE.Entry<U32, B.OrdMap<U32, Unit>>, xs, ys)) == SC.append(BE.Entry<U32, B.OrdMap<U32, Unit>>, smap(w, xs), smap(w, ys)) : List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      LL.cons_cong(BE.Entry<U32, B.OrdMap<U32, Unit>>, BE.Entry{k, G.sdel(s, w)}, smap(w, SC.append(BE.Entry<U32, B.OrdMap<U32, Unit>>, t, ys)), SC.append(BE.Entry<U32, B.OrdMap<U32, Unit>>, smap(w, t), smap(w, ys)), smap_app(w, t, ys))

def strip_io(+t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)) == smap(w, T.io(U32, B.OrdMap<U32, Unit>, t)) : List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, BE.Entry{+k, +s}, +r}:
      -EN = BE.Entry<U32, B.OrdMap<U32, Unit>>
      Equal.trans(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, SC.append(EN, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), Con{BE.Entry{k, G.sdel(s, w)}, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))}), SC.append(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), Con{BE.Entry{k, G.sdel(s, w)}, smap(w, T.io(U32, B.OrdMap<U32, Unit>, r))}), smap(w, SC.append(EN, T.io(U32, B.OrdMap<U32, Unit>, l), Con{BE.Entry{k, s}, T.io(U32, B.OrdMap<U32, Unit>, r)})),
        Equal.trans(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, SC.append(EN, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), Con{BE.Entry{k, G.sdel(s, w)}, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))}), SC.append(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), Con{BE.Entry{k, G.sdel(s, w)}, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))}), SC.append(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), Con{BE.Entry{k, G.sdel(s, w)}, smap(w, T.io(U32, B.OrdMap<U32, Unit>, r))}),
          Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, z => SC.append(EN, z, Con{BE.Entry{k, G.sdel(s, w)}, T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))}), T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), strip_io(l, w)),
          Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, z => SC.append(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), Con{BE.Entry{k, G.sdel(s, w)}, z}), T.io(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)), smap(w, T.io(U32, B.OrdMap<U32, Unit>, r)), strip_io(r, w))),
        Equal.sym(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, smap(w, SC.append(EN, T.io(U32, B.OrdMap<U32, Unit>, l), Con{BE.Entry{k, s}, T.io(U32, B.OrdMap<U32, Unit>, r)})), SC.append(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, l)), Con{BE.Entry{k, G.sdel(s, w)}, smap(w, T.io(U32, B.OrdMap<U32, Unit>, r))}), smap_app(w, T.io(U32, B.OrdMap<U32, Unit>, l), Con{BE.Entry{k, s}, T.io(U32, B.OrdMap<U32, Unit>, r)})))

def strip_abs(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {aabs(G.strip(adj, w)) == smap(w, aabs(adj)) : List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>}:
  match adj:
    case B.BST{n, +t}:
      strip_io(t, w)

def above_smap(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +k: U32) -> {SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, xs), k) == SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, xs, k) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s}, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(Cmp.is_lt(U32.cmp(k, k2)), z), SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, t), k), SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), above_smap(w, t, k))

def sorted_smap(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, xs)) == SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      %Equal.sym(Bool, SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, t), k), SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), above_smap(w, t, k)) : {Bool.and(_, SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, t))) == Bool.and(SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t)) : Bool}
      Equal.cong(Bool, Bool, z => Bool.and(SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), z), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, t)), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t), sorted_smap(w, t))

def length_smap(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> {SC.length(BE.Entry<U32, B.OrdMap<U32, Unit>>, smap(w, xs)) == SC.length(BE.Entry<U32, B.OrdMap<U32, Unit>>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(BE.Entry<U32, B.OrdMap<U32, Unit>>, smap(w, t)), SC.length(BE.Entry<U32, B.OrdMap<U32, Unit>>, t), length_smap(w, t))

def isred_strip(+t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)) == B.is_red(U32, B.OrdMap<U32, Unit>, t) : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{c, l, BE.Entry{k, s}, r}:
      {==}

def bh_strip(+t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)) == T.bh(U32, B.OrdMap<U32, Unit>, t) : Nat}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, BE.Entry{k, s}, r}:
      Equal.cong(Nat, Nat, z => T.bh_c(c, z), T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), T.bh(U32, B.OrdMap<U32, Unit>, l), bh_strip(l, w))

def nrrc_strip(c: B.Color, +l: B.Tree<U32, B.OrdMap<U32, Unit>>, +r: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)) == T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r) : Bool}:
  match c:
    case B.R{}:
      Equal.trans(Bool,
        Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w))), Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)))),
        Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, l)), Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)))),
        Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, l)), Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, r))),
        Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)))), B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), B.is_red(U32, B.OrdMap<U32, Unit>, l), isred_strip(l, w)),
        Equal.cong(Bool, Bool, z => Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, l)), Bool.not(z)), B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)), B.is_red(U32, B.OrdMap<U32, Unit>, r), isred_strip(r, w)))
    case B.B{}:
      {==}

def ok_strip(+t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)) == T.ok(U32, B.OrdMap<U32, Unit>, t) : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, BE.Entry{k, s}, +r}:
      %Equal.sym(Bool, T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), T.ok(U32, B.OrdMap<U32, Unit>, l), ok_strip(l, w)) : {Bool.and(Bool.and(_, T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)))) == Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r))) : Bool}
      %Equal.sym(Bool, T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)), T.ok(U32, B.OrdMap<U32, Unit>, r), ok_strip(r, w)) : {Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), _), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)))) == Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r))) : Bool}
      %Equal.sym(Nat, T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(l, w)), T.bh(U32, B.OrdMap<U32, Unit>, l), bh_strip(l, w)) : {Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(_, T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w))), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)))) == Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r))) : Bool}
      %Equal.sym(Nat, T.bh(U32, B.OrdMap<U32, Unit>, G.strip_tree(r, w)), T.bh(U32, B.OrdMap<U32, Unit>, r), bh_strip(r, w)) : {Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), _), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)))) == Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r))) : Bool}
      %Equal.sym(Bool, T.nrr_c(U32, B.OrdMap<U32, Unit>, c, G.strip_tree(l, w), G.strip_tree(r, w)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r), nrrc_strip(c, l, r, w)) : {Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), _)) == Bool.and(Bool.and(T.ok(U32, B.OrdMap<U32, Unit>, l), T.ok(U32, B.OrdMap<U32, Unit>, r)), Bool.and(Nat.is_eq(T.bh(U32, B.OrdMap<U32, Unit>, l), T.bh(U32, B.OrdMap<U32, Unit>, r)), T.nrr_c(U32, B.OrdMap<U32, Unit>, c, l, r))) : Bool}
      {==}

def bal_strip(+t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> {T.bal(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)) == T.bal(U32, B.OrdMap<U32, Unit>, t) : Bool}:
  Equal.trans(Bool,
    Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w))), T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w))),
    Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, t)), T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w))),
    Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, t)), T.ok(U32, B.OrdMap<U32, Unit>, t)),
    Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w))), B.is_red(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)), B.is_red(U32, B.OrdMap<U32, Unit>, t), isred_strip(t, w)),
    Equal.cong(Bool, Bool, z => Bool.and(Bool.not(B.is_red(U32, B.OrdMap<U32, Unit>, t)), z), T.ok(U32, B.OrdMap<U32, Unit>, G.strip_tree(t, w)), T.ok(U32, B.OrdMap<U32, Unit>, t), ok_strip(t, w)))

def strip_inv(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +w: U32, +g: {ainv(adj) == True{} : Bool}) -> {ainv(G.strip(adj, w)) == True{} : Bool}:
  match adj:
    case B.BST{+n, +t}:
      -EN = BE.Entry<U32, B.OrdMap<U32, Unit>>
      +t1 = G.strip_tree(t, w)
      %Equal.sym(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, T.io(U32, B.OrdMap<U32, Unit>, t1), smap(w, T.io(U32, B.OrdMap<U32, Unit>, t)), strip_io(t, w)) : {Bool.and(SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, _), Bool.and(T.bal(U32, B.OrdMap<U32, Unit>, t1), Nat.is_eq(n, SC.length(EN, _)))) == True{} : Bool}
      %Equal.sym(Bool, SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, smap(w, T.io(U32, B.OrdMap<U32, Unit>, t))), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, T.io(U32, B.OrdMap<U32, Unit>, t)), sorted_smap(w, T.io(U32, B.OrdMap<U32, Unit>, t))) : {Bool.and(_, Bool.and(T.bal(U32, B.OrdMap<U32, Unit>, t1), Nat.is_eq(n, SC.length(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, t)))))) == True{} : Bool}
      %Equal.sym(Bool, T.bal(U32, B.OrdMap<U32, Unit>, t1), T.bal(U32, B.OrdMap<U32, Unit>, t), bal_strip(t, w)) : {Bool.and(SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, T.io(U32, B.OrdMap<U32, Unit>, t)), Bool.and(_, Nat.is_eq(n, SC.length(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, t)))))) == True{} : Bool}
      %Equal.sym(Nat, SC.length(EN, smap(w, T.io(U32, B.OrdMap<U32, Unit>, t))), SC.length(EN, T.io(U32, B.OrdMap<U32, Unit>, t)), length_smap(w, T.io(U32, B.OrdMap<U32, Unit>, t))) : {Bool.and(SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, T.io(U32, B.OrdMap<U32, Unit>, t)), Bool.and(T.bal(U32, B.OrdMap<U32, Unit>, t), Nat.is_eq(n, _))) == True{} : Bool}
      g

def allinv_smap(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +a: {allinv(xs) == True{} : Bool}) -> {allinv(smap(w, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      L.and_intro(sinv(G.sdel(s, w)), allinv(smap(w, t)), sdel_inv(s, w, L.and_left(sinv(s), allinv(t), a)), allinv_smap(w, t, L.and_right(sinv(s), allinv(t), a)))

def amap_smap(+w: U32, +xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +a: {allinv(xs) == True{} : Bool}) -> {amap(smap(w, xs)) == GS.strip(w, amap(xs)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      -EM = BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, Con{BE.Entry{k, sabs(G.sdel(s, w))}, amap(smap(w, t))}, Con{BE.Entry{k, GS.sdel(w, sabs(s))}, amap(smap(w, t))}, Con{BE.Entry{k, GS.sdel(w, sabs(s))}, GS.strip(w, amap(t))},
        Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => Con{BE.Entry{k, z}, amap(smap(w, t))}, sabs(G.sdel(s, w)), GS.sdel(w, sabs(s)), sdel_abs(s, w, L.and_left(sinv(s), allinv(t), a))),
        LL.cons_cong(EM, BE.Entry{k, GS.sdel(w, sabs(s))}, amap(smap(w, t)), GS.strip(w, amap(t)), amap_smap(w, t, L.and_right(sinv(s), allinv(t), a))))

# ---- the abstract adjacency list is sorted (needed by proofs/graph/wfops) ----

def above_amap(xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +k: U32, +h: {SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, xs, k) == True{} : Bool}) -> {SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(xs), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s}, +t}:
      L.and_intro(Cmp.is_lt(U32.cmp(k, k2)), SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(t), k),
        L.and_left(Cmp.is_lt(U32.cmp(k, k2)), SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), h),
        above_amap(t, k, L.and_right(Cmp.is_lt(U32.cmp(k, k2)), SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k), h)))

def sorted_amap(xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, +h: {SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, xs) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +s}, +t}:
      L.and_intro(SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(t), k2), SO.sorted(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(t)),
        above_amap(t, k2, L.and_left(SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k2), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t), h)),
        sorted_amap(t, L.and_right(SO.above(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t, k2), SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, t), h)))

def aabs_sorted(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +h: {ainv(adj) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, aabs(adj)) == True{} : Bool}:
  match adj:
    case B.BST{+n, +t}:
      ST.inv_s(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, n, t, h)

def gadj(g: G.Graph) -> B.OrdMap<U32, B.OrdMap<U32, Unit>>:
  match g:
    case G.G{d, adj}:
      adj

def gdir(g: G.Graph) -> Bool:
  match g:
    case G.G{+d, adj}:
      d

def abs_adj_sorted(+g: G.Graph, +h: {ainv(gadj(g)) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, amap(aabs(gadj(g)))) == True{} : Bool}:
  sorted_amap(aabs(gadj(g)), aabs_sorted(gadj(g), h))
