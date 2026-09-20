import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../../spec/balanced_search_tree.bend as M
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as ME
import ../../types/graph.bend as E
import ./fmap.bend as FM

# Well-formedness of the graph model (spec/graph.bend `wf`): adjacency /
# endpoint closure, the self-loop policy and undirected symmetry.
#
# Layer 0 (this half of the file) lifts the four finite-map laws of
# proofs/graph/fmap.bend to the graph model's own vocabulary: `hasv`, `nbrs`,
# `smem`, and the effect of `put` / `del` / `strip` / `sadd` / `sdel` on them.

# ---- the two levels of map ----

def sdelM(+x: U32, m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>) -> Maybe<&2, List<&2, ME.Entry<U32, Unit>>>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      Some{GS.sdel(x, s)}

# ---- hasv / nbrs under put ----

def hasv_put_same(+v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.hasv(v, GS.put(v, s, adj)) == True{} : Bool}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z),
    GS.find(v, GS.put(v, s, adj)), Some{s},
    FM.find_ins_same(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, v, s, adj))

def hasv_put_other(+j: U32, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ne: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}) -> {GS.hasv(j, GS.put(v, s, adj)) == GS.hasv(j, adj) : Bool}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z),
    GS.find(j, GS.put(v, s, adj)), GS.find(j, adj),
    FM.find_ins_other(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, j, v, s, adj, ne))

def hasv_del_same(+v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.hasv(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)) == False{} : Bool}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z),
    GS.find(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), None{},
    FM.find_del_same(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))

def hasv_del_other(+j: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ne: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}) -> {GS.hasv(j, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)) == GS.hasv(j, adj) : Bool}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z),
    GS.find(j, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), GS.find(j, adj),
    FM.find_del_other(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, j, v, adj, ne))

def nbrs_put_same(+v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.nbrs(v, GS.put(v, s, adj)) == s : List<&2, ME.Entry<U32, Unit>>}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, List<&2, ME.Entry<U32, Unit>>, z => GS.sset(List<&2, ME.Entry<U32, Unit>>, z, Nil{}),
    GS.find(v, GS.put(v, s, adj)), Some{s},
    FM.find_ins_same(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, v, s, adj))

def nbrs_put_other(+j: U32, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ne: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}) -> {GS.nbrs(j, GS.put(v, s, adj)) == GS.nbrs(j, adj) : List<&2, ME.Entry<U32, Unit>>}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, List<&2, ME.Entry<U32, Unit>>, z => GS.sset(List<&2, ME.Entry<U32, Unit>>, z, Nil{}),
    GS.find(j, GS.put(v, s, adj)), GS.find(j, adj),
    FM.find_ins_other(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, j, v, s, adj, ne))

def nbrs_del_other(+j: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ne: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}) -> {GS.nbrs(j, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)) == GS.nbrs(j, adj) : List<&2, ME.Entry<U32, Unit>>}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, List<&2, ME.Entry<U32, Unit>>, z => GS.sset(List<&2, ME.Entry<U32, Unit>>, z, Nil{}),
    GS.find(j, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), GS.find(j, adj),
    FM.find_del_other(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, j, v, adj, ne))

# ---- membership in a neighbour set ----

def smem_sadd_same(+w: U32, +s: List<&2, ME.Entry<U32, Unit>>) -> {GS.smem(w, GS.sadd(w, s)) == True{} : Bool}:
  Equal.cong(Maybe<&2, Unit>, Bool, z => M.is_some(Unit, z),
    M.find(~U32, ~U32.cmp, Unit, w, GS.sadd(w, s)), Some{Unit{}},
    FM.find_ins_same(~U32, ~U32.cmp, ~O.u32_order, Unit, w, Unit{}, s))

def smem_sadd_other(+j: U32, +w: U32, +s: List<&2, ME.Entry<U32, Unit>>, +ne: {Cmp.is_eq(U32.cmp(j, w)) == False{} : Bool}) -> {GS.smem(j, GS.sadd(w, s)) == GS.smem(j, s) : Bool}:
  Equal.cong(Maybe<&2, Unit>, Bool, z => M.is_some(Unit, z),
    M.find(~U32, ~U32.cmp, Unit, j, GS.sadd(w, s)), M.find(~U32, ~U32.cmp, Unit, j, s),
    FM.find_ins_other(~U32, ~U32.cmp, ~O.u32_order, Unit, j, w, Unit{}, s, ne))

def smem_sdel_same(+w: U32, +s: List<&2, ME.Entry<U32, Unit>>) -> {GS.smem(w, GS.sdel(w, s)) == False{} : Bool}:
  Equal.cong(Maybe<&2, Unit>, Bool, z => M.is_some(Unit, z),
    M.find(~U32, ~U32.cmp, Unit, w, GS.sdel(w, s)), None{},
    FM.find_del_same(~U32, ~U32.cmp, Unit, w, s))

def smem_sdel_other(+j: U32, +w: U32, +s: List<&2, ME.Entry<U32, Unit>>, +ne: {Cmp.is_eq(U32.cmp(j, w)) == False{} : Bool}) -> {GS.smem(j, GS.sdel(w, s)) == GS.smem(j, s) : Bool}:
  Equal.cong(Maybe<&2, Unit>, Bool, z => M.is_some(Unit, z),
    M.find(~U32, ~U32.cmp, Unit, j, GS.sdel(w, s)), M.find(~U32, ~U32.cmp, Unit, j, s),
    FM.find_del_other(~U32, ~U32.cmp, ~O.u32_order, Unit, j, w, s, ne))

# ---- strip: remove one vertex from every neighbour set ----

def find_strip_c(+j: U32, +x: U32, +k: U32, +s: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, c: Cmp, +ec: {U32.cmp(j, k) == c : Cmp}, +ih: {GS.find(j, GS.strip(x, t)) == sdelM(x, GS.find(j, t)) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}) -> {GS.find(j, GS.strip(x, Con{ME.Entry{k, s}, t})) == sdelM(x, GS.find(j, Con{ME.Entry{k, s}, t})) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(j, k), LT{}, ec) : {M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, GS.sdel(x, s)}, GS.find(j, GS.strip(x, t))) == sdelM(x, M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, s}, GS.find(j, t))) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}
      ih
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(j, k), EQ{}, ec) : {M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, GS.sdel(x, s)}, GS.find(j, GS.strip(x, t))) == sdelM(x, M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, s}, GS.find(j, t))) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(j, k), GT{}, ec) : {M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, GS.sdel(x, s)}, GS.find(j, GS.strip(x, t))) == sdelM(x, M.find_at(U32, List<&2, ME.Entry<U32, Unit>>, _, ME.Entry{k, s}, GS.find(j, t))) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}
      ih

def find_strip(+j: U32, +x: U32, adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.find(j, GS.strip(x, adj)) == sdelM(x, GS.find(j, adj)) : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}:
  match adj:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +s}, +t}:
      find_strip_c(j, x, k, s, t, U32.cmp(j, k), {==}, find_strip(j, x, t))

def is_some_sdelM(+x: U32, m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>) -> {M.is_some(List<&2, ME.Entry<U32, Unit>>, sdelM(x, m)) == M.is_some(List<&2, ME.Entry<U32, Unit>>, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      {==}

def sset_sdelM(+x: U32, m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>) -> {GS.sset(List<&2, ME.Entry<U32, Unit>>, sdelM(x, m), Nil{}) == GS.sdel(x, GS.sset(List<&2, ME.Entry<U32, Unit>>, m, Nil{})) : List<&2, ME.Entry<U32, Unit>>}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      {==}

def hasv_strip(+j: U32, +x: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.hasv(j, GS.strip(x, adj)) == GS.hasv(j, adj) : Bool}:
  Equal.trans(Bool,
    M.is_some(List<&2, ME.Entry<U32, Unit>>, GS.find(j, GS.strip(x, adj))),
    M.is_some(List<&2, ME.Entry<U32, Unit>>, sdelM(x, GS.find(j, adj))),
    M.is_some(List<&2, ME.Entry<U32, Unit>>, GS.find(j, adj)),
    Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z),
      GS.find(j, GS.strip(x, adj)), sdelM(x, GS.find(j, adj)), find_strip(j, x, adj)),
    is_some_sdelM(x, GS.find(j, adj)))

def nbrs_strip(+j: U32, +x: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> {GS.nbrs(j, GS.strip(x, adj)) == GS.sdel(x, GS.nbrs(j, adj)) : List<&2, ME.Entry<U32, Unit>>}:
  Equal.trans(List<&2, ME.Entry<U32, Unit>>,
    GS.sset(List<&2, ME.Entry<U32, Unit>>, GS.find(j, GS.strip(x, adj)), Nil{}),
    GS.sset(List<&2, ME.Entry<U32, Unit>>, sdelM(x, GS.find(j, adj)), Nil{}),
    GS.sdel(x, GS.sset(List<&2, ME.Entry<U32, Unit>>, GS.find(j, adj), Nil{})),
    Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, List<&2, ME.Entry<U32, Unit>>, z => GS.sset(List<&2, ME.Entry<U32, Unit>>, z, Nil{}),
      GS.find(j, GS.strip(x, adj)), sdelM(x, GS.find(j, adj)), find_strip(j, x, adj)),
    sset_sdelM(x, GS.find(j, adj)))

# ---- the initial model is well formed ----

def or_r_true(x: Bool, +y: Bool, +hy: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      hy

def wf_new(+d: Bool) -> {GS.wf(GS.new(d)) == True{} : Bool}:
  L.and_intro(Bool.and(GS.closed(Nil{}, Nil{}), GS.loopfree(Nil{})), Bool.or(d, GS.symmetric(Nil{}, Nil{})),
    {==}, or_r_true(d, GS.symmetric(Nil{}, Nil{}), {==}))

# ---- the observation-only operations cannot break it ----

def wf_has_vertex(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.HasVertex{v}))) == True{} : Bool}:
  h

def wf_has_edge(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.HasEdge{u, v}))) == True{} : Bool}:
  h

def wf_neighbors(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Neighbors{v}))) == True{} : Bool}:
  h

def wf_vertices(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Vertices{}))) == True{} : Bool}:
  h

def wf_edges(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Edges{}))) == True{} : Bool}:
  h
