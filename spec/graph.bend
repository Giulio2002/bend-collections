import Base
import ./common.bend as SC
import ./balanced_search_tree.bend as M
import ../types/balanced_search_tree.bend as ME
import ../types/graph.bend as E

# Finite simple graph: a finite map from each vertex to its finite set of
# (out-)neighbours, both kept as key-sorted association lists (the ordered
# finite-map model of spec/balanced_search_tree.bend, with Unit values for
# sets). Undirected graphs store every edge in both endpoint sets. Self-loops
# are rejected; adding an existing edge changes nothing observable.

type Model is Data:
  GM{directed: Bool, adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>}

def new(directed: Bool) -> Model:
  GM{directed, Nil{}}

def find(+v: U32, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Maybe<&2, List<&2, ME.Entry<U32, Unit>>>:
  M.find(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, xs)

def put(+v: U32, s: List<&2, ME.Entry<U32, Unit>>, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  M.ins(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, s, xs)

def sadd(+w: U32, s: List<&2, ME.Entry<U32, Unit>>) -> List<&2, ME.Entry<U32, Unit>>:
  M.ins(~U32, ~U32.cmp, Unit, w, Unit{}, s)

def sdel(+w: U32, s: List<&2, ME.Entry<U32, Unit>>) -> List<&2, ME.Entry<U32, Unit>>:
  M.del(~U32, ~U32.cmp, Unit, w, s)

def smem(+w: U32, s: List<&2, ME.Entry<U32, Unit>>) -> Bool:
  M.is_some(Unit, M.find(~U32, ~U32.cmp, Unit, w, s))

def keys(-V: Data, xs: List<&2, ME.Entry<U32, V>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{ME.key(U32, V, e), keys(V, t)}

# Remove w from every neighbour set.
def strip(+w: U32, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ME.Entry{k, s}, t}:
      Con{ME.Entry{k, sdel(w, s)}, strip(w, t)}

def keep_if(b: Bool, x: E.Edge, rest: List<&2, E.Edge>) -> List<&2, E.Edge>:
  match b:
    case True{}:
      Con{x, rest}
    case False{}:
      rest

# Edges leaving u; an undirected edge is listed once, from its smaller end.
def out_edges(+directed: Bool, +u: U32, ws: List<&2, U32>) -> List<&2, E.Edge>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      keep_if(Bool.or(directed, Cmp.is_lt(U32.cmp(u, w))), E.Edge{u, w}, out_edges(directed, u, t))

def all_edges(+directed: Bool, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> List<&2, E.Edge>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ME.Entry{u, s}, t}:
      SC.append(E.Edge, out_edges(directed, u, keys(Unit, s)), all_edges(directed, t))

def same(+u: U32, +v: U32) -> Bool:
  Cmp.is_eq(U32.cmp(u, v))

def add_vertex_at(m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32) -> Model & E.Obs:
  match m:
    case None{}:
      (GM{d, put(v, Nil{}, adj)}, E.OUnit{Done{Unit{}}})
    case Some{s}:
      (GM{d, adj}, E.OUnit{Fail{E.VertexExists{}}})

def remove_vertex_at(m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32) -> Model & E.Obs:
  match m:
    case None{}:
      (GM{d, adj}, E.OUnit{Fail{E.VertexNotFound{}}})
    case Some{s}:
      (GM{d, strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))}, E.OUnit{Done{Unit{}}})

# Insert v into u's set and, when undirected, u into v's set.
def link(d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, su: List<&2, ME.Entry<U32, Unit>>, sv: List<&2, ME.Entry<U32, Unit>>) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  match d:
    case True{}:
      put(u, sadd(v, su), adj)
    case False{}:
      put(v, sadd(u, sv), put(u, sadd(v, su), adj))

def unlink(d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, su: List<&2, ME.Entry<U32, Unit>>, sv: List<&2, ME.Entry<U32, Unit>>) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  match d:
    case True{}:
      put(u, sdel(v, su), adj)
    case False{}:
      put(v, sdel(u, sv), put(u, sdel(v, su), adj))

def add_edge_at(mu: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, mv: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, loop: Bool, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> Model & E.Obs:
  match mu mv loop:
    case None{} _ _:
      (GM{d, adj}, E.OUnit{Fail{E.VertexNotFound{}}})
    case Some{su} None{} _:
      (GM{d, adj}, E.OUnit{Fail{E.VertexNotFound{}}})
    case Some{su} Some{sv} True{}:
      (GM{d, adj}, E.OUnit{Fail{E.SelfLoop{}}})
    case Some{su} Some{sv} False{}:
      (GM{d, link(d, adj, u, v, su, sv)}, E.OUnit{Done{Unit{}}})

def remove_present(present: Bool, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, su: List<&2, ME.Entry<U32, Unit>>, sv: List<&2, ME.Entry<U32, Unit>>) -> Model & E.Obs:
  match present:
    case False{}:
      (GM{d, adj}, E.OUnit{Fail{E.EdgeNotFound{}}})
    case True{}:
      (GM{d, unlink(d, adj, u, v, su, sv)}, E.OUnit{Done{Unit{}}})

def remove_edge_at(mu: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, mv: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> Model & E.Obs:
  match mu mv:
    case None{} _:
      (GM{d, adj}, E.OUnit{Fail{E.VertexNotFound{}}})
    case Some{su} None{}:
      (GM{d, adj}, E.OUnit{Fail{E.VertexNotFound{}}})
    case Some{+su} Some{sv}:
      remove_present(smem(v, su), d, adj, u, v, su, sv)

def has_edge_at(mu: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, mv: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +v: U32) -> Result<&2, &2, E.Error, Bool>:
  match mu mv:
    case None{} _:
      Fail{E.VertexNotFound{}}
    case Some{su} None{}:
      Fail{E.VertexNotFound{}}
    case Some{su} Some{sv}:
      Done{smem(v, su)}

def neighbors_at(m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>) -> Result<&2, &2, E.Error, List<&2, U32>>:
  match m:
    case None{}:
      Fail{E.VertexNotFound{}}
    case Some{s}:
      Done{keys(Unit, s)}

def step(+g: Model, op: E.Op) -> Model & E.Obs:
  match g op:
    case GM{+d, +adj} E.AddVertex{+v}:
      add_vertex_at(find(v, adj), d, adj, v)
    case GM{+d, +adj} E.RemoveVertex{+v}:
      remove_vertex_at(find(v, adj), d, adj, v)
    case GM{+d, +adj} E.AddEdge{+u, +v}:
      add_edge_at(find(u, adj), find(v, adj), same(u, v), d, adj, u, v)
    case GM{+d, +adj} E.RemoveEdge{+u, +v}:
      remove_edge_at(find(u, adj), find(v, adj), d, adj, u, v)
    case GM{+d, +adj} E.HasVertex{+v}:
      (GM{d, adj}, E.OBool{M.is_some(List<&2, ME.Entry<U32, Unit>>, find(v, adj))})
    case GM{+d, +adj} E.HasEdge{+u, +v}:
      (GM{d, adj}, E.OFlag{has_edge_at(find(u, adj), find(v, adj), v)})
    case GM{+d, +adj} E.Neighbors{+v}:
      (GM{d, adj}, E.ONeighbors{neighbors_at(find(v, adj))})
    case GM{+d, +adj} E.Vertices{}:
      (GM{d, adj}, E.OVertices{keys(List<&2, ME.Entry<U32, Unit>>, adj)})
    case GM{+d, +adj} E.Edges{}:
      (GM{d, adj}, E.OEdges{all_edges(d, adj)})

def cons_obs(o: E.Obs, r: Model & List<&2, E.Obs>) -> Model & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +g: Model) -> Model & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (g, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(Model, E.Obs, step(g, op)), run(rest, Pair.fst(Model, E.Obs, step(g, op))))

# ---- well-formedness of a model ----
#
# A model is well formed when
#   closure    every neighbour of every vertex is itself a vertex, so every
#              stored edge has both endpoints in the vertex set;
#   loop-free  no vertex is one of its own neighbours (the SelfLoop policy);
#   symmetry   an UNDIRECTED model stores every edge at both endpoints.
# `new` establishes it and every operation of `step` preserves it
# (proofs/graph/wf.bend).

def sset(-V: Data, m: Maybe<&2, V>, d: V) -> V:
  match m:
    case None{}:
      d
    case Some{s}:
      s

# the neighbour set of v (empty when v is not a vertex)
def nbrs(+v: U32, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> List<&2, ME.Entry<U32, Unit>>:
  sset(List<&2, ME.Entry<U32, Unit>>, find(v, xs), Nil{})

def hasv(+v: U32, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  M.is_some(List<&2, ME.Entry<U32, Unit>>, find(v, xs))

# every neighbour in ws is a vertex of adj
def all_vertices(ws: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{ME.Entry{+w, x}, t}:
      Bool.and(hasv(w, adj), all_vertices(t, adj))

def closed(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{u, s}, t}:
      Bool.and(all_vertices(s, adj), closed(t, adj))

def loopfree(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{+u, +s}, t}:
      Bool.and(Bool.not(smem(u, s)), loopfree(t))

# u is a neighbour of every w in ws
def sym_set(+u: U32, ws: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{ME.Entry{+w, x}, t}:
      Bool.and(smem(u, nbrs(w, adj)), sym_set(u, t, adj))

def symmetric(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{+u, +s}, t}:
      Bool.and(sym_set(u, s, adj), symmetric(t, adj))

def wf(g: Model) -> Bool:
  match g:
    case GM{+d, +adj}:
      Bool.and(Bool.and(closed(adj, adj), loopfree(adj)), Bool.or(d, symmetric(adj, adj)))
