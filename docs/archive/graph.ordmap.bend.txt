import Base
import ../spec/common.bend as SC
import ../types/graph.bend as E
import ../types/balanced_search_tree.bend as BE
import ./balanced_search_tree.bend as B

# Finite simple graph over U32 vertex ids, directed or undirected (fixed at
# construction). Representation: a red-black tree ordered map (src/
# balanced_search_tree.bend, U32 instance) from each vertex to the ordered
# set (a red-black map to Unit) of its out-neighbours; an undirected edge is
# stored in both endpoint sets. Policies: isolated vertices are allowed;
# add_vertex of an existing vertex fails with VertexExists; edge operations
# fail with VertexNotFound when an endpoint is missing; self-loops fail with
# SelfLoop; adding an existing edge succeeds and changes nothing; removing a
# missing edge fails with EdgeNotFound; remove_vertex deletes all incident
# edges. Every failure returns the state unchanged.
#
# Cost (V vertices, D = max neighbour-set size): has_vertex/add_vertex
# O(log V); add_edge/remove_edge/has_edge O(log V + log D); neighbors
# O(log V + D); vertices O(V); edges O(V + E); remove_vertex O(V log D + log V)
# because every neighbour set is visited (in-edges of directed graphs are not
# indexed separately).

type Graph is Data:
  G{directed: Bool, adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>}

def new(directed: Bool) -> Graph:
  G{directed, B.new(U32, B.OrdMap<U32, Unit>)}

def get(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32) -> Maybe<&2, B.OrdMap<U32, Unit>>:
  B.get(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v)

def put(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32, s: B.OrdMap<U32, Unit>) -> B.OrdMap<U32, B.OrdMap<U32, Unit>>:
  B.insert(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v, s)

def sadd(s: B.OrdMap<U32, Unit>, +w: U32) -> B.OrdMap<U32, Unit>:
  B.insert(~U32, ~U32.cmp, Unit, s, w, Unit{})

def sdel(s: B.OrdMap<U32, Unit>, +w: U32) -> B.OrdMap<U32, Unit>:
  Pair.fst(B.OrdMap<U32, Unit>, Result<&2, &2, BE.Error, Unit>, B.remove(~U32, ~U32.cmp, Unit, s, w))

def smem(s: B.OrdMap<U32, Unit>, +w: U32) -> Bool:
  B.contains(~U32, ~U32.cmp, Unit, s, w)

def keys(-V: Data, xs: List<&2, BE.Entry<U32, V>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{BE.key(U32, V, e), keys(V, t)}

def has_vertex(g: Graph, +v: U32) -> Bool:
  match g:
    case G{d, adj}:
      B.contains(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v)

def add_vertex_at(m: Maybe<&2, B.OrdMap<U32, Unit>>, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match m:
    case None{}:
      (G{d, put(adj, v, B.new(U32, Unit))}, Done{Unit{}})
    case Some{s}:
      (G{d, adj}, Fail{E.VertexExists{}})

def add_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match g:
    case G{+d, +adj}:
      add_vertex_at(get(adj, v), d, adj, v)

# Remove w from every neighbour set (shape-preserving tree walk).
def strip_tree(t: B.Tree<U32, B.OrdMap<U32, Unit>>, +w: U32) -> B.Tree<U32, B.OrdMap<U32, Unit>>:
  match t:
    case B.Leaf{}:
      B.Leaf{}
    case B.Node{c, l, BE.Entry{k, s}, r}:
      B.Node{c, strip_tree(l, w), BE.Entry{k, sdel(s, w)}, strip_tree(r, w)}

def strip(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +w: U32) -> B.OrdMap<U32, B.OrdMap<U32, Unit>>:
  match adj:
    case B.BST{n, t}:
      B.BST{n, strip_tree(t, w)}

def remove_vertex_at(m: Maybe<&2, B.OrdMap<U32, Unit>>, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match m:
    case None{}:
      (G{d, adj}, Fail{E.VertexNotFound{}})
    case Some{s}:
      (G{d, strip(Pair.fst(B.OrdMap<U32, B.OrdMap<U32, Unit>>, Result<&2, &2, BE.Error, B.OrdMap<U32, Unit>>, B.remove(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v)), v)}, Done{Unit{}})

def remove_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match g:
    case G{+d, +adj}:
      remove_vertex_at(get(adj, v), d, adj, v)

def link(d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, su: B.OrdMap<U32, Unit>, sv: B.OrdMap<U32, Unit>) -> B.OrdMap<U32, B.OrdMap<U32, Unit>>:
  match d:
    case True{}:
      put(adj, u, sadd(su, v))
    case False{}:
      put(put(adj, u, sadd(su, v)), v, sadd(sv, u))

def unlink(d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, su: B.OrdMap<U32, Unit>, sv: B.OrdMap<U32, Unit>) -> B.OrdMap<U32, B.OrdMap<U32, Unit>>:
  match d:
    case True{}:
      put(adj, u, sdel(su, v))
    case False{}:
      put(put(adj, u, sdel(su, v)), v, sdel(sv, u))

def add_edge_at(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, loop: Bool, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match mu mv loop:
    case None{} _ _:
      (G{d, adj}, Fail{E.VertexNotFound{}})
    case Some{su} None{} _:
      (G{d, adj}, Fail{E.VertexNotFound{}})
    case Some{su} Some{sv} True{}:
      (G{d, adj}, Fail{E.SelfLoop{}})
    case Some{su} Some{sv} False{}:
      (G{d, link(d, adj, u, v, su, sv)}, Done{Unit{}})

# Add the edge u -> v (and v -> u when undirected); idempotent.
def add_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match g:
    case G{+d, +adj}:
      add_edge_at(get(adj, u), get(adj, v), Cmp.is_eq(U32.cmp(u, v)), d, adj, u, v)

def remove_present(present: Bool, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, su: B.OrdMap<U32, Unit>, sv: B.OrdMap<U32, Unit>) -> Graph & Result<&2, &2, E.Error, Unit>:
  match present:
    case False{}:
      (G{d, adj}, Fail{E.EdgeNotFound{}})
    case True{}:
      (G{d, unlink(d, adj, u, v, su, sv)}, Done{Unit{}})

def remove_edge_at(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match mu mv:
    case None{} _:
      (G{d, adj}, Fail{E.VertexNotFound{}})
    case Some{su} None{}:
      (G{d, adj}, Fail{E.VertexNotFound{}})
    case Some{+su} Some{sv}:
      remove_present(smem(su, v), d, adj, u, v, su, sv)

def remove_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  match g:
    case G{+d, +adj}:
      remove_edge_at(get(adj, u), get(adj, v), d, adj, u, v)

def has_edge_at(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, +v: U32) -> Result<&2, &2, E.Error, Bool>:
  match mu mv:
    case None{} _:
      Fail{E.VertexNotFound{}}
    case Some{su} None{}:
      Fail{E.VertexNotFound{}}
    case Some{su} Some{sv}:
      Done{smem(su, v)}

def has_edge(g: Graph, +u: U32, +v: U32) -> Result<&2, &2, E.Error, Bool>:
  match g:
    case G{d, +adj}:
      has_edge_at(get(adj, u), get(adj, v), v)

def neighbors_at(m: Maybe<&2, B.OrdMap<U32, Unit>>) -> Result<&2, &2, E.Error, List<&2, U32>>:
  match m:
    case None{}:
      Fail{E.VertexNotFound{}}
    case Some{s}:
      Done{keys(Unit, B.to_list(U32, Unit, s))}

# Out-neighbours of v (all neighbours when undirected), ascending.
def neighbors(g: Graph, +v: U32) -> Result<&2, &2, E.Error, List<&2, U32>>:
  match g:
    case G{d, +adj}:
      neighbors_at(get(adj, v))

# Vertices, ascending.
def vertices(g: Graph) -> List<&2, U32>:
  match g:
    case G{d, adj}:
      keys(B.OrdMap<U32, Unit>, B.to_list(U32, B.OrdMap<U32, Unit>, adj))

def keep_if(b: Bool, x: E.Edge, rest: List<&2, E.Edge>) -> List<&2, E.Edge>:
  match b:
    case True{}:
      Con{x, rest}
    case False{}:
      rest

def out_edges(+directed: Bool, +u: U32, ws: List<&2, U32>) -> List<&2, E.Edge>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      keep_if(Bool.or(directed, Cmp.is_lt(U32.cmp(u, w))), E.Edge{u, w}, out_edges(directed, u, t))

def edges_go(+directed: Bool, xs: List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>) -> List<&2, E.Edge>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{BE.Entry{u, s}, t}:
      SC.append(E.Edge, out_edges(directed, u, keys(Unit, B.to_list(U32, Unit, s))), edges_go(directed, t))

# Edges in lexicographic (src, dst) order; an undirected edge appears once,
# as (smaller, larger).
def edges(g: Graph) -> List<&2, E.Edge>:
  match g:
    case G{+d, adj}:
      edges_go(d, B.to_list(U32, B.OrdMap<U32, Unit>, adj))

# ---- trace runner ----

def obs_unit(r: Graph & Result<&2, &2, E.Error, Unit>) -> Graph & E.Obs:
  (g, x) = r
  (g, E.OUnit{x})

def step(+g: Graph, op: E.Op) -> Graph & E.Obs:
  match op:
    case E.AddVertex{v}:
      obs_unit(add_vertex(g, v))
    case E.RemoveVertex{v}:
      obs_unit(remove_vertex(g, v))
    case E.AddEdge{u, v}:
      obs_unit(add_edge(g, u, v))
    case E.RemoveEdge{u, v}:
      obs_unit(remove_edge(g, u, v))
    case E.HasVertex{v}:
      (g, E.OBool{has_vertex(g, v)})
    case E.HasEdge{u, v}:
      (g, E.OFlag{has_edge(g, u, v)})
    case E.Neighbors{v}:
      (g, E.ONeighbors{neighbors(g, v)})
    case E.Vertices{}:
      (g, E.OVertices{vertices(g)})
    case E.Edges{}:
      (g, E.OEdges{edges(g)})

def record(acc: List<&2, E.Obs>, r: Graph & E.Obs) -> Graph & List<&2, E.Obs>:
  (g, o) = r
  (g, Con{o, acc})

def step_acc(op: E.Op, st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  (g, acc) = st
  record(acc, step(g, op))

def run_acc(ops: List<&2, E.Op>, st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  (g, acc) = st
  (g, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, g: Graph) -> Graph & List<&2, E.Obs>:
  finish(run_acc(ops, (g, Nil{})))
