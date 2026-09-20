import Base
import ./lib/logic.bend as L
import ../spec/graph.bend as GS
import ../src/graph.bend as G
import ../types/graph.bend as E
import ../types/balanced_search_tree.bend as ME
import ./graph/model.bend as M
import ./graph/steps.bend as ST
import ./graph/trace.bend as TR
import ./graph/wf.bend as WF
import ./graph/wfops.bend as WFO

# Graph: public proof entry point. The representation is the checked U32
# instance of the red-black tree ordered map (vertex -> ordered neighbour set).
#   abstraction  ST.abs (spec adjacency: vertex -> key-sorted neighbour list)
#   invariant    ST.inv (vertex map and every neighbour set satisfy the
#                ordered-map invariant)
# Every operation, including every error path, is proven in ST.step_ok;
# traces run from the real constructor new(directed) for both modes.
#
# proofs/graph/wf.bend additionally develops the MODEL well-formedness
# predicate spec/graph.bend `wf` (endpoint closure, the self-loop policy and
# undirected symmetry): the finite-map laws it rests on, the fact that the
# initial model satisfies it, and the fact that the five observation-only
# operations cannot break it. Preservation by AddVertex / RemoveVertex /
# AddEdge / RemoveEdge is NOT proved yet - see PROOF_STATUS.md.

def new_abs(+d: Bool) -> {ST.abs(G.new(d)) == GS.new(d) : GS.Model}:
  {==}

def new_inv(+d: Bool) -> {ST.inv(G.new(d)) == True{} : Bool}:
  {==}

def step_ok(+g: G.Graph, +op: E.Op, +h: {ST.inv(g) == True{} : Bool}) -> ST.StepOK(g, op):
  ST.step_ok(g, op, h)

def trace_new(+d: Bool, +ops: List<&2, E.Op>) -> {TR.view(G.run(ops, G.new(d))) == GS.run(ops, GS.new(d)) : GS.Model & List<&2, E.Obs>}:
  TR.trace_from(ops, G.new(d), {==})

def trace_new_inv(+d: Bool, +ops: List<&2, E.Op>) -> {ST.inv(Pair.fst(G.Graph, List<&2, E.Obs>, G.run(ops, G.new(d)))) == True{} : Bool}:
  TR.inv_from(ops, G.new(d), {==})

# ---- model well-formedness (spec/graph.bend `wf`) ----

def new_wf(+d: Bool) -> {GS.wf(GS.new(d)) == True{} : Bool}:
  WF.wf_new(d)

def has_vertex_wf(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.HasVertex{v}))) == True{} : Bool}:
  WF.wf_has_vertex(d, adj, v, h)

def has_edge_wf(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.HasEdge{u, v}))) == True{} : Bool}:
  WF.wf_has_edge(d, adj, u, v, h)

def neighbors_wf(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Neighbors{v}))) == True{} : Bool}:
  WF.wf_neighbors(d, adj, v, h)

def vertices_wf(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Vertices{}))) == True{} : Bool}:
  WF.wf_vertices(d, adj, h)

def edges_wf(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.Edges{}))) == True{} : Bool}:
  WF.wf_edges(d, adj, h)

# Every spec operation preserves model well-formedness, on the abstraction of a
# real runtime graph (the sortedness side condition of RemoveEdge is
# discharged from the runtime invariant).
def step_wf(g: G.Graph, +op: E.Op, +hinv: {ST.inv(g) == True{} : Bool}, +hwf: {GS.wf(ST.abs(g)) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(ST.abs(g), op))) == True{} : Bool}:
  match g:
    case G.G{+d, +adj}:
      WFO.wf_step(d, M.amap(M.aabs(adj)), op,
        M.sorted_amap(M.aabs(adj), M.aabs_sorted(adj,
          L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), hinv))),
        hwf)

def new_abs_wf(+d: Bool) -> {GS.wf(ST.abs(G.new(d))) == True{} : Bool}:
  WF.wf_new(d)
