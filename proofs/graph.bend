import Base
import ./lib/logic.bend as L
import ./lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/graph.bend as GS
import ../src/graph.bend as G
import ../types/graph.bend as E
import ../types/balanced_search_tree.bend as ME
import ./graph/state.bend as ST
import ./graph/ops.bend as OP
import ./graph/gstep.bend as GT
import ./graph/gtrace.bend as TR
import ./graph/wf.bend as WF
import ./graph/wfops.bend as WFO

# Graph: public proof entry point.
#
# Representation: indexed vertex slots plus adjacency blocks (src/graph.bend).
# Both tables are linear Base.Arrays, so -- as for the other array-backed
# structures -- the laws are stated about the graph BUILT from a Data mirror
# (ST.real of a shadow):
#   abstraction  ST.model (the spec adjacency list of the window [lo, hi))
#   invariant    ST.good  (perfect trees, ascending ids, well-formed
#                blocks, and spec well-formedness of the model)
# Every operation, including every error path, is proven in TR.step_ok, and
# arbitrary finite traces run from the real constructor new(directed) in both
# modes (TR.trace_new). The only premise is the capacity condition
# 3 + mu < 2^q, q <= 30 (proofs/graph/gtrace.bend).

def new_real(+d: Bool) -> {G.new(d) == ST.real(ST.empty_shadow(d)) : G.Graph}:
  ST.new_real(d)

def new_abs(+d: Bool) -> {ST.model(ST.empty_shadow(d)) == GS.new(d) : GS.Model}:
  ST.new_model(d)

def new_inv(+d: Bool) -> {ST.good(ST.empty_shadow(d)) == True{} : Bool}:
  ST.new_good(d)

def step_ok(+sh: ST.Shadow, +op: E.Op, +h: {ST.good(sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(sh)), SC.pow2(q)) == True{} : Bool}) -> GT.StepOK(sh, op):
  TR.step_ok(sh, op, h, q, hq, hroom)

def trace_new(+d: Bool, +ops: List<&2, E.Op>, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, TR.adds(ops)), SC.pow2(q)) == True{} : Bool}) -> TR.TraceNew(d, ops):
  TR.trace_new(d, ops, q, hq, room)

def trace_from(+ops: List<&2, E.Op>, +sh: ST.Shadow, +h: {ST.good(sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, Nat.add(GT.mu(sh), TR.adds(ops))), SC.pow2(q)) == True{} : Bool}) -> TR.TraceOK(ops, sh):
  TR.trace_from(ops, sh, h, q, hq, room)

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

# A good shadow's model is well formed, and every spec operation preserves
# well-formedness of it (the sortedness side condition comes from the
# ascending id window).
def good_wf(+sh: ST.Shadow, +h: {ST.good(sh) == True{} : Bool}) -> {GS.wf(ST.model(sh)) == True{} : Bool}:
  match sh:
    case ST.Sh{+dir, +lo, +hi, +depth, +it, +at}:
      OP.g_wf(dir, lo, hi, depth, it, at, h)

def step_wf(+sh: ST.Shadow, +op: E.Op, +h: {ST.good(sh) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(ST.model(sh), op))) == True{} : Bool}:
  match sh:
    case ST.Sh{+dir, +lo, +hi, +depth, +it, +at}:
      GT.wf_after(dir, lo, hi, depth, it, at, h, op, Pair.fst(GS.Model, E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op)), Pair.snd(GS.Model, E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op)),
        Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op), (Pair.fst(GS.Model, E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op)), Pair.snd(GS.Model, E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op))), L.pair_eta(GS.Model, E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op))))
