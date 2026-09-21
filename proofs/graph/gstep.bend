import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../spec/balanced_search_tree.bend as S2
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./ops.bend as OP
import ./edge.bend as ED
import ./nbrs.bend as NB
import ./edges.bend as EG
import ./search.bend as SE
import ./window.bend as W
import ./wfops.bend as WFO

# One public graph operation on a good shadow: the runtime state after it is
# the state of a new good shadow, and (abstract state, observation) is the
# specification's step.
#
# The fourth component is the capacity measure: the number of vertices plus
# the largest degree. An add operation raises it by at most one, a removal
# or a read never raises it, so a trace law carries a single explicit
# premise `3 + measure + adds < 2^30` (every index then stays inside U32 and
# every doubling of the vertex table or of a block stays below 2^31 words).

def mdeg(+bs: List<&2, AR.Tree<U32>>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{+b, t}:
      Nat.max(ST.bdeg(b), mdeg(t))

def mu(sh: ST.Shadow) -> Nat:
  match sh:
    case ST.Sh{dir, +lo, +hi, depth, it, +at}:
      Nat.add(Nat.sub(hi, lo), mdeg(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))

def cost(op: E.Op) -> Nat:
  match op:
    case E.AddVertex{v}:
      1n
    case E.AddEdge{u, v}:
      1n
    case _:
      0n

def StepOK(sh: ST.Shadow, op: E.Op) -> Type:
  Sigma<&1, &1, ST.Shadow, sh2 => Sigma<&1, &1, E.Obs, o => {G.step(ST.real(sh), op) == (ST.real(sh2), o) : G.Graph & E.Obs} & ({ST.good(sh2) == True{} : Bool} & ({(ST.model(sh2), o) == GS.step(ST.model(sh), op) : GS.Model & E.Obs} & {Nat.is_le(mu(sh2), Nat.add(mu(sh), cost(op))) == True{} : Bool}))>>

def mk(-sh: ST.Shadow, -op: E.Op, sh2: ST.Shadow, o: E.Obs, e1: {G.step(ST.real(sh), op) == (ST.real(sh2), o) : G.Graph & E.Obs}, e2: {ST.good(sh2) == True{} : Bool}, e3: {(ST.model(sh2), o) == GS.step(ST.model(sh), op) : GS.Model & E.Obs}, e4: {Nat.is_le(mu(sh2), Nat.add(mu(sh), cost(op))) == True{} : Bool}) -> StepOK(sh, op):
  (sh2, (o, (e1, (e2, (e3, e4)))))

def mu_same(+sh: ST.Shadow, +op: E.Op, +hc: {cost(op) == 0n : Nat}) -> {Nat.is_le(mu(sh), Nat.add(mu(sh), cost(op))) == True{} : Bool}:
  L.subst(Nat, c => {Nat.is_le(mu(sh), Nat.add(mu(sh), c)) == True{} : Bool}, 0n, cost(op), Equal.sym(Nat, cost(op), 0n, hc), N.le_add_right(mu(sh), 0n))

# The two windows have the same length in a good shadow.
def hlen_good(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(U32, ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo))) == SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))) : Nat}:
  +k = Nat.sub(hi, lo)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  Equal.trans(Nat, SC.length(U32, ST.win(U32, AR.slots(U32, it), lo, k)), k, SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)),
    ED.win_len(U32, AR.slots(U32, it), lo, k, ED.win_fits(U32, depth, it, lo, hi, OP.g_ids(dir, lo, hi, depth, it, at, h), hlo, hcap)),
    Equal.sym(Nat, SC.length(AR.Tree<U32>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)), k, ED.win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k, ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), hlo, hcap))))

# ---- the read-only operations: the shadow is unchanged ----

def so_has_vertex(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.HasVertex{v}):
  +b = S2.is_some(List<&2, BE.Entry<U32, Unit>>, S2.find(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))))
  mk(ST.Sh{dir, lo, hi, depth, it, at}, E.HasVertex{v}, ST.Sh{dir, lo, hi, depth, it, at}, E.OBool{b},
    Equal.cong(G.Graph & Bool, G.Graph & E.Obs, z => G.obs_bool(z), G.has_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), b), OP.has_vertex_ok(dir, lo, hi, depth, it, at, v, h, hlen_good(dir, lo, hi, depth, it, at, h))),
    h, {==}, mu_same(ST.Sh{dir, lo, hi, depth, it, at}, E.HasVertex{v}, {==}))

def so_has_edge(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +u: U32, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.HasEdge{u, v}):
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +r = GS.has_edge_at(GS.find(u, am), GS.find(v, am), v)
  mk(ST.Sh{dir, lo, hi, depth, it, at}, E.HasEdge{u, v}, ST.Sh{dir, lo, hi, depth, it, at}, E.OFlag{r},
    Equal.cong(G.Graph & Result<&2, &2, E.Error, Bool>, G.Graph & E.Obs, z => G.obs_flag(z), G.has_edge(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), u, v), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), r), ED.has_edge_ok(dir, lo, hi, depth, it, at, u, v, h)),
    h, {==}, mu_same(ST.Sh{dir, lo, hi, depth, it, at}, E.HasEdge{u, v}, {==}))

def so_neighbors(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.Neighbors{v}):
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +r = GS.neighbors_at(GS.find(v, am))
  mk(ST.Sh{dir, lo, hi, depth, it, at}, E.Neighbors{v}, ST.Sh{dir, lo, hi, depth, it, at}, E.ONeighbors{r},
    Equal.cong(G.Graph & Result<&2, &2, E.Error, List<&2, U32>>, G.Graph & E.Obs, z => G.obs_nbrs(z), G.neighbors(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), r), NB.neighbors_ok(dir, lo, hi, depth, it, at, v, h)),
    h, {==}, mu_same(ST.Sh{dir, lo, hi, depth, it, at}, E.Neighbors{v}, {==}))

def so_vertices(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.Vertices{}):
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +r = GS.keys(List<&2, BE.Entry<U32, Unit>>, am)
  mk(ST.Sh{dir, lo, hi, depth, it, at}, E.Vertices{}, ST.Sh{dir, lo, hi, depth, it, at}, E.OVertices{r},
    Equal.cong(G.Graph & List<&2, U32>, G.Graph & E.Obs, z => G.obs_vs(z), G.vertices(ST.real(ST.Sh{dir, lo, hi, depth, it, at})), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), r), NB.vertices_ok(dir, lo, hi, depth, it, at, h)),
    h, {==}, mu_same(ST.Sh{dir, lo, hi, depth, it, at}, E.Vertices{}, {==}))

def so_edges(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.Edges{}):
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  +r = GS.all_edges(dir, am)
  mk(ST.Sh{dir, lo, hi, depth, it, at}, E.Edges{}, ST.Sh{dir, lo, hi, depth, it, at}, E.OEdges{r},
    Equal.cong(G.Graph & List<&2, E.Edge>, G.Graph & E.Obs, z => G.obs_es(z), G.edges(ST.real(ST.Sh{dir, lo, hi, depth, it, at})), (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), r), EG.edges_ok(dir, lo, hi, depth, it, at, h)),
    h, {==}, mu_same(ST.Sh{dir, lo, hi, depth, it, at}, E.Edges{}, {==}))

# ---- Nat.max ----

def max_l_c(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_le(a, Bool.pick(Nat, c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      N.lt_le(a, b, ec)
    case False{}:
      N.le_refl(a)

def le_max_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  max_l_c(a, b, Nat.is_lt(a, b), {==})

def max_r_c(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_le(b, Bool.pick(Nat, c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      N.le_refl(b)
    case False{}:
      N.not_lt_le(a, b, ec)

def le_max_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  max_r_c(a, b, Nat.is_lt(a, b), {==})

def max_le_c(+a: Nat, +b: Nat, +x: Nat, +ha: {Nat.is_le(a, x) == True{} : Bool}, +hb: {Nat.is_le(b, x) == True{} : Bool}, c: Bool) -> {Nat.is_le(Bool.pick(Nat, c, b, a), x) == True{} : Bool}:
  match c:
    case True{}:
      hb
    case False{}:
      ha

def max_le(+a: Nat, +b: Nat, +x: Nat, +ha: {Nat.is_le(a, x) == True{} : Bool}, +hb: {Nat.is_le(b, x) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), x) == True{} : Bool}:
  max_le_c(a, b, x, ha, hb, Nat.is_lt(a, b))

# ---- the degree measure under a block update ----

def mdeg_upd_le(+bs: List<&2, AR.Tree<U32>>, +l: Nat, +b: AR.Tree<U32>, +h: {Nat.is_le(ST.bdeg(b), ST.bdeg(ED.bnth(bs, l))) == True{} : Bool}) -> {Nat.is_le(mdeg(SC.update(AR.Tree<U32>, bs, l, b)), mdeg(bs)) == True{} : Bool}:
  match bs l:
    case Nil{} l0:
      {==}
    case Con{+b0, +t} 0n:
      max_le(ST.bdeg(b), mdeg(t), Nat.max(ST.bdeg(b0), mdeg(t)), N.le_trans(ST.bdeg(b), ST.bdeg(b0), Nat.max(ST.bdeg(b0), mdeg(t)), h, le_max_l(ST.bdeg(b0), mdeg(t))), le_max_r(ST.bdeg(b0), mdeg(t)))
    case Con{+b0, +t} 1n+p:
      max_le(ST.bdeg(b0), mdeg(SC.update(AR.Tree<U32>, t, p, b)), Nat.max(ST.bdeg(b0), mdeg(t)), le_max_l(ST.bdeg(b0), mdeg(t)),
        N.le_trans(mdeg(SC.update(AR.Tree<U32>, t, p, b)), mdeg(t), Nat.max(ST.bdeg(b0), mdeg(t)), mdeg_upd_le(t, p, b, h), le_max_r(ST.bdeg(b0), mdeg(t))))

# ---- assembling the invariant ----

def good_mk(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hpi: {AR.perfect(U32, depth, it) == True{} : Bool}, +hpa: {AR.perfect(AR.Tree<U32>, depth, at) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}, +hasc: {SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo) == True{} : Bool}, +hbl: {ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))) == True{} : Bool}, +hwf: {GS.wf(ST.model(ST.Sh{dir, lo, hi, depth, it, at})) == True{} : Bool}) -> {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}:
  L.and_intro(Nat.is_le(depth, 31n), OP.t1(dir, lo, hi, depth, it, at), hd,
    L.and_intro(AR.perfect(U32, depth, it), OP.t2(dir, lo, hi, depth, it, at), hpi,
      L.and_intro(AR.perfect(AR.Tree<U32>, depth, at), OP.t3(dir, lo, hi, depth, it, at), hpa,
        L.and_intro(Nat.is_le(lo, hi), OP.t4(dir, lo, hi, depth, it, at), hlo,
          L.and_intro(Nat.is_le(hi, SC.pow2(depth)), OP.t5(dir, lo, hi, depth, it, at), hcap,
            L.and_intro(SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo), OP.t6(dir, lo, hi, depth, it, at), hasc,
              L.and_intro(ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))), GS.wf(ST.model(ST.Sh{dir, lo, hi, depth, it, at})), hbl, hwf)))))))

# The model a step reaches is well formed (the specification step preserves
# well-formedness: proofs/graph/wfops.bend).
def wf_after(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +op: E.Op, +m2: GS.Model, +o: E.Obs, +e3: {(m2, o) == GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), op) : GS.Model & E.Obs}) -> {GS.wf(m2) == True{} : Bool}:
  +am = ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))
  L.subst(GS.Model, z => {GS.wf(z) == True{} : Bool}, Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{dir, am}, op)), m2,
    Equal.sym(GS.Model, m2, Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{dir, am}, op)), Equal.cong(GS.Model & E.Obs, GS.Model, p => Pair.fst(GS.Model, E.Obs, p), (m2, o), GS.step(GS.GM{dir, am}, op), e3)),
    WFO.wf_step(dir, am, op, W.sorted_amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)), W.asc_win(Nat.sub(hi, lo), AR.slots(U32, it), lo, OP.g_asc(dir, lo, hi, depth, it, at, h))), OP.g_wf(dir, lo, hi, depth, it, at, h)))
