import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../../spec/balanced_search_tree.bend as M
import ../../spec/graph.bend as GS
import ../../types/balanced_search_tree.bend as ME
import ../../types/graph.bend as E
import ./fmap.bend as FM
import ./wf.bend as W
import ../balanced_search_tree/specops.bend as SP
import ../balanced_search_tree/sorted.bend as SO

# Layer 1 of the graph model well-formedness development: the three
# components of spec/graph.bend `wf` are preserved by every operation of
# `GS.step` that changes the model.
#
# Shape of every proof: the operation changes BOTH the walked entry list and
# the lookup context, so each predicate needs
#   * a "context" lemma (the walked list is fixed, the context grows), and
#   * an "ins"/"del" lemma (the context is fixed, the walked list changes).
# The two are composed at the end. `_c` helpers exist wherever Bend has to
# branch on a comparison that is not a parameter.

# ---- the keys of two distinct vertices differ ----

def ne_from_hasv_c(c: Cmp, +w: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(w, v) == c : Cmp}, +hw: {GS.hasv(w, adj) == True{} : Bool}, +hv: {GS.hasv(v, adj) == False{} : Bool}) -> {Cmp.is_eq(U32.cmp(w, v)) == False{} : Bool}:
  match c:
    case LT{}:
      FM.ne_of_lt(~U32, ~U32.cmp, w, v, ec)
    case EQ{}:
      Empty.absurd({Cmp.is_eq(U32.cmp(w, v)) == False{} : Bool},
        L.true_not_false(GS.hasv(v, adj),
          L.subst(U32, x => {GS.hasv(x, adj) == True{} : Bool}, w, v, O.antisym(~U32, ~U32.cmp, O.u32_order, w, v, ec), hw),
          hv))
    case GT{}:
      FM.ne_of_gt(~U32, ~U32.cmp, w, v, ec)

# ---- closure ----

def ne_from_hasv(+w: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hw: {GS.hasv(w, adj) == True{} : Bool}, +hv: {GS.hasv(v, adj) == False{} : Bool}) -> {Cmp.is_eq(U32.cmp(w, v)) == False{} : Bool}:
  ne_from_hasv_c(U32.cmp(w, v), w, v, adj, {==}, hw, hv)

def hasv_put_mono_c(c: Cmp, +w: U32, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(w, v) == c : Cmp}, +h: {GS.hasv(w, adj) == True{} : Bool}) -> {GS.hasv(w, GS.put(v, s, adj)) == True{} : Bool}:
  match c:
    case EQ{}:
      L.subst(U32, x => {GS.hasv(x, GS.put(v, s, adj)) == True{} : Bool}, v, w,
        Equal.sym(U32, w, v, O.antisym(~U32, ~U32.cmp, O.u32_order, w, v, ec)),
        W.hasv_put_same(v, s, adj))
    case LT{}:
      Equal.trans(Bool, GS.hasv(w, GS.put(v, s, adj)), GS.hasv(w, adj), True{},
        W.hasv_put_other(w, v, s, adj, FM.ne_of_lt(~U32, ~U32.cmp, w, v, ec)), h)
    case GT{}:
      Equal.trans(Bool, GS.hasv(w, GS.put(v, s, adj)), GS.hasv(w, adj), True{},
        W.hasv_put_other(w, v, s, adj, FM.ne_of_gt(~U32, ~U32.cmp, w, v, ec)), h)

def hasv_put_mono(+w: U32, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.hasv(w, adj) == True{} : Bool}) -> {GS.hasv(w, GS.put(v, s, adj)) == True{} : Bool}:
  hasv_put_mono_c(U32.cmp(w, v), w, v, s, adj, {==}, h)

def all_vertices_ctx_put(ws: List<&2, ME.Entry<U32, Unit>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.all_vertices(ws, adj) == True{} : Bool}) -> {GS.all_vertices(ws, GS.put(v, s, adj)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, x}, +t}:
      L.and_intro(GS.hasv(w, GS.put(v, s, adj)), GS.all_vertices(t, GS.put(v, s, adj)),
        hasv_put_mono(w, v, s, adj, L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h)),
        all_vertices_ctx_put(t, v, s, adj, L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), h)))

def closed_ctx_put(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.closed(xs, adj) == True{} : Bool}) -> {GS.closed(xs, GS.put(v, s, adj)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(GS.all_vertices(se, GS.put(v, s, adj)), GS.closed(t, GS.put(v, s, adj)),
        all_vertices_ctx_put(se, v, s, adj, L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), h)),
        closed_ctx_put(t, v, s, adj, L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), h)))

# ---- inserting one entry into the walked list ----

def closed_ins_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, k) == c : Cmp}, +hs: {GS.all_vertices(s, adj) == True{} : Bool}, +h: {GS.closed(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.closed(GS.put(v, s, t), adj) == True{} : Bool}) -> {GS.closed(GS.put(v, s, Con{ME.Entry{k, se}, t}), adj) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, Con{ME.Entry{k, se}, t}}, FM.ins_lt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.closed(_, adj) == True{} : Bool}
      L.and_intro(GS.all_vertices(s, adj), GS.closed(Con{ME.Entry{k, se}, t}, adj), hs, h)
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, t}, FM.ins_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.closed(_, adj) == True{} : Bool}
      L.and_intro(GS.all_vertices(s, adj), GS.closed(t, adj), hs, L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), h))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, GS.put(v, s, t)}, FM.ins_gt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.closed(_, adj) == True{} : Bool}
      L.and_intro(GS.all_vertices(se, adj), GS.closed(GS.put(v, s, t), adj), L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), h), ih)

def closed_ins(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hs: {GS.all_vertices(s, adj) == True{} : Bool}, +h: {GS.closed(xs, adj) == True{} : Bool}) -> {GS.closed(GS.put(v, s, xs), adj) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(GS.all_vertices(s, adj), True{}, hs, {==})
    case Con{ME.Entry{+k, +se}, +t}:
      closed_ins_c(U32.cmp(v, k), k, se, t, v, s, adj, {==}, hs, h,
        closed_ins(t, v, s, adj, hs, L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), h)))

def loopfree_ins_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +ec: {U32.cmp(v, k) == c : Cmp}, +hn: {Bool.not(GS.smem(v, s)) == True{} : Bool}, +h: {GS.loopfree(Con{ME.Entry{k, se}, t}) == True{} : Bool}, +ih: {GS.loopfree(GS.put(v, s, t)) == True{} : Bool}) -> {GS.loopfree(GS.put(v, s, Con{ME.Entry{k, se}, t})) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, Con{ME.Entry{k, se}, t}}, FM.ins_lt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.loopfree(_) == True{} : Bool}
      L.and_intro(Bool.not(GS.smem(v, s)), GS.loopfree(Con{ME.Entry{k, se}, t}), hn, h)
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, t}, FM.ins_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.loopfree(_) == True{} : Bool}
      L.and_intro(Bool.not(GS.smem(v, s)), GS.loopfree(t), hn, L.and_right(Bool.not(GS.smem(k, se)), GS.loopfree(t), h))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, GS.put(v, s, t)}, FM.ins_gt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.loopfree(_) == True{} : Bool}
      L.and_intro(Bool.not(GS.smem(k, se)), GS.loopfree(GS.put(v, s, t)), L.and_left(Bool.not(GS.smem(k, se)), GS.loopfree(t), h), ih)

def loopfree_ins(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +hn: {Bool.not(GS.smem(v, s)) == True{} : Bool}, +h: {GS.loopfree(xs) == True{} : Bool}) -> {GS.loopfree(GS.put(v, s, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(Bool.not(GS.smem(v, s)), True{}, hn, {==})
    case Con{ME.Entry{+k, +se}, +t}:
      loopfree_ins_c(U32.cmp(v, k), k, se, t, v, s, {==}, hn, h,
        loopfree_ins(t, v, s, hn, L.and_right(Bool.not(GS.smem(k, se)), GS.loopfree(t), h)))

def symmetric_ins_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, k) == c : Cmp}, +hs: {GS.sym_set(v, s, adj) == True{} : Bool}, +h: {GS.symmetric(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.symmetric(GS.put(v, s, t), adj) == True{} : Bool}) -> {GS.symmetric(GS.put(v, s, Con{ME.Entry{k, se}, t}), adj) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, Con{ME.Entry{k, se}, t}}, FM.ins_lt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.symmetric(_, adj) == True{} : Bool}
      L.and_intro(GS.sym_set(v, s, adj), GS.symmetric(Con{ME.Entry{k, se}, t}, adj), hs, h)
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{v, s}, t}, FM.ins_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.symmetric(_, adj) == True{} : Bool}
      L.and_intro(GS.sym_set(v, s, adj), GS.symmetric(t, adj), hs, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(v, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, GS.put(v, s, t)}, FM.ins_gt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, s, ec)) : {GS.symmetric(_, adj) == True{} : Bool}
      L.and_intro(GS.sym_set(k, se, adj), GS.symmetric(GS.put(v, s, t), adj), L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h), ih)

def symmetric_ins(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +s: List<&2, ME.Entry<U32, Unit>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hs: {GS.sym_set(v, s, adj) == True{} : Bool}, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.symmetric(GS.put(v, s, xs), adj) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(GS.sym_set(v, s, adj), True{}, hs, {==})
    case Con{ME.Entry{+k, +se}, +t}:
      symmetric_ins_c(U32.cmp(v, k), k, se, t, v, s, adj, {==}, hs, h,
        symmetric_ins(t, v, s, adj, hs, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

# ---- symmetry under a context that gains one isolated vertex ----

def sym_set_ctx_put_absent(+u: U32, ws: List<&2, ME.Entry<U32, Unit>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hws: {GS.all_vertices(ws, adj) == True{} : Bool}, +hv: {GS.hasv(v, adj) == False{} : Bool}, +h: {GS.sym_set(u, ws, adj) == True{} : Bool}) -> {GS.sym_set(u, ws, GS.put(v, Nil{}, adj)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, x}, +t}:
      L.and_intro(GS.smem(u, GS.nbrs(w, GS.put(v, Nil{}, adj))), GS.sym_set(u, t, GS.put(v, Nil{}, adj)),
        L.subst(List<&2, ME.Entry<U32, Unit>>, z => {GS.smem(u, z) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(v, Nil{}, adj)),
          Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(v, Nil{}, adj)), GS.nbrs(w, adj),
            W.nbrs_put_other(w, v, Nil{}, adj,
              ne_from_hasv(w, v, adj, L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), hws), hv))),
          L.and_left(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)),
        sym_set_ctx_put_absent(u, t, v, adj,
          L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), hws), hv,
          L.and_right(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)))

def symmetric_ctx_put_absent(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hcl: {GS.closed(xs, adj) == True{} : Bool}, +hv: {GS.hasv(v, adj) == False{} : Bool}, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.symmetric(xs, GS.put(v, Nil{}, adj)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(GS.sym_set(k, se, GS.put(v, Nil{}, adj)), GS.symmetric(t, GS.put(v, Nil{}, adj)),
        sym_set_ctx_put_absent(k, se, v, adj,
          L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), hcl), hv,
          L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)),
        symmetric_ctx_put_absent(t, v, adj,
          L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), hcl), hv,
          L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

# ---- assembling a well-formedness proof ----

def wf_parts(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hc: {GS.closed(adj, adj) == True{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}, +hs: {Bool.or(d, GS.symmetric(adj, adj)) == True{} : Bool}) -> {GS.wf(GS.GM{d, adj}) == True{} : Bool}:
  L.and_intro(Bool.and(GS.closed(adj, adj), GS.loopfree(adj)), Bool.or(d, GS.symmetric(adj, adj)),
    L.and_intro(GS.closed(adj, adj), GS.loopfree(adj), hc, hl), hs)

def wf_closed(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.closed(adj, adj) == True{} : Bool}:
  L.and_left(GS.closed(adj, adj), GS.loopfree(adj),
    L.and_left(Bool.and(GS.closed(adj, adj), GS.loopfree(adj)), Bool.or(d, GS.symmetric(adj, adj)), h))

def wf_loopfree(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.loopfree(adj) == True{} : Bool}:
  L.and_right(GS.closed(adj, adj), GS.loopfree(adj),
    L.and_left(Bool.and(GS.closed(adj, adj), GS.loopfree(adj)), Bool.or(d, GS.symmetric(adj, adj)), h))

def wf_sym(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {Bool.or(d, GS.symmetric(adj, adj)) == True{} : Bool}:
  L.and_right(Bool.and(GS.closed(adj, adj), GS.loopfree(adj)), Bool.or(d, GS.symmetric(adj, adj)), h)

# A directed model owes nothing about symmetry; an undirected one carries the
# old symmetry proof through `f`.
def sym_or(d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +adj2: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {Bool.or(d, GS.symmetric(adj, adj)) == True{} : Bool}, f: @+hx: {GS.symmetric(adj, adj) == True{} : Bool} -> {GS.symmetric(adj2, adj2) == True{} : Bool}) -> {Bool.or(d, GS.symmetric(adj2, adj2)) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      f(h)

# ---- AddVertex of a vertex that is not present ----

def wf_add_vertex_new(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +hv: {GS.hasv(v, adj) == False{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(GS.GM{d, GS.put(v, Nil{}, adj)}) == True{} : Bool}:
  wf_parts(d, GS.put(v, Nil{}, adj),
    closed_ins(adj, v, Nil{}, GS.put(v, Nil{}, adj), {==},
      closed_ctx_put(adj, v, Nil{}, adj, wf_closed(d, adj, h))),
    loopfree_ins(adj, v, Nil{}, {==}, wf_loopfree(d, adj, h)),
    sym_or(d, adj, GS.put(v, Nil{}, adj), wf_sym(d, adj, h),
      hx => symmetric_ins(adj, v, Nil{}, GS.put(v, Nil{}, adj), {==},
        symmetric_ctx_put_absent(adj, v, adj, wf_closed(d, adj, h), hv, hx))))

def wf_add_vertex_at(m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +hm: {GS.find(v, adj) == m : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.add_vertex_at(m, d, adj, v))) == True{} : Bool}:
  match m:
    case None{}:
      wf_add_vertex_new(d, adj, v,
        Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, z => M.is_some(List<&2, ME.Entry<U32, Unit>>, z), GS.find(v, adj), None{}, hm), h)
    case Some{+s}:
      h

def wf_add_vertex(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.AddVertex{v}))) == True{} : Bool}:
  wf_add_vertex_at(GS.find(v, adj), d, adj, v, {==}, h)

# ---- reading one entry out of a predicate that walks the list ----

def closed_at_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(u, k) == c : Cmp}, +h: {GS.closed(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.all_vertices(GS.nbrs(u, t), adj) == True{} : Bool}) -> {GS.all_vertices(GS.nbrs(u, Con{ME.Entry{k, se}, t}), adj) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), Some{se}, SP.find_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, ec)) : {GS.all_vertices(GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), h)
    case LT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_lt(~U32, ~U32.cmp, u, k, ec))) : {GS.all_vertices(GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      ih
    case GT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_gt(~U32, ~U32.cmp, u, k, ec))) : {GS.all_vertices(GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      ih

def closed_at(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.closed(xs, adj) == True{} : Bool}) -> {GS.all_vertices(GS.nbrs(u, xs), adj) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      closed_at_c(U32.cmp(u, k), k, se, t, u, adj, {==}, h,
        closed_at(t, u, adj, L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), h)))

def loopfree_at_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +ec: {U32.cmp(u, k) == c : Cmp}, +h: {GS.loopfree(Con{ME.Entry{k, se}, t}) == True{} : Bool}, +ih: {Bool.not(GS.smem(u, GS.nbrs(u, t))) == True{} : Bool}) -> {Bool.not(GS.smem(u, GS.nbrs(u, Con{ME.Entry{k, se}, t}))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), Some{se}, SP.find_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, ec)) : {Bool.not(GS.smem(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}))) == True{} : Bool}
      L.subst(U32, x => {Bool.not(GS.smem(x, se)) == True{} : Bool}, k, u,
        Equal.sym(U32, u, k, O.antisym(~U32, ~U32.cmp, O.u32_order, u, k, ec)),
        L.and_left(Bool.not(GS.smem(k, se)), GS.loopfree(t), h))
    case LT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_lt(~U32, ~U32.cmp, u, k, ec))) : {Bool.not(GS.smem(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}))) == True{} : Bool}
      ih
    case GT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_gt(~U32, ~U32.cmp, u, k, ec))) : {Bool.not(GS.smem(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}))) == True{} : Bool}
      ih

def loopfree_at(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +h: {GS.loopfree(xs) == True{} : Bool}) -> {Bool.not(GS.smem(u, GS.nbrs(u, xs))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      loopfree_at_c(U32.cmp(u, k), k, se, t, u, {==}, h,
        loopfree_at(t, u, L.and_right(Bool.not(GS.smem(k, se)), GS.loopfree(t), h)))

def symmetric_at_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(u, k) == c : Cmp}, +h: {GS.symmetric(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.sym_set(u, GS.nbrs(u, t), adj) == True{} : Bool}) -> {GS.sym_set(u, GS.nbrs(u, Con{ME.Entry{k, se}, t}), adj) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), Some{se}, SP.find_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, ec)) : {GS.sym_set(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      L.subst(U32, x => {GS.sym_set(x, se, adj) == True{} : Bool}, k, u,
        Equal.sym(U32, u, k, O.antisym(~U32, ~U32.cmp, O.u32_order, u, k, ec)),
        L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h))
    case LT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_lt(~U32, ~U32.cmp, u, k, ec))) : {GS.sym_set(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      ih
    case GT{}:
      %Equal.sym(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, GS.find(u, Con{ME.Entry{k, se}, t}), GS.find(u, t), FM.find_ne(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, u, FM.ne_of_gt(~U32, ~U32.cmp, u, k, ec))) : {GS.sym_set(u, GS.sset(List<&2, ME.Entry<U32, Unit>>, _, Nil{}), adj) == True{} : Bool}
      ih

def symmetric_at(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.sym_set(u, GS.nbrs(u, xs), adj) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      symmetric_at_c(U32.cmp(u, k), k, se, t, u, adj, {==}, h,
        symmetric_at(t, u, adj, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

# ---- adding / removing one member of a neighbour set ----

def smem_sadd_mono_c(c: Cmp, +j: U32, +y: U32, +ss: List<&2, ME.Entry<U32, Unit>>, +ec: {U32.cmp(j, y) == c : Cmp}, +h: {GS.smem(j, ss) == True{} : Bool}) -> {GS.smem(j, GS.sadd(y, ss)) == True{} : Bool}:
  match c:
    case EQ{}:
      L.subst(U32, x => {GS.smem(x, GS.sadd(y, ss)) == True{} : Bool}, y, j,
        Equal.sym(U32, j, y, O.antisym(~U32, ~U32.cmp, O.u32_order, j, y, ec)),
        W.smem_sadd_same(y, ss))
    case LT{}:
      Equal.trans(Bool, GS.smem(j, GS.sadd(y, ss)), GS.smem(j, ss), True{},
        W.smem_sadd_other(j, y, ss, FM.ne_of_lt(~U32, ~U32.cmp, j, y, ec)), h)
    case GT{}:
      Equal.trans(Bool, GS.smem(j, GS.sadd(y, ss)), GS.smem(j, ss), True{},
        W.smem_sadd_other(j, y, ss, FM.ne_of_gt(~U32, ~U32.cmp, j, y, ec)), h)

def smem_sadd_mono(+j: U32, +y: U32, +ss: List<&2, ME.Entry<U32, Unit>>, +h: {GS.smem(j, ss) == True{} : Bool}) -> {GS.smem(j, GS.sadd(y, ss)) == True{} : Bool}:
  smem_sadd_mono_c(U32.cmp(j, y), j, y, ss, {==}, h)

def all_vertices_sadd_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(y, w) == c : Cmp}, +hy: {GS.hasv(y, adj) == True{} : Bool}, +h: {GS.all_vertices(Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.all_vertices(GS.sadd(y, t), adj) == True{} : Bool}) -> {GS.all_vertices(GS.sadd(y, Con{ME.Entry{w, uu}, t}), adj) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{y, Unit{}}, Con{ME.Entry{w, uu}, t}}, FM.ins_lt(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      L.and_intro(GS.hasv(y, adj), GS.all_vertices(Con{ME.Entry{w, uu}, t}, adj), hy, h)
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{y, Unit{}}, t}, FM.ins_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      L.and_intro(GS.hasv(y, adj), GS.all_vertices(t, adj), hy, L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), h))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sadd(y, t)}, FM.ins_gt(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      L.and_intro(GS.hasv(w, adj), GS.all_vertices(GS.sadd(y, t), adj), L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h), ih)

def all_vertices_sadd(ws: List<&2, ME.Entry<U32, Unit>>, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hy: {GS.hasv(y, adj) == True{} : Bool}, +h: {GS.all_vertices(ws, adj) == True{} : Bool}) -> {GS.all_vertices(GS.sadd(y, ws), adj) == True{} : Bool}:
  match ws:
    case Nil{}:
      L.and_intro(GS.hasv(y, adj), True{}, hy, {==})
    case Con{ME.Entry{+w, +uu}, +t}:
      all_vertices_sadd_c(U32.cmp(y, w), w, uu, t, y, adj, {==}, hy, h,
        all_vertices_sadd(t, y, adj, hy, L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), h)))

def all_vertices_sdel_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(y, w) == c : Cmp}, +h: {GS.all_vertices(Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.all_vertices(GS.sdel(y, t), adj) == True{} : Bool}) -> {GS.all_vertices(GS.sdel(y, Con{ME.Entry{w, uu}, t}), adj) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(y, Con{ME.Entry{w, uu}, t}), GS.sdel(y, t), FM.del_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(y, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, LT{}, ME.Entry{w, uu}, t, y, {==}, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      L.and_intro(GS.hasv(w, adj), GS.all_vertices(GS.sdel(y, t), adj), L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h), ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(y, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, GT{}, ME.Entry{w, uu}, t, y, {==}, ec)) : {GS.all_vertices(_, adj) == True{} : Bool}
      L.and_intro(GS.hasv(w, adj), GS.all_vertices(GS.sdel(y, t), adj), L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h), ih)

def all_vertices_sdel(ws: List<&2, ME.Entry<U32, Unit>>, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.all_vertices(ws, adj) == True{} : Bool}) -> {GS.all_vertices(GS.sdel(y, ws), adj) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      all_vertices_sdel_c(U32.cmp(y, w), w, uu, t, y, adj, {==}, h,
        all_vertices_sdel(t, y, adj, L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), h)))

def sym_set_ins_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +u: U32, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(y, w) == c : Cmp}, +hy: {GS.smem(u, GS.nbrs(y, adj)) == True{} : Bool}, +h: {GS.sym_set(u, Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.sym_set(u, GS.sadd(y, t), adj) == True{} : Bool}) -> {GS.sym_set(u, GS.sadd(y, Con{ME.Entry{w, uu}, t}), adj) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{y, Unit{}}, Con{ME.Entry{w, uu}, t}}, FM.ins_lt(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.sym_set(u, _, adj) == True{} : Bool}
      L.and_intro(GS.smem(u, GS.nbrs(y, adj)), GS.sym_set(u, Con{ME.Entry{w, uu}, t}, adj), hy, h)
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{y, Unit{}}, t}, FM.ins_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.sym_set(u, _, adj) == True{} : Bool}
      L.and_intro(GS.smem(u, GS.nbrs(y, adj)), GS.sym_set(u, t, adj), hy, L.and_right(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sadd(y, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sadd(y, t)}, FM.ins_gt(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, y, Unit{}, ec)) : {GS.sym_set(u, _, adj) == True{} : Bool}
      L.and_intro(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, GS.sadd(y, t), adj), L.and_left(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h), ih)

def sym_set_ins(ws: List<&2, ME.Entry<U32, Unit>>, +u: U32, +y: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hy: {GS.smem(u, GS.nbrs(y, adj)) == True{} : Bool}, +h: {GS.sym_set(u, ws, adj) == True{} : Bool}) -> {GS.sym_set(u, GS.sadd(y, ws), adj) == True{} : Bool}:
  match ws:
    case Nil{}:
      L.and_intro(GS.smem(u, GS.nbrs(y, adj)), True{}, hy, {==})
    case Con{ME.Entry{+w, +uu}, +t}:
      sym_set_ins_c(U32.cmp(y, w), w, uu, t, u, y, adj, {==}, hy, h,
        sym_set_ins(t, u, y, adj, hy, L.and_right(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)))

# ---- the context gains one member in one neighbour set ----

def smem_nbrs_put_sadd_c(c: Cmp, +j: U32, +w: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(w, y) == c : Cmp}, +h: {GS.smem(j, GS.nbrs(w, adj)) == True{} : Bool}) -> {GS.smem(j, GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      L.subst(U32, x => {GS.smem(j, GS.nbrs(x, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}, y, w,
        Equal.sym(U32, w, y, O.antisym(~U32, ~U32.cmp, O.u32_order, w, y, ec)),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.sadd(z, GS.nbrs(y, adj)), GS.nbrs(y, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
          Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(y, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)), GS.sadd(z, GS.nbrs(y, adj)), W.nbrs_put_same(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
          smem_sadd_mono(j, z, GS.nbrs(y, adj),
            L.subst(U32, x => {GS.smem(j, GS.nbrs(x, adj)) == True{} : Bool}, w, y,
              O.antisym(~U32, ~U32.cmp, O.u32_order, w, y, ec), h))))
    case LT{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
        Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)), GS.nbrs(w, adj),
          W.nbrs_put_other(w, y, GS.sadd(z, GS.nbrs(y, adj)), adj, FM.ne_of_lt(~U32, ~U32.cmp, w, y, ec))), h)
    case GT{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
        Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)), GS.nbrs(w, adj),
          W.nbrs_put_other(w, y, GS.sadd(z, GS.nbrs(y, adj)), adj, FM.ne_of_gt(~U32, ~U32.cmp, w, y, ec))), h)

def smem_nbrs_put_sadd(+j: U32, +w: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.smem(j, GS.nbrs(w, adj)) == True{} : Bool}) -> {GS.smem(j, GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}:
  smem_nbrs_put_sadd_c(U32.cmp(w, y), j, w, y, z, adj, {==}, h)

def sym_set_ctx_put_sadd(ws: List<&2, ME.Entry<U32, Unit>>, +u: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.sym_set(u, ws, adj) == True{} : Bool}) -> {GS.sym_set(u, ws, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, uu}, +t}:
      L.and_intro(GS.smem(u, GS.nbrs(w, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj))), GS.sym_set(u, t, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
        smem_nbrs_put_sadd(u, w, y, z, adj, L.and_left(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)),
        sym_set_ctx_put_sadd(t, u, y, z, adj, L.and_right(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)))

def symmetric_ctx_put_sadd(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.symmetric(xs, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(GS.sym_set(k, se, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)), GS.symmetric(t, GS.put(y, GS.sadd(z, GS.nbrs(y, adj)), adj)),
        sym_set_ctx_put_sadd(se, k, y, z, adj, L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)),
        symmetric_ctx_put_sadd(t, y, z, adj, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

def nbrs_of_some(+u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +s: List<&2, ME.Entry<U32, Unit>>, +hf: {GS.find(u, adj) == Some{s} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}) -> {GS.nbrs(u, adj) == s : List<&2, ME.Entry<U32, Unit>>}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, List<&2, ME.Entry<U32, Unit>>, zz => GS.sset(List<&2, ME.Entry<U32, Unit>>, zz, Nil{}), GS.find(u, adj), Some{s}, hf)

def hasv_of_some(+u: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +s: List<&2, ME.Entry<U32, Unit>>, +hf: {GS.find(u, adj) == Some{s} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}) -> {GS.hasv(u, adj) == True{} : Bool}:
  Equal.cong(Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, Bool, zz => M.is_some(List<&2, ME.Entry<U32, Unit>>, zz), GS.find(u, adj), Some{s}, hf)

# ---- AddEdge ----
#
# A1 is the model after linking u -> v, A2 after also linking v -> u (the
# undirected case). Symmetry only holds at A2: after the first put alone, u
# lists v but v does not yet list u, so the symmetry proof cannot be factored
# through A1 the way closure and loop-freedom can.

def A1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  GS.put(u, GS.sadd(v, GS.nbrs(u, adj)), adj)

def A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  GS.put(v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v))

def is_eq_flipc(c: Cmp) -> {Cmp.is_eq(O.flipc(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ne_flip(+a: U32, +b: U32, +h: {Cmp.is_eq(U32.cmp(a, b)) == False{} : Bool}) -> {Cmp.is_eq(U32.cmp(b, a)) == False{} : Bool}:
  Equal.trans(Bool, Cmp.is_eq(U32.cmp(b, a)), Cmp.is_eq(U32.cmp(a, b)), False{},
    Equal.trans(Bool, Cmp.is_eq(U32.cmp(b, a)), Cmp.is_eq(O.flipc(U32.cmp(a, b))), Cmp.is_eq(U32.cmp(a, b)),
      Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), U32.cmp(b, a), O.flipc(U32.cmp(a, b)),
        O.flip(~U32, ~U32.cmp, O.u32_order, a, b)),
      is_eq_flipc(U32.cmp(a, b))),
    h)

def closed_A1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hv: {GS.hasv(v, adj) == True{} : Bool}, +hc: {GS.closed(adj, adj) == True{} : Bool}) -> {GS.closed(A1(adj, u, v), A1(adj, u, v)) == True{} : Bool}:
  closed_ins(adj, u, GS.sadd(v, GS.nbrs(u, adj)), A1(adj, u, v),
    all_vertices_sadd(GS.nbrs(u, adj), v, A1(adj, u, v),
      hasv_put_mono(v, u, GS.sadd(v, GS.nbrs(u, adj)), adj, hv),
      all_vertices_ctx_put(GS.nbrs(u, adj), u, GS.sadd(v, GS.nbrs(u, adj)), adj, closed_at(adj, u, adj, hc))),
    closed_ctx_put(adj, u, GS.sadd(v, GS.nbrs(u, adj)), adj, hc))

def loopfree_A1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}) -> {GS.loopfree(A1(adj, u, v)) == True{} : Bool}:
  loopfree_ins(adj, u, GS.sadd(v, GS.nbrs(u, adj)),
    L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(u, GS.nbrs(u, adj)), GS.smem(u, GS.sadd(v, GS.nbrs(u, adj))),
      Equal.sym(Bool, GS.smem(u, GS.sadd(v, GS.nbrs(u, adj))), GS.smem(u, GS.nbrs(u, adj)),
        W.smem_sadd_other(u, v, GS.nbrs(u, adj), hne)),
      loopfree_at(adj, u, hl)),
    hl)

def closed_A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hu: {GS.hasv(u, adj) == True{} : Bool}, +hv: {GS.hasv(v, adj) == True{} : Bool}, +hc: {GS.closed(adj, adj) == True{} : Bool}) -> {GS.closed(A2(adj, u, v), A2(adj, u, v)) == True{} : Bool}:
  closed_ins(A1(adj, u, v), v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A2(adj, u, v),
    all_vertices_sadd(GS.nbrs(v, A1(adj, u, v)), u, A2(adj, u, v),
      hasv_put_mono(u, v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v),
        hasv_put_mono(u, u, GS.sadd(v, GS.nbrs(u, adj)), adj, hu)),
      all_vertices_ctx_put(GS.nbrs(v, A1(adj, u, v)), v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v),
        closed_at(A1(adj, u, v), v, A1(adj, u, v), closed_A1(adj, u, v, hv, hc)))),
    closed_ctx_put(A1(adj, u, v), v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v), closed_A1(adj, u, v, hv, hc)))

def loopfree_A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}) -> {GS.loopfree(A2(adj, u, v)) == True{} : Bool}:
  loopfree_ins(A1(adj, u, v), v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))),
    L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(v, GS.nbrs(v, A1(adj, u, v))), GS.smem(v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v)))),
      Equal.sym(Bool, GS.smem(v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v)))), GS.smem(v, GS.nbrs(v, A1(adj, u, v))),
        W.smem_sadd_other(v, u, GS.nbrs(v, A1(adj, u, v)), ne_flip(u, v, hne))),
      loopfree_at(A1(adj, u, v), v, loopfree_A1(adj, u, v, hne, hl))),
    loopfree_A1(adj, u, v, hne, hl))

# u is already a neighbour of v in A2, and v of u, by construction.
def smem_u_nbrs_v_A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> {GS.smem(u, GS.nbrs(v, A2(adj, u, v))) == True{} : Bool}:
  L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(u, zz) == True{} : Bool}, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), GS.nbrs(v, A2(adj, u, v)),
    Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(v, A2(adj, u, v)), GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), W.nbrs_put_same(v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v))),
    W.smem_sadd_same(u, GS.nbrs(v, A1(adj, u, v))))

def smem_v_nbrs_u_A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}) -> {GS.smem(v, GS.nbrs(u, A2(adj, u, v))) == True{} : Bool}:
  L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(v, zz) == True{} : Bool}, GS.sadd(v, GS.nbrs(u, adj)), GS.nbrs(u, A2(adj, u, v)),
    Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(u, A2(adj, u, v)), GS.sadd(v, GS.nbrs(u, adj)),
      Equal.trans(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(u, A2(adj, u, v)), GS.nbrs(u, A1(adj, u, v)), GS.sadd(v, GS.nbrs(u, adj)),
        W.nbrs_put_other(u, v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A1(adj, u, v), hne),
        W.nbrs_put_same(u, GS.sadd(v, GS.nbrs(u, adj)), adj))),
    W.smem_sadd_same(v, GS.nbrs(u, adj)))

# any sym_set fact about the old context survives both puts
def sym_set_to_A2(+ws: List<&2, ME.Entry<U32, Unit>>, +j: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +h: {GS.sym_set(j, ws, adj) == True{} : Bool}) -> {GS.sym_set(j, ws, A2(adj, u, v)) == True{} : Bool}:
  sym_set_ctx_put_sadd(ws, j, v, u, A1(adj, u, v), sym_set_ctx_put_sadd(ws, j, u, v, adj, h))

def symmetric_to_A2(+xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.symmetric(xs, A2(adj, u, v)) == True{} : Bool}:
  symmetric_ctx_put_sadd(xs, v, u, A1(adj, u, v), symmetric_ctx_put_sadd(xs, u, v, adj, h))

def symmetric_A2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hsym: {GS.symmetric(adj, adj) == True{} : Bool}) -> {GS.symmetric(A2(adj, u, v), A2(adj, u, v)) == True{} : Bool}:
  symmetric_ins(A1(adj, u, v), v, GS.sadd(u, GS.nbrs(v, A1(adj, u, v))), A2(adj, u, v),
    sym_set_ins(GS.nbrs(v, A1(adj, u, v)), v, u, A2(adj, u, v),
      smem_v_nbrs_u_A2(adj, u, v, hne),
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.sym_set(v, zz, A2(adj, u, v)) == True{} : Bool}, GS.nbrs(v, adj), GS.nbrs(v, A1(adj, u, v)),
        Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(v, A1(adj, u, v)), GS.nbrs(v, adj), W.nbrs_put_other(v, u, GS.sadd(v, GS.nbrs(u, adj)), adj, ne_flip(u, v, hne))),
        sym_set_to_A2(GS.nbrs(v, adj), v, adj, u, v, symmetric_at(adj, v, adj, hsym)))),
    symmetric_ins(adj, u, GS.sadd(v, GS.nbrs(u, adj)), A2(adj, u, v),
      sym_set_ins(GS.nbrs(u, adj), u, v, A2(adj, u, v),
        smem_u_nbrs_v_A2(adj, u, v),
        sym_set_to_A2(GS.nbrs(u, adj), u, adj, u, v, symmetric_at(adj, u, adj, hsym))),
      symmetric_to_A2(adj, adj, u, v, hsym)))

def wf_link(d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +su: List<&2, ME.Entry<U32, Unit>>, +sv: List<&2, ME.Entry<U32, Unit>>, +hfu: {GS.find(u, adj) == Some{su} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hfv: {GS.find(v, adj) == Some{sv} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(GS.GM{d, GS.link(d, adj, u, v, su, sv)}) == True{} : Bool}:
  match d:
    case True{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{True{}, GS.put(u, GS.sadd(v, zz), adj)}) == True{} : Bool}, GS.nbrs(u, adj), su,
        nbrs_of_some(u, adj, su, hfu),
        wf_parts(True{}, A1(adj, u, v),
          closed_A1(adj, u, v, hasv_of_some(v, adj, sv, hfv), wf_closed(True{}, adj, h)),
          loopfree_A1(adj, u, v, hne, wf_loopfree(True{}, adj, h)),
          {==}))
    case False{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{False{}, GS.put(v, GS.sadd(u, sv), GS.put(u, GS.sadd(v, zz), adj))}) == True{} : Bool}, GS.nbrs(u, adj), su,
        nbrs_of_some(u, adj, su, hfu),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{False{}, GS.put(v, GS.sadd(u, zz), A1(adj, u, v))}) == True{} : Bool}, GS.nbrs(v, A1(adj, u, v)), sv,
          Equal.trans(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(v, A1(adj, u, v)), GS.nbrs(v, adj), sv,
            W.nbrs_put_other(v, u, GS.sadd(v, GS.nbrs(u, adj)), adj, ne_flip(u, v, hne)),
            nbrs_of_some(v, adj, sv, hfv)),
          wf_parts(False{}, A2(adj, u, v),
            closed_A2(adj, u, v, hasv_of_some(u, adj, su, hfu), hasv_of_some(v, adj, sv, hfv), wf_closed(False{}, adj, h)),
            loopfree_A2(adj, u, v, hne, wf_loopfree(False{}, adj, h)),
            symmetric_A2(adj, u, v, hne, wf_sym(False{}, adj, h)))))

def wf_add_edge_at(mu: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, mv: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, loop: Bool, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hmu: {GS.find(u, adj) == mu : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hmv: {GS.find(v, adj) == mv : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hlp: {GS.same(u, v) == loop : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.add_edge_at(mu, mv, loop, d, adj, u, v))) == True{} : Bool}:
  match mu mv loop:
    case None{} _ _:
      h
    case Some{+su} None{} _:
      h
    case Some{+su} Some{+sv} True{}:
      h
    case Some{+su} Some{+sv} False{}:
      wf_link(d, adj, u, v, su, sv, hmu, hmv, hlp, h)

def wf_add_edge(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.AddEdge{u, v}))) == True{} : Bool}:
  wf_add_edge_at(GS.find(u, adj), GS.find(v, adj), GS.same(u, v), d, adj, u, v, {==}, {==}, {==}, h)

# ---- RemoveVertex ----
#
# DV = strip(v, del(v, adj)): v's entry disappears and v is removed from every
# remaining neighbour set. Unlike an edge removal this is a MAP over the list,
# so one induction per predicate suffices.

def nbrs_DV(+w: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hwv: {Cmp.is_eq(U32.cmp(w, v)) == False{} : Bool}) -> {GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == GS.sdel(v, GS.nbrs(w, adj)) : List<&2, ME.Entry<U32, Unit>>}:
  Equal.trans(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.sdel(v, GS.nbrs(w, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.sdel(v, GS.nbrs(w, adj)),
    W.nbrs_strip(w, v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)),
    Equal.cong(List<&2, ME.Entry<U32, Unit>>, List<&2, ME.Entry<U32, Unit>>, zz => GS.sdel(v, zz), GS.nbrs(w, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), GS.nbrs(w, adj),
      W.nbrs_del_other(w, v, adj, hwv)))

def hasv_DV(+w: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hwv: {Cmp.is_eq(U32.cmp(w, v)) == False{} : Bool}) -> {GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == GS.hasv(w, adj) : Bool}:
  Equal.trans(Bool, GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.hasv(w, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), GS.hasv(w, adj),
    W.hasv_strip(w, v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)),
    W.hasv_del_other(w, v, adj, hwv))

def all_vertices_sdel_DV_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, w) == c : Cmp}, +h: {GS.all_vertices(Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.all_vertices(GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}) -> {GS.all_vertices(GS.sdel(v, Con{ME.Entry{w, uu}, t}), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), GS.sdel(v, t), FM.del_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, v, ec)) : {GS.all_vertices(_, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, LT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.all_vertices(_, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.all_vertices(GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        Equal.trans(Bool, GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.hasv(w, adj), True{},
          hasv_DV(w, v, adj, ne_flip(v, w, FM.ne_of_lt(~U32, ~U32.cmp, v, w, ec))),
          L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h)),
        ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, GT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.all_vertices(_, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.all_vertices(GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        Equal.trans(Bool, GS.hasv(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.hasv(w, adj), True{},
          hasv_DV(w, v, adj, ne_flip(v, w, FM.ne_of_gt(~U32, ~U32.cmp, v, w, ec))),
          L.and_left(GS.hasv(w, adj), GS.all_vertices(t, adj), h)),
        ih)

def all_vertices_sdel_DV(ws: List<&2, ME.Entry<U32, Unit>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.all_vertices(ws, adj) == True{} : Bool}) -> {GS.all_vertices(GS.sdel(v, ws), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      all_vertices_sdel_DV_c(U32.cmp(v, w), w, uu, t, v, adj, {==}, h,
        all_vertices_sdel_DV(t, v, adj, L.and_right(GS.hasv(w, adj), GS.all_vertices(t, adj), h)))

def sym_set_sdel_DV_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +j: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, w) == c : Cmp}, +hjv: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}, +h: {GS.sym_set(j, Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.sym_set(j, GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}) -> {GS.sym_set(j, GS.sdel(v, Con{ME.Entry{w, uu}, t}), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), GS.sdel(v, t), FM.del_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, v, ec)) : {GS.sym_set(j, _, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, LT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.sym_set(j, _, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.smem(j, GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)))), GS.sym_set(j, GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.sdel(v, GS.nbrs(w, adj)), GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
          Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.sdel(v, GS.nbrs(w, adj)),
            nbrs_DV(w, v, adj, ne_flip(v, w, FM.ne_of_lt(~U32, ~U32.cmp, v, w, ec)))),
          Equal.trans(Bool, GS.smem(j, GS.sdel(v, GS.nbrs(w, adj))), GS.smem(j, GS.nbrs(w, adj)), True{},
            W.smem_sdel_other(j, v, GS.nbrs(w, adj), hjv),
            L.and_left(GS.smem(j, GS.nbrs(w, adj)), GS.sym_set(j, t, adj), h))),
        ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, GT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.sym_set(j, _, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.smem(j, GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)))), GS.sym_set(j, GS.sdel(v, t), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.sdel(v, GS.nbrs(w, adj)), GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
          Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.sdel(v, GS.nbrs(w, adj)),
            nbrs_DV(w, v, adj, ne_flip(v, w, FM.ne_of_gt(~U32, ~U32.cmp, v, w, ec)))),
          Equal.trans(Bool, GS.smem(j, GS.sdel(v, GS.nbrs(w, adj))), GS.smem(j, GS.nbrs(w, adj)), True{},
            W.smem_sdel_other(j, v, GS.nbrs(w, adj), hjv),
            L.and_left(GS.smem(j, GS.nbrs(w, adj)), GS.sym_set(j, t, adj), h))),
        ih)

def sym_set_sdel_DV(ws: List<&2, ME.Entry<U32, Unit>>, +j: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hjv: {Cmp.is_eq(U32.cmp(j, v)) == False{} : Bool}, +h: {GS.sym_set(j, ws, adj) == True{} : Bool}) -> {GS.sym_set(j, GS.sdel(v, ws), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      sym_set_sdel_DV_c(U32.cmp(v, w), w, uu, t, j, v, adj, {==}, hjv, h,
        sym_set_sdel_DV(t, j, v, adj, hjv, L.and_right(GS.smem(j, GS.nbrs(w, adj)), GS.sym_set(j, t, adj), h)))

def closed_DV_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, k) == c : Cmp}, +h: {GS.closed(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.closed(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}) -> {GS.closed(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t})), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t), FM.del_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, ec)) : {GS.closed(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, LT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.closed(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.all_vertices(GS.sdel(v, se), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.closed(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        all_vertices_sdel_DV(se, v, adj, L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), h)), ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, GT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.closed(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.all_vertices(GS.sdel(v, se), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.closed(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        all_vertices_sdel_DV(se, v, adj, L.and_left(GS.all_vertices(se, adj), GS.closed(t, adj), h)), ih)

def closed_DV(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.closed(xs, adj) == True{} : Bool}) -> {GS.closed(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, xs)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      closed_DV_c(U32.cmp(v, k), k, se, t, v, adj, {==}, h,
        closed_DV(t, v, adj, L.and_right(GS.all_vertices(se, adj), GS.closed(t, adj), h)))

def loopfree_DV_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +ec: {U32.cmp(v, k) == c : Cmp}, +h: {GS.loopfree(Con{ME.Entry{k, se}, t}) == True{} : Bool}, +ih: {GS.loopfree(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t))) == True{} : Bool}) -> {GS.loopfree(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t), FM.del_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, ec)) : {GS.loopfree(GS.strip(v, _)) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, LT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.loopfree(GS.strip(v, _)) == True{} : Bool}
      L.and_intro(Bool.not(GS.smem(k, GS.sdel(v, se))), GS.loopfree(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t))),
        L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(k, se), GS.smem(k, GS.sdel(v, se)),
          Equal.sym(Bool, GS.smem(k, GS.sdel(v, se)), GS.smem(k, se),
            W.smem_sdel_other(k, v, se, ne_flip(v, k, FM.ne_of_lt(~U32, ~U32.cmp, v, k, ec)))),
          L.and_left(Bool.not(GS.smem(k, se)), GS.loopfree(t), h)),
        ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, GT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.loopfree(GS.strip(v, _)) == True{} : Bool}
      L.and_intro(Bool.not(GS.smem(k, GS.sdel(v, se))), GS.loopfree(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t))),
        L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(k, se), GS.smem(k, GS.sdel(v, se)),
          Equal.sym(Bool, GS.smem(k, GS.sdel(v, se)), GS.smem(k, se),
            W.smem_sdel_other(k, v, se, ne_flip(v, k, FM.ne_of_gt(~U32, ~U32.cmp, v, k, ec)))),
          L.and_left(Bool.not(GS.smem(k, se)), GS.loopfree(t), h)),
        ih)

def loopfree_DV(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.loopfree(xs) == True{} : Bool}) -> {GS.loopfree(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, xs))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      loopfree_DV_c(U32.cmp(v, k), k, se, t, v, {==}, h,
        loopfree_DV(t, v, L.and_right(Bool.not(GS.smem(k, se)), GS.loopfree(t), h)))

def symmetric_DV_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, k) == c : Cmp}, +h: {GS.symmetric(Con{ME.Entry{k, se}, t}, adj) == True{} : Bool}, +ih: {GS.symmetric(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}) -> {GS.symmetric(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t})), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t), FM.del_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, v, ec)) : {GS.symmetric(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, LT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.symmetric(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.sym_set(k, GS.sdel(v, se), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.symmetric(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        sym_set_sdel_DV(se, k, v, adj, ne_flip(v, k, FM.ne_of_lt(~U32, ~U32.cmp, v, k, ec)),
          L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)), ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)}, FM.del_ne_c(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, GT{}, ME.Entry{k, se}, t, v, {==}, ec)) : {GS.symmetric(GS.strip(v, _), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}
      L.and_intro(GS.sym_set(k, GS.sdel(v, se), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))), GS.symmetric(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, t)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))),
        sym_set_sdel_DV(se, k, v, adj, ne_flip(v, k, FM.ne_of_gt(~U32, ~U32.cmp, v, k, ec)),
          L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)), ih)

def symmetric_DV(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {GS.symmetric(GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, xs)), GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      symmetric_DV_c(U32.cmp(v, k), k, se, t, v, adj, {==}, h,
        symmetric_DV(t, v, adj, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

def wf_remove_vertex_at(m: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.remove_vertex_at(m, d, adj, v))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+s}:
      wf_parts(d, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)),
        closed_DV(adj, v, adj, wf_closed(d, adj, h)),
        loopfree_DV(adj, v, wf_loopfree(d, adj, h)),
        sym_or(d, adj, GS.strip(v, M.del(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, v, adj)), wf_sym(d, adj, h), hx => symmetric_DV(adj, v, adj, hx)))

def wf_remove_vertex(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +v: U32, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.RemoveVertex{v}))) == True{} : Bool}:
  wf_remove_vertex_at(GS.find(v, adj), d, adj, v, h)

# ---- RemoveEdge: closure and loop-freedom ----
#
# D1 unlinks u -> v, D2 also unlinks v -> u. Both only SHRINK neighbour sets,
# so closure and loop-freedom go through exactly as for AddEdge.

def D1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  GS.put(u, GS.sdel(v, GS.nbrs(u, adj)), adj)

def D2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32) -> List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>:
  GS.put(v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))), D1(adj, u, v))

def closed_D1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hc: {GS.closed(adj, adj) == True{} : Bool}) -> {GS.closed(D1(adj, u, v), D1(adj, u, v)) == True{} : Bool}:
  closed_ins(adj, u, GS.sdel(v, GS.nbrs(u, adj)), D1(adj, u, v),
    all_vertices_sdel(GS.nbrs(u, adj), v, D1(adj, u, v),
      all_vertices_ctx_put(GS.nbrs(u, adj), u, GS.sdel(v, GS.nbrs(u, adj)), adj, closed_at(adj, u, adj, hc))),
    closed_ctx_put(adj, u, GS.sdel(v, GS.nbrs(u, adj)), adj, hc))

def loopfree_D1(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}) -> {GS.loopfree(D1(adj, u, v)) == True{} : Bool}:
  loopfree_ins(adj, u, GS.sdel(v, GS.nbrs(u, adj)),
    L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(u, GS.nbrs(u, adj)), GS.smem(u, GS.sdel(v, GS.nbrs(u, adj))),
      Equal.sym(Bool, GS.smem(u, GS.sdel(v, GS.nbrs(u, adj))), GS.smem(u, GS.nbrs(u, adj)),
        W.smem_sdel_other(u, v, GS.nbrs(u, adj), hne)),
      loopfree_at(adj, u, hl)),
    hl)

def closed_D2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hc: {GS.closed(adj, adj) == True{} : Bool}) -> {GS.closed(D2(adj, u, v), D2(adj, u, v)) == True{} : Bool}:
  closed_ins(D1(adj, u, v), v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))), D2(adj, u, v),
    all_vertices_sdel(GS.nbrs(v, D1(adj, u, v)), u, D2(adj, u, v),
      all_vertices_ctx_put(GS.nbrs(v, D1(adj, u, v)), v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))), D1(adj, u, v),
        closed_at(D1(adj, u, v), v, D1(adj, u, v), closed_D1(adj, u, v, hc)))),
    closed_ctx_put(D1(adj, u, v), v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))), D1(adj, u, v), closed_D1(adj, u, v, hc)))

def loopfree_D2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}) -> {GS.loopfree(D2(adj, u, v)) == True{} : Bool}:
  loopfree_ins(D1(adj, u, v), v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))),
    L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, GS.smem(v, GS.nbrs(v, D1(adj, u, v))), GS.smem(v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v)))),
      Equal.sym(Bool, GS.smem(v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v)))), GS.smem(v, GS.nbrs(v, D1(adj, u, v))),
        W.smem_sdel_other(v, u, GS.nbrs(v, D1(adj, u, v)), ne_flip(u, v, hne))),
      loopfree_at(D1(adj, u, v), v, loopfree_D1(adj, u, v, hne, hl))),
    loopfree_D1(adj, u, v, hne, hl))

# ---- RemoveEdge: symmetry ----
#
# Symmetry is the one component that genuinely needs the adjacency list to be
# SORTED. `GS.put` inserts before the first greater key; on an unsorted list
# it could leave a second, stale entry for the same vertex behind, and that
# stale entry would still claim an edge the removal has just deleted - the
# theorem would be false, not merely unproved. The runtime invariant
# (proofs/graph/steps.bend `inv`) supplies the sortedness.

def or_l_false(+x: Bool, +yy: Bool, +hx: {x == False{} : Bool}, +h: {Bool.or(x, yy) == True{} : Bool}) -> {yy == True{} : Bool}:
  L.subst(Bool, zz => {Bool.or(zz, yy) == True{} : Bool}, x, False{}, hx, h)

def or_r_true(x: Bool, +yy: Bool, +hy: {yy == True{} : Bool}) -> {Bool.or(x, yy) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      hy

# the context loses one member of one neighbour set
def smem_nbrs_put_sdel_c(c: Cmp, +j: U32, +w: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(w, y) == c : Cmp}, +hjz: {Cmp.is_eq(U32.cmp(j, z)) == False{} : Bool}, +h: {GS.smem(j, GS.nbrs(w, adj)) == True{} : Bool}) -> {GS.smem(j, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}:
  match c:
    case EQ{}:
      L.subst(U32, x => {GS.smem(j, GS.nbrs(x, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}, y, w,
        Equal.sym(U32, w, y, O.antisym(~U32, ~U32.cmp, O.u32_order, w, y, ec)),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.sdel(z, GS.nbrs(y, adj)), GS.nbrs(y, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
          Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(y, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)), GS.sdel(z, GS.nbrs(y, adj)), W.nbrs_put_same(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
          Equal.trans(Bool, GS.smem(j, GS.sdel(z, GS.nbrs(y, adj))), GS.smem(j, GS.nbrs(y, adj)), True{},
            W.smem_sdel_other(j, z, GS.nbrs(y, adj), hjz),
            L.subst(U32, x => {GS.smem(j, GS.nbrs(x, adj)) == True{} : Bool}, w, y,
              O.antisym(~U32, ~U32.cmp, O.u32_order, w, y, ec), h))))
    case LT{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
        Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)), GS.nbrs(w, adj),
          W.nbrs_put_other(w, y, GS.sdel(z, GS.nbrs(y, adj)), adj, FM.ne_of_lt(~U32, ~U32.cmp, w, y, ec))), h)
    case GT{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
        Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)), GS.nbrs(w, adj),
          W.nbrs_put_other(w, y, GS.sdel(z, GS.nbrs(y, adj)), adj, FM.ne_of_gt(~U32, ~U32.cmp, w, y, ec))), h)

def smem_nbrs_put_sdel(+j: U32, +w: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hjz: {Cmp.is_eq(U32.cmp(j, z)) == False{} : Bool}, +h: {GS.smem(j, GS.nbrs(w, adj)) == True{} : Bool}) -> {GS.smem(j, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}:
  smem_nbrs_put_sdel_c(U32.cmp(w, y), j, w, y, z, adj, {==}, hjz, h)

def sym_set_ctx_put_sdel(ws: List<&2, ME.Entry<U32, Unit>>, +j: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hjz: {Cmp.is_eq(U32.cmp(j, z)) == False{} : Bool}, +h: {GS.sym_set(j, ws, adj) == True{} : Bool}) -> {GS.sym_set(j, ws, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, uu}, +t}:
      L.and_intro(GS.smem(j, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj))), GS.sym_set(j, t, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
        smem_nbrs_put_sdel(j, w, y, z, adj, hjz, L.and_left(GS.smem(j, GS.nbrs(w, adj)), GS.sym_set(j, t, adj), h)),
        sym_set_ctx_put_sdel(t, j, y, z, adj, hjz, L.and_right(GS.smem(j, GS.nbrs(w, adj)), GS.sym_set(j, t, adj), h)))

# ---- "no entry of xs has key y" ----

def nokey(+y: U32, xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{+k, se}, t}:
      Bool.and(Bool.not(Cmp.is_eq(U32.cmp(k, y))), nokey(y, t))

def nokey_of_above(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +h: {SO.above(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, xs, y) == True{} : Bool}) -> {nokey(y, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(Bool.not(Cmp.is_eq(U32.cmp(k, y))), nokey(y, t),
        L.not_false(Cmp.is_eq(U32.cmp(k, y)),
          FM.ne_of_gt(~U32, ~U32.cmp, k, y,
            SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, y, k,
              SO.ab_head(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y, h)))),
        nokey_of_above(t, y, SO.ab_tail(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y, h)))

def nokey_after(+k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, Con{ME.Entry{k, se}, t}) == True{} : Bool}, +hlt: {U32.cmp(y, k) == LT{} : Cmp}) -> {nokey(y, Con{ME.Entry{k, se}, t}) == True{} : Bool}:
  L.and_intro(Bool.not(Cmp.is_eq(U32.cmp(k, y))), nokey(y, t),
    L.not_false(Cmp.is_eq(U32.cmp(k, y)),
      FM.ne_of_gt(~U32, ~U32.cmp, k, y, SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, y, k, hlt))),
    nokey_of_above(t, y,
      SO.above_gt(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, t, k, y,
        SO.so_above(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, hso), hlt)))

def nokey_eq(+k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, Con{ME.Entry{k, se}, t}) == True{} : Bool}, +heq: {U32.cmp(y, k) == EQ{} : Cmp}) -> {nokey(y, t) == True{} : Bool}:
  nokey_of_above(t, y,
    L.subst(U32, x => {SO.above(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, t, x) == True{} : Bool}, k, y,
      Equal.sym(U32, y, k, O.antisym(~U32, ~U32.cmp, O.u32_order, y, k, heq)),
      SO.so_above(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, hso)))

# ---- symmetry with one key excused ----

def sym_skip(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{+k, +se}, t}:
      Bool.and(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx))

def sym_skip_upgrade(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hnk: {nokey(y, xs) == True{} : Bool}, +h: {sym_skip(xs, y, ctx) == True{} : Bool}) -> {GS.symmetric(xs, ctx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(GS.sym_set(k, se, ctx), GS.symmetric(t, ctx),
        or_l_false(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx),
          L.not_true(Cmp.is_eq(U32.cmp(k, y)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(k, y))), nokey(y, t), hnk)),
          L.and_left(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx), h)),
        sym_skip_upgrade(t, y, ctx,
          L.and_right(Bool.not(Cmp.is_eq(U32.cmp(k, y))), nokey(y, t), hnk),
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx), h)))

def sym_skip2(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y1: U32, +y2: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{ME.Entry{+k, +se}, t}:
      Bool.and(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx))

def sym_skip2_to_skip(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y1: U32, +y2: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hnk: {nokey(y1, xs) == True{} : Bool}, +h: {sym_skip2(xs, y1, y2, ctx) == True{} : Bool}) -> {sym_skip(xs, y2, ctx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx)), sym_skip(t, y2, ctx),
        or_l_false(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx)),
          L.not_true(Cmp.is_eq(U32.cmp(k, y1)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(k, y1))), nokey(y1, t), hnk)),
          L.and_left(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx), h)),
        sym_skip2_to_skip(t, y1, y2, ctx,
          L.and_right(Bool.not(Cmp.is_eq(U32.cmp(k, y1))), nokey(y1, t), hnk),
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx), h)))

def skip2_head_c2(c2: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec2: {U32.cmp(k, v) == c2 : Cmp}, +hku: {Cmp.is_eq(U32.cmp(k, u)) == False{} : Bool}, +h: {GS.sym_set(k, se, adj) == True{} : Bool}) -> {Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v))) == True{} : Bool}:
  match c2:
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, v), EQ{}, ec2) : {Bool.or(Cmp.is_eq(_), GS.sym_set(k, se, D2(adj, u, v))) == True{} : Bool}
      {==}
    case LT{}:
      or_r_true(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)),
        sym_set_ctx_put_sdel(se, k, v, u, D1(adj, u, v), hku,
          sym_set_ctx_put_sdel(se, k, u, v, adj, FM.ne_of_lt(~U32, ~U32.cmp, k, v, ec2), h)))
    case GT{}:
      or_r_true(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)),
        sym_set_ctx_put_sdel(se, k, v, u, D1(adj, u, v), hku,
          sym_set_ctx_put_sdel(se, k, u, v, adj, FM.ne_of_gt(~U32, ~U32.cmp, k, v, ec2), h)))

def skip2_head(c1: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec1: {U32.cmp(k, u) == c1 : Cmp}, +h: {GS.sym_set(k, se, adj) == True{} : Bool}) -> {Bool.or(Cmp.is_eq(U32.cmp(k, u)), Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)))) == True{} : Bool}:
  match c1:
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(k, u), EQ{}, ec1) : {Bool.or(Cmp.is_eq(_), Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)))) == True{} : Bool}
      {==}
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(k, u), LT{}, ec1) : {Bool.or(Cmp.is_eq(_), Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)))) == True{} : Bool}
      skip2_head_c2(U32.cmp(k, v), k, se, u, v, adj, {==}, FM.ne_of_lt(~U32, ~U32.cmp, k, u, ec1), h)
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(k, u), GT{}, ec1) : {Bool.or(Cmp.is_eq(_), Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)))) == True{} : Bool}
      skip2_head_c2(U32.cmp(k, v), k, se, u, v, adj, {==}, FM.ne_of_gt(~U32, ~U32.cmp, k, u, ec1), h)

def sym_skip2_build(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +h: {GS.symmetric(xs, adj) == True{} : Bool}) -> {sym_skip2(xs, u, v, D2(adj, u, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{ME.Entry{+k, +se}, +t}:
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(k, u)), Bool.or(Cmp.is_eq(U32.cmp(k, v)), GS.sym_set(k, se, D2(adj, u, v)))), sym_skip2(t, u, v, D2(adj, u, v)),
        skip2_head(U32.cmp(k, u), k, se, u, v, adj, {==}, L.and_left(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)),
        sym_skip2_build(t, u, v, adj, L.and_right(GS.sym_set(k, se, adj), GS.symmetric(t, adj), h)))

# ---- inserting into a SORTED list, with one key excused ----

def symmetric_ins_skip_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +s: List<&2, ME.Entry<U32, Unit>>, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(y, k) == c : Cmp}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, Con{ME.Entry{k, se}, t}) == True{} : Bool}, +hs: {GS.sym_set(y, s, ctx) == True{} : Bool}, +h: {sym_skip(Con{ME.Entry{k, se}, t}, y, ctx) == True{} : Bool}, +ih: {GS.symmetric(GS.put(y, s, t), ctx) == True{} : Bool}) -> {GS.symmetric(GS.put(y, s, Con{ME.Entry{k, se}, t}), ctx) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{y, s}, Con{ME.Entry{k, se}, t}}, FM.ins_lt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y, s, ec)) : {GS.symmetric(_, ctx) == True{} : Bool}
      L.and_intro(GS.sym_set(y, s, ctx), GS.symmetric(Con{ME.Entry{k, se}, t}, ctx), hs,
        sym_skip_upgrade(Con{ME.Entry{k, se}, t}, y, ctx, nokey_after(k, se, t, y, hso, ec), h))
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{y, s}, t}, FM.ins_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y, s, ec)) : {GS.symmetric(_, ctx) == True{} : Bool}
      L.and_intro(GS.sym_set(y, s, ctx), GS.symmetric(t, ctx), hs,
        sym_skip_upgrade(t, y, ctx, nokey_eq(k, se, t, y, hso, ec),
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx), h)))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, GS.put(y, s, t)}, FM.ins_gt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y, s, ec)) : {GS.symmetric(_, ctx) == True{} : Bool}
      L.and_intro(GS.sym_set(k, se, ctx), GS.symmetric(GS.put(y, s, t), ctx),
        or_l_false(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx),
          L.not_true(Cmp.is_eq(U32.cmp(k, y)),
            L.not_false(Cmp.is_eq(U32.cmp(k, y)),
              FM.ne_of_lt(~U32, ~U32.cmp, k, y, SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, y, k, ec)))),
          L.and_left(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx), h)),
        ih)

def symmetric_ins_skip(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y: U32, +s: List<&2, ME.Entry<U32, Unit>>, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, xs) == True{} : Bool}, +hs: {GS.sym_set(y, s, ctx) == True{} : Bool}, +h: {sym_skip(xs, y, ctx) == True{} : Bool}) -> {GS.symmetric(GS.put(y, s, xs), ctx) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(GS.sym_set(y, s, ctx), True{}, hs, {==})
    case Con{ME.Entry{+k, +se}, +t}:
      symmetric_ins_skip_c(U32.cmp(y, k), k, se, t, y, s, ctx, {==}, hso, hs, h,
        symmetric_ins_skip(t, y, s, ctx, SO.so_tail(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, hso), hs,
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y)), GS.sym_set(k, se, ctx)), sym_skip(t, y, ctx), h)))

def sym_skip2_ins_c(c: Cmp, +k: U32, +se: List<&2, ME.Entry<U32, Unit>>, +t: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y1: U32, +s: List<&2, ME.Entry<U32, Unit>>, +y2: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(y1, k) == c : Cmp}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, Con{ME.Entry{k, se}, t}) == True{} : Bool}, +hs: {GS.sym_set(y1, s, ctx) == True{} : Bool}, +h: {sym_skip2(Con{ME.Entry{k, se}, t}, y1, y2, ctx) == True{} : Bool}, +ih: {sym_skip(GS.put(y1, s, t), y2, ctx) == True{} : Bool}) -> {sym_skip(GS.put(y1, s, Con{ME.Entry{k, se}, t}), y2, ctx) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y1, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{y1, s}, Con{ME.Entry{k, se}, t}}, FM.ins_lt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y1, s, ec)) : {sym_skip(_, y2, ctx) == True{} : Bool}
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx)), sym_skip(Con{ME.Entry{k, se}, t}, y2, ctx),
        or_r_true(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx), hs),
        sym_skip2_to_skip(Con{ME.Entry{k, se}, t}, y1, y2, ctx, nokey_after(k, se, t, y1, hso, ec), h))
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y1, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{y1, s}, t}, FM.ins_eq(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y1, s, ec)) : {sym_skip(_, y2, ctx) == True{} : Bool}
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx)), sym_skip(t, y2, ctx),
        or_r_true(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx), hs),
        sym_skip2_to_skip(t, y1, y2, ctx, nokey_eq(k, se, t, y1, hso, ec),
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx), h)))
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, GS.put(y1, s, Con{ME.Entry{k, se}, t}), Con{ME.Entry{k, se}, GS.put(y1, s, t)}, FM.ins_gt(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, y1, s, ec)) : {sym_skip(_, y2, ctx) == True{} : Bool}
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx)), sym_skip(GS.put(y1, s, t), y2, ctx),
        or_l_false(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx)),
          L.not_true(Cmp.is_eq(U32.cmp(k, y1)),
            L.not_false(Cmp.is_eq(U32.cmp(k, y1)),
              FM.ne_of_lt(~U32, ~U32.cmp, k, y1, SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, y1, k, ec)))),
          L.and_left(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx), h)),
        ih)

def sym_skip2_ins(xs: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +y1: U32, +s: List<&2, ME.Entry<U32, Unit>>, +y2: U32, +ctx: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, xs) == True{} : Bool}, +hs: {GS.sym_set(y1, s, ctx) == True{} : Bool}, +h: {sym_skip2(xs, y1, y2, ctx) == True{} : Bool}) -> {sym_skip(GS.put(y1, s, xs), y2, ctx) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(Bool.or(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx)), True{},
        or_r_true(Cmp.is_eq(U32.cmp(y1, y2)), GS.sym_set(y1, s, ctx), hs), {==})
    case Con{ME.Entry{+k, +se}, +t}:
      sym_skip2_ins_c(U32.cmp(y1, k), k, se, t, y1, s, y2, ctx, {==}, hso, hs, h,
        sym_skip2_ins(t, y1, s, y2, ctx, SO.so_tail(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, ME.Entry{k, se}, t, hso), hs,
          L.and_right(Bool.or(Cmp.is_eq(U32.cmp(k, y1)), Bool.or(Cmp.is_eq(U32.cmp(k, y2)), GS.sym_set(k, se, ctx))), sym_skip2(t, y1, y2, ctx), h)))

def smem_nbrs_put_sdel_ne(+j: U32, +w: U32, +y: U32, +z: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hwy: {Cmp.is_eq(U32.cmp(w, y)) == False{} : Bool}, +h: {GS.smem(j, GS.nbrs(w, adj)) == True{} : Bool}) -> {GS.smem(j, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj))) == True{} : Bool}:
  L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(j, zz) == True{} : Bool}, GS.nbrs(w, adj), GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)),
    Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(w, GS.put(y, GS.sdel(z, GS.nbrs(y, adj)), adj)), GS.nbrs(w, adj), W.nbrs_put_other(w, y, GS.sdel(z, GS.nbrs(y, adj)), adj, hwy)), h)

# ---- "j is not one of the members of ws" ----

def nokey_set(+j: U32, ws: List<&2, ME.Entry<U32, Unit>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{ME.Entry{+w, uu}, t}:
      Bool.and(Bool.not(Cmp.is_eq(U32.cmp(w, j))), nokey_set(j, t))

def smem_cons_c(c: Cmp, +j: U32, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +ec: {U32.cmp(j, w) == c : Cmp}, +ne: {Cmp.is_eq(c) == False{} : Bool}) -> {GS.smem(j, Con{ME.Entry{w, uu}, t}) == GS.smem(j, t) : Bool}:
  match c:
    case EQ{}:
      Empty.absurd({GS.smem(j, Con{ME.Entry{w, uu}, t}) == GS.smem(j, t) : Bool}, L.true_false(ne))
    case LT{}:
      Equal.cong(Maybe<&2, Unit>, Bool, zz => M.is_some(Unit, zz),
        M.find(~U32, ~U32.cmp, Unit, j, Con{ME.Entry{w, uu}, t}), M.find(~U32, ~U32.cmp, Unit, j, t),
        FM.find_ne(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, j, FM.ne_of_lt(~U32, ~U32.cmp, j, w, ec)))
    case GT{}:
      Equal.cong(Maybe<&2, Unit>, Bool, zz => M.is_some(Unit, zz),
        M.find(~U32, ~U32.cmp, Unit, j, Con{ME.Entry{w, uu}, t}), M.find(~U32, ~U32.cmp, Unit, j, t),
        FM.find_ne(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, j, FM.ne_of_gt(~U32, ~U32.cmp, j, w, ec)))

def head_ne(c: Cmp, +j: U32, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +ec: {U32.cmp(j, w) == c : Cmp}, +h: {GS.smem(j, Con{ME.Entry{w, uu}, t}) == False{} : Bool}) -> {Bool.not(Cmp.is_eq(U32.cmp(w, j))) == True{} : Bool}:
  match c:
    case EQ{}:
      Empty.absurd({Bool.not(Cmp.is_eq(U32.cmp(w, j))) == True{} : Bool},
        L.true_not_false(GS.smem(j, Con{ME.Entry{w, uu}, t}),
          Equal.cong(Maybe<&2, Unit>, Bool, zz => M.is_some(Unit, zz),
            M.find(~U32, ~U32.cmp, Unit, j, Con{ME.Entry{w, uu}, t}), Some{uu},
            SP.find_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, j, ec)),
          h))
    case LT{}:
      L.not_false(Cmp.is_eq(U32.cmp(w, j)), FM.ne_of_gt(~U32, ~U32.cmp, w, j, SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, j, w, ec)))
    case GT{}:
      L.not_false(Cmp.is_eq(U32.cmp(w, j)), FM.ne_of_lt(~U32, ~U32.cmp, w, j, SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, j, w, ec)))

def tail_absent(c: Cmp, +j: U32, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +ec: {U32.cmp(j, w) == c : Cmp}, +h: {GS.smem(j, Con{ME.Entry{w, uu}, t}) == False{} : Bool}) -> {GS.smem(j, t) == False{} : Bool}:
  match c:
    case EQ{}:
      Empty.absurd({GS.smem(j, t) == False{} : Bool},
        L.true_not_false(GS.smem(j, Con{ME.Entry{w, uu}, t}),
          Equal.cong(Maybe<&2, Unit>, Bool, zz => M.is_some(Unit, zz),
            M.find(~U32, ~U32.cmp, Unit, j, Con{ME.Entry{w, uu}, t}), Some{uu},
            SP.find_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, j, ec)),
          h))
    case LT{}:
      Equal.trans(Bool, GS.smem(j, t), GS.smem(j, Con{ME.Entry{w, uu}, t}), False{},
        Equal.sym(Bool, GS.smem(j, Con{ME.Entry{w, uu}, t}), GS.smem(j, t), smem_cons_c(LT{}, j, w, uu, t, ec, {==})), h)
    case GT{}:
      Equal.trans(Bool, GS.smem(j, t), GS.smem(j, Con{ME.Entry{w, uu}, t}), False{},
        Equal.sym(Bool, GS.smem(j, Con{ME.Entry{w, uu}, t}), GS.smem(j, t), smem_cons_c(GT{}, j, w, uu, t, ec, {==})), h)

def nokey_set_of_absent(ws: List<&2, ME.Entry<U32, Unit>>, +j: U32, +h: {GS.smem(j, ws) == False{} : Bool}) -> {nokey_set(j, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      L.and_intro(Bool.not(Cmp.is_eq(U32.cmp(w, j))), nokey_set(j, t),
        head_ne(U32.cmp(j, w), j, w, uu, t, {==}, h),
        nokey_set_of_absent(t, j, tail_absent(U32.cmp(j, w), j, w, uu, t, {==}, h)))

# the two rewritten entries are still symmetric in the new model
def sym_set_D2_at_u_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(v, w) == c : Cmp}, +hnk: {nokey_set(u, Con{ME.Entry{w, uu}, t}) == True{} : Bool}, +h: {GS.sym_set(u, Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.sym_set(u, GS.sdel(v, t), D2(adj, u, v)) == True{} : Bool}) -> {GS.sym_set(u, GS.sdel(v, Con{ME.Entry{w, uu}, t}), D2(adj, u, v)) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), GS.sdel(v, t), FM.del_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, v, ec)) : {GS.sym_set(u, _, D2(adj, u, v)) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, LT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.sym_set(u, _, D2(adj, u, v)) == True{} : Bool}
      L.and_intro(GS.smem(u, GS.nbrs(w, D2(adj, u, v))), GS.sym_set(u, GS.sdel(v, t), D2(adj, u, v)),
        smem_nbrs_put_sdel_ne(u, w, v, u, D1(adj, u, v), ne_flip(v, w, FM.ne_of_lt(~U32, ~U32.cmp, v, w, ec)),
          smem_nbrs_put_sdel_ne(u, w, u, v, adj, L.not_true(Cmp.is_eq(U32.cmp(w, u)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(w, u))), nokey_set(u, t), hnk)),
            L.and_left(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h))),
        ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(v, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(v, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, GT{}, ME.Entry{w, uu}, t, v, {==}, ec)) : {GS.sym_set(u, _, D2(adj, u, v)) == True{} : Bool}
      L.and_intro(GS.smem(u, GS.nbrs(w, D2(adj, u, v))), GS.sym_set(u, GS.sdel(v, t), D2(adj, u, v)),
        smem_nbrs_put_sdel_ne(u, w, v, u, D1(adj, u, v), ne_flip(v, w, FM.ne_of_gt(~U32, ~U32.cmp, v, w, ec)),
          smem_nbrs_put_sdel_ne(u, w, u, v, adj, L.not_true(Cmp.is_eq(U32.cmp(w, u)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(w, u))), nokey_set(u, t), hnk)),
            L.and_left(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h))),
        ih)

def sym_set_D2_at_u(ws: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hnk: {nokey_set(u, ws) == True{} : Bool}, +h: {GS.sym_set(u, ws, adj) == True{} : Bool}) -> {GS.sym_set(u, GS.sdel(v, ws), D2(adj, u, v)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      sym_set_D2_at_u_c(U32.cmp(v, w), w, uu, t, u, v, adj, {==}, hnk, h,
        sym_set_D2_at_u(t, u, v, adj,
          L.and_right(Bool.not(Cmp.is_eq(U32.cmp(w, u))), nokey_set(u, t), hnk),
          L.and_right(GS.smem(u, GS.nbrs(w, adj)), GS.sym_set(u, t, adj), h)))

def sym_set_D2_at_v_c(c: Cmp, +w: U32, +uu: Unit, +t: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(u, w) == c : Cmp}, +hnk: {nokey_set(v, Con{ME.Entry{w, uu}, t}) == True{} : Bool}, +h: {GS.sym_set(v, Con{ME.Entry{w, uu}, t}, adj) == True{} : Bool}, +ih: {GS.sym_set(v, GS.sdel(u, t), D2(adj, u, v)) == True{} : Bool}) -> {GS.sym_set(v, GS.sdel(u, Con{ME.Entry{w, uu}, t}), D2(adj, u, v)) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(u, Con{ME.Entry{w, uu}, t}), GS.sdel(u, t), FM.del_eq(~U32, ~U32.cmp, Unit, ME.Entry{w, uu}, t, u, ec)) : {GS.sym_set(v, _, D2(adj, u, v)) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(u, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(u, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, LT{}, ME.Entry{w, uu}, t, u, {==}, ec)) : {GS.sym_set(v, _, D2(adj, u, v)) == True{} : Bool}
      L.and_intro(GS.smem(v, GS.nbrs(w, D2(adj, u, v))), GS.sym_set(v, GS.sdel(u, t), D2(adj, u, v)),
        smem_nbrs_put_sdel_ne(v, w, v, u, D1(adj, u, v), L.not_true(Cmp.is_eq(U32.cmp(w, v)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(w, v))), nokey_set(v, t), hnk)),
          smem_nbrs_put_sdel_ne(v, w, u, v, adj, ne_flip(u, w, FM.ne_of_lt(~U32, ~U32.cmp, u, w, ec)),
            L.and_left(GS.smem(v, GS.nbrs(w, adj)), GS.sym_set(v, t, adj), h))),
        ih)
    case GT{}:
      %Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.sdel(u, Con{ME.Entry{w, uu}, t}), Con{ME.Entry{w, uu}, GS.sdel(u, t)}, FM.del_ne_c(~U32, ~U32.cmp, Unit, GT{}, ME.Entry{w, uu}, t, u, {==}, ec)) : {GS.sym_set(v, _, D2(adj, u, v)) == True{} : Bool}
      L.and_intro(GS.smem(v, GS.nbrs(w, D2(adj, u, v))), GS.sym_set(v, GS.sdel(u, t), D2(adj, u, v)),
        smem_nbrs_put_sdel_ne(v, w, v, u, D1(adj, u, v), L.not_true(Cmp.is_eq(U32.cmp(w, v)), L.and_left(Bool.not(Cmp.is_eq(U32.cmp(w, v))), nokey_set(v, t), hnk)),
          smem_nbrs_put_sdel_ne(v, w, u, v, adj, ne_flip(u, w, FM.ne_of_gt(~U32, ~U32.cmp, u, w, ec)),
            L.and_left(GS.smem(v, GS.nbrs(w, adj)), GS.sym_set(v, t, adj), h))),
        ih)

def sym_set_D2_at_v(ws: List<&2, ME.Entry<U32, Unit>>, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +hnk: {nokey_set(v, ws) == True{} : Bool}, +h: {GS.sym_set(v, ws, adj) == True{} : Bool}) -> {GS.sym_set(v, GS.sdel(u, ws), D2(adj, u, v)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{ME.Entry{+w, +uu}, +t}:
      sym_set_D2_at_v_c(U32.cmp(u, w), w, uu, t, u, v, adj, {==}, hnk, h,
        sym_set_D2_at_v(t, u, v, adj,
          L.and_right(Bool.not(Cmp.is_eq(U32.cmp(w, v))), nokey_set(v, t), hnk),
          L.and_right(GS.smem(v, GS.nbrs(w, adj)), GS.sym_set(v, t, adj), h)))

def symmetric_D2(+adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}, +hsym: {GS.symmetric(adj, adj) == True{} : Bool}) -> {GS.symmetric(D2(adj, u, v), D2(adj, u, v)) == True{} : Bool}:
  symmetric_ins_skip(D1(adj, u, v), v, GS.sdel(u, GS.nbrs(v, D1(adj, u, v))), D2(adj, u, v),
    SP.sorted_ins(~U32, ~U32.cmp, ~O.u32_order, List<&2, ME.Entry<U32, Unit>>, adj, u, GS.sdel(v, GS.nbrs(u, adj)), hso),
    L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.sym_set(v, GS.sdel(u, zz), D2(adj, u, v)) == True{} : Bool}, GS.nbrs(v, adj), GS.nbrs(v, D1(adj, u, v)),
      Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(v, D1(adj, u, v)), GS.nbrs(v, adj), W.nbrs_put_other(v, u, GS.sdel(v, GS.nbrs(u, adj)), adj, ne_flip(u, v, hne))),
      sym_set_D2_at_v(GS.nbrs(v, adj), u, v, adj,
        nokey_set_of_absent(GS.nbrs(v, adj), v, L.not_true(GS.smem(v, GS.nbrs(v, adj)), loopfree_at(adj, v, hl))),
        symmetric_at(adj, v, adj, hsym))),
    sym_skip2_ins(adj, u, GS.sdel(v, GS.nbrs(u, adj)), v, D2(adj, u, v), hso,
      sym_set_D2_at_u(GS.nbrs(u, adj), u, v, adj,
        nokey_set_of_absent(GS.nbrs(u, adj), u, L.not_true(GS.smem(u, GS.nbrs(u, adj)), loopfree_at(adj, u, hl))),
        symmetric_at(adj, u, adj, hsym)),
      sym_skip2_build(adj, u, v, adj, hsym)))

def ne_of_edge_c(c: Cmp, +u: U32, +v: U32, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +ec: {U32.cmp(u, v) == c : Cmp}, +hp: {GS.smem(v, GS.nbrs(u, adj)) == True{} : Bool}, +hl: {GS.loopfree(adj) == True{} : Bool}) -> {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}:
  match c:
    case EQ{}:
      Empty.absurd({Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool},
        L.true_not_false(GS.smem(u, GS.nbrs(u, adj)),
          L.subst(U32, x => {GS.smem(x, GS.nbrs(u, adj)) == True{} : Bool}, v, u,
            Equal.sym(U32, u, v, O.antisym(~U32, ~U32.cmp, O.u32_order, u, v, ec)), hp),
          L.not_true(GS.smem(u, GS.nbrs(u, adj)), loopfree_at(adj, u, hl))))
    case LT{}:
      FM.ne_of_lt(~U32, ~U32.cmp, u, v, ec)
    case GT{}:
      FM.ne_of_gt(~U32, ~U32.cmp, u, v, ec)

def wf_unlink(d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +su: List<&2, ME.Entry<U32, Unit>>, +sv: List<&2, ME.Entry<U32, Unit>>, +hfu: {GS.find(u, adj) == Some{su} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hfv: {GS.find(v, adj) == Some{sv} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hne: {Cmp.is_eq(U32.cmp(u, v)) == False{} : Bool}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(GS.GM{d, GS.unlink(d, adj, u, v, su, sv)}) == True{} : Bool}:
  match d:
    case True{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{True{}, GS.put(u, GS.sdel(v, zz), adj)}) == True{} : Bool}, GS.nbrs(u, adj), su,
        nbrs_of_some(u, adj, su, hfu),
        wf_parts(True{}, D1(adj, u, v),
          closed_D1(adj, u, v, wf_closed(True{}, adj, h)),
          loopfree_D1(adj, u, v, hne, wf_loopfree(True{}, adj, h)),
          {==}))
    case False{}:
      L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{False{}, GS.put(v, GS.sdel(u, sv), GS.put(u, GS.sdel(v, zz), adj))}) == True{} : Bool}, GS.nbrs(u, adj), su,
        nbrs_of_some(u, adj, su, hfu),
        L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.wf(GS.GM{False{}, GS.put(v, GS.sdel(u, zz), D1(adj, u, v))}) == True{} : Bool}, GS.nbrs(v, D1(adj, u, v)), sv,
          Equal.trans(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(v, D1(adj, u, v)), GS.nbrs(v, adj), sv,
            W.nbrs_put_other(v, u, GS.sdel(v, GS.nbrs(u, adj)), adj, ne_flip(u, v, hne)),
            nbrs_of_some(v, adj, sv, hfv)),
          wf_parts(False{}, D2(adj, u, v),
            closed_D2(adj, u, v, wf_closed(False{}, adj, h)),
            loopfree_D2(adj, u, v, hne, wf_loopfree(False{}, adj, h)),
            symmetric_D2(adj, u, v, hne, hso, wf_loopfree(False{}, adj, h), wf_sym(False{}, adj, h)))))

def wf_remove_present(present: Bool, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +su: List<&2, ME.Entry<U32, Unit>>, +sv: List<&2, ME.Entry<U32, Unit>>, +hfu: {GS.find(u, adj) == Some{su} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hfv: {GS.find(v, adj) == Some{sv} : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hpr: {GS.smem(v, su) == present : Bool}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.remove_present(present, d, adj, u, v, su, sv))) == True{} : Bool}:
  match present:
    case False{}:
      h
    case True{}:
      wf_unlink(d, adj, u, v, su, sv, hfu, hfv,
        ne_of_edge_c(U32.cmp(u, v), u, v, adj, {==},
          L.subst(List<&2, ME.Entry<U32, Unit>>, zz => {GS.smem(v, zz) == True{} : Bool}, su, GS.nbrs(u, adj),
            Equal.sym(List<&2, ME.Entry<U32, Unit>>, GS.nbrs(u, adj), su, nbrs_of_some(u, adj, su, hfu)), hpr),
          wf_loopfree(d, adj, h)),
        hso, h)

def wf_remove_edge_at(mu: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, mv: Maybe<&2, List<&2, ME.Entry<U32, Unit>>>, +d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hmu: {GS.find(u, adj) == mu : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hmv: {GS.find(v, adj) == mv : Maybe<&2, List<&2, ME.Entry<U32, Unit>>>}, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.remove_edge_at(mu, mv, d, adj, u, v))) == True{} : Bool}:
  match mu mv:
    case None{} _:
      h
    case Some{+su} None{}:
      h
    case Some{+su} Some{+sv}:
      wf_remove_present(GS.smem(v, su), d, adj, u, v, su, sv, hmu, hmv, {==}, hso, h)

def wf_remove_edge(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, +u: U32, +v: U32, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, E.RemoveEdge{u, v}))) == True{} : Bool}:
  wf_remove_edge_at(GS.find(u, adj), GS.find(v, adj), d, adj, u, v, {==}, {==}, hso, h)

# ---- every spec operation preserves well-formedness ----

def wf_step(+d: Bool, +adj: List<&2, ME.Entry<U32, List<&2, ME.Entry<U32, Unit>>>>, op: E.Op, +hso: {SO.sorted(~U32, ~U32.cmp, List<&2, ME.Entry<U32, Unit>>, adj) == True{} : Bool}, +h: {GS.wf(GS.GM{d, adj}) == True{} : Bool}) -> {GS.wf(Pair.fst(GS.Model, E.Obs, GS.step(GS.GM{d, adj}, op))) == True{} : Bool}:
  match op:
    case E.AddVertex{+v}:
      wf_add_vertex(d, adj, v, h)
    case E.RemoveVertex{+v}:
      wf_remove_vertex(d, adj, v, h)
    case E.AddEdge{+u, +v}:
      wf_add_edge(d, adj, u, v, h)
    case E.RemoveEdge{+u, +v}:
      wf_remove_edge(d, adj, u, v, hso, h)
    case E.HasVertex{+v}:
      W.wf_has_vertex(d, adj, v, h)
    case E.HasEdge{+u, +v}:
      W.wf_has_edge(d, adj, u, v, h)
    case E.Neighbors{+v}:
      W.wf_neighbors(d, adj, v, h)
    case E.Vertices{}:
      W.wf_vertices(d, adj, h)
    case E.Edges{}:
      W.wf_edges(d, adj, h)
