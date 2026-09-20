import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/balanced_search_tree.bend as B
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ../balanced_search_tree/steps.bend as ST
import ../balanced_search_tree/api.bend as API
import ./model.bend as M

# Graph state: abstraction, invariant and every public operation.

def abs(g: G.Graph) -> GS.Model:
  match g:
    case G.G{d, adj}:
      GS.GM{d, M.amap(M.aabs(adj))}

# Invariant: the vertex map and every neighbour set satisfy the ordered-map
# invariant (sorted keys, the red-black invariant, exact size).
def inv(g: G.Graph) -> Bool:
  match g:
    case G.G{d, +adj}:
      Bool.and(M.ainv(adj), M.allinv(M.aabs(adj)))

def view1(r: G.Graph & E.Obs) -> GS.Model & E.Obs:
  match r:
    case Tuple{g, o}:
      (abs(g), o)

def StepOK(g: G.Graph, op: E.Op) -> Type:
  {view1(G.step(g, op)) == GS.step(abs(g), op) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.step(g, op))) == True{} : Bool}

# Store a set at u: abstraction and invariants.
def PutOK(adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, u: U32, x: B.OrdMap<U32, Unit>) -> Type:
  {M.amap(M.aabs(G.put(adj, u, x))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>} & ({M.ainv(G.put(adj, u, x)) == True{} : Bool} & {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool})

def put_ok(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}) -> PutOK(adj, u, x):
  +ea = API.insert_abs(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, u, x, ga)
  (Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(adj, u, x))), M.amap(S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, x, M.aabs(adj))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))),
     Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => M.amap(z), M.aabs(G.put(adj, u, x)), S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, x, M.aabs(adj)), ea),
     M.amap_ins(u, x, M.aabs(adj))),
   (API.insert_inv(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, u, x, ga),
    L.subst(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, xs => {M.allinv(xs) == True{} : Bool}, S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, x, M.aabs(adj)), M.aabs(G.put(adj, u, x)), Equal.sym(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, M.aabs(G.put(adj, u, x)), S.ins(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, x, M.aabs(adj)), ea), M.allinv_ins(u, x, M.aabs(adj), ix, aa))))

def put_eq(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}) -> {M.amap(M.aabs(G.put(adj, u, x))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  Pair.fst({M.amap(M.aabs(G.put(adj, u, x))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, {M.ainv(G.put(adj, u, x)) == True{} : Bool} & {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}, put_ok(adj, u, x, ga, aa, ix))

def put_ga(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}) -> {M.ainv(G.put(adj, u, x)) == True{} : Bool}:
  Pair.fst({M.ainv(G.put(adj, u, x)) == True{} : Bool}, {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}, Pair.snd({M.amap(M.aabs(G.put(adj, u, x))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, {M.ainv(G.put(adj, u, x)) == True{} : Bool} & {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}, put_ok(adj, u, x, ga, aa, ix)))

def put_aa(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}) -> {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}:
  Pair.snd({M.ainv(G.put(adj, u, x)) == True{} : Bool}, {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}, Pair.snd({M.amap(M.aabs(G.put(adj, u, x))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, {M.ainv(G.put(adj, u, x)) == True{} : Bool} & {M.allinv(M.aabs(G.put(adj, u, x))) == True{} : Bool}, put_ok(adj, u, x, ga, aa, ix)))

def sadd_abs(+s: B.OrdMap<U32, Unit>, +w: U32, +i: {M.sinv(s) == True{} : Bool}) -> {M.sabs(G.sadd(s, w)) == GS.sadd(w, M.sabs(s)) : List<&2, BE.Entry<U32, Unit>>}:
  API.insert_abs(~U32, ~U32.cmp, ~O.u32_order, Unit, s, w, Unit{}, i)

def sadd_inv(+s: B.OrdMap<U32, Unit>, +w: U32, +i: {M.sinv(s) == True{} : Bool}) -> {M.sinv(G.sadd(s, w)) == True{} : Bool}:
  API.insert_inv(~U32, ~U32.cmp, ~O.u32_order, Unit, s, w, Unit{}, i)

# Two successive puts (the undirected case of link/unlink).
def put2_eq(+adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +v: U32, +y: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}, +iy: {M.sinv(y) == True{} : Bool}) -> {M.amap(M.aabs(G.put(G.put(adj, u, x), v, y))) == S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj)))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +a1 = G.put(adj, u, x)
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(a1, v, y))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), M.amap(M.aabs(a1))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj)))),
    put_eq(a1, v, y, put_ga(adj, u, x, ga, aa, ix), put_aa(adj, u, x, ga, aa, ix), iy),
    Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), z), M.amap(M.aabs(a1)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))), put_eq(adj, u, x, ga, aa, ix)))

def put2_inv(+d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +v: U32, +y: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}, +iy: {M.sinv(y) == True{} : Bool}) -> {inv(G.G{d, G.put(G.put(adj, u, x), v, y)}) == True{} : Bool}:
  +a1 = G.put(adj, u, x)
  L.and_intro(M.ainv(G.put(a1, v, y)), M.allinv(M.aabs(G.put(a1, v, y))), put_ga(a1, v, y, put_ga(adj, u, x, ga, aa, ix), put_aa(adj, u, x, ga, aa, ix), iy), put_aa(a1, v, y, put_ga(adj, u, x, ga, aa, ix), put_aa(adj, u, x, ga, aa, ix), iy))

def put1_inv(+d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +x: B.OrdMap<U32, Unit>, +ga: {M.ainv(adj) == True{} : Bool}, +aa: {M.allinv(M.aabs(adj)) == True{} : Bool}, +ix: {M.sinv(x) == True{} : Bool}) -> {inv(G.G{d, G.put(adj, u, x)}) == True{} : Bool}:
  L.and_intro(M.ainv(G.put(adj, u, x)), M.allinv(M.aabs(G.put(adj, u, x))), put_ga(adj, u, x, ga, aa, ix), put_aa(adj, u, x, ga, aa, ix))

# ---- state-changing operations, over an arbitrary lookup result ----

def av_core(+d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32, m: Maybe<&2, B.OrdMap<U32, Unit>>, +g: {inv(G.G{d, adj}) == True{} : Bool}) -> {view1(G.obs_unit(G.add_vertex_at(m, d, adj, v))) == GS.add_vertex_at(M.mapM(m), d, M.amap(M.aabs(adj)), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_vertex_at(m, d, adj, v)))) == True{} : Bool}:
  match m:
    case None{}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +x = B.new(U32, Unit)
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{d, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.put(adj, v, x))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, Nil{}, M.amap(M.aabs(adj))), put_eq(adj, v, x, ga, aa, {==})),
       put1_inv(d, adj, v, x, ga, aa, {==}))
    case Some{s}:
      ({==}, g)

def rv_core(+d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +v: U32, m: Maybe<&2, B.OrdMap<U32, Unit>>, +g: {inv(G.G{d, adj}) == True{} : Bool}) -> {view1(G.obs_unit(G.remove_vertex_at(m, d, adj, v))) == GS.remove_vertex_at(M.mapM(m), d, M.amap(M.aabs(adj)), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_vertex_at(m, d, adj, v)))) == True{} : Bool}:
  match m:
    case None{}:
      ({==}, g)
    case Some{s}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +adj1 = Pair.fst(B.OrdMap<U32, B.OrdMap<U32, Unit>>, Result<&2, &2, BE.Error, B.OrdMap<U32, Unit>>, B.remove(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v))
      +er = Pair.fst({M.aabs(adj1) == S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj)) : List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>}, {M.ainv(adj1) == True{} : Bool}, API.remove_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga))
      +g1 = Pair.snd({M.aabs(adj1) == S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj)) : List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>}, {M.ainv(adj1) == True{} : Bool}, API.remove_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga))
      +aa1 = L.subst(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, xs => {M.allinv(xs) == True{} : Bool}, S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj)), M.aabs(adj1), Equal.sym(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, M.aabs(adj1), S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj)), er), M.allinv_del(v, M.aabs(adj), aa))
      +es = M.strip_abs(adj1, v)
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{d, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.strip(adj1, v))), GS.strip(v, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.amap(M.aabs(adj)))),
         Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.strip(adj1, v))), M.amap(M.smap(v, M.aabs(adj1))), GS.strip(v, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.amap(M.aabs(adj)))),
           Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => M.amap(z), M.aabs(G.strip(adj1, v)), M.smap(v, M.aabs(adj1)), es),
           Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.smap(v, M.aabs(adj1))), GS.strip(v, M.amap(M.aabs(adj1))), GS.strip(v, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.amap(M.aabs(adj)))),
             M.amap_smap(v, M.aabs(adj1), aa1),
             Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.strip(v, z), M.amap(M.aabs(adj1)), S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.amap(M.aabs(adj))),
               Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(adj1)), M.amap(S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj))), S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.amap(M.aabs(adj))),
                 Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => M.amap(z), M.aabs(adj1), S.del(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, M.aabs(adj)), er),
                 M.amap_del(v, M.aabs(adj))))))),
       L.and_intro(M.ainv(G.strip(adj1, v)), M.allinv(M.aabs(G.strip(adj1, v))), M.strip_inv(adj1, v, g1),
         L.subst(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, xs => {M.allinv(xs) == True{} : Bool}, M.smap(v, M.aabs(adj1)), M.aabs(G.strip(adj1, v)), Equal.sym(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, M.aabs(G.strip(adj1, v)), M.smap(v, M.aabs(adj1)), es), M.allinv_smap(v, M.aabs(adj1), aa1))))

def ae_core(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, lp: Bool, d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, +g: {inv(G.G{d, adj}) == True{} : Bool}, +au: {M.allM(mu) == True{} : Bool}, +av: {M.allM(mv) == True{} : Bool}) -> {view1(G.obs_unit(G.add_edge_at(mu, mv, lp, d, adj, u, v))) == GS.add_edge_at(M.mapM(mu), M.mapM(mv), lp, d, M.amap(M.aabs(adj)), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_edge_at(mu, mv, lp, d, adj, u, v)))) == True{} : Bool}:
  match mu mv lp d:
    case None{} _ _ _:
      ({==}, g)
    case Some{su} None{} _ _:
      ({==}, g)
    case Some{su} Some{sv} True{} _:
      ({==}, g)
    case Some{+su} Some{+sv} False{} True{}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +x = G.sadd(su, v)
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{True{}, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.put(adj, u, x))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sadd(v, M.sabs(su)), M.amap(M.aabs(adj))),
         Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(adj, u, x))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sadd(v, M.sabs(su)), M.amap(M.aabs(adj))),
           put_eq(adj, u, x, ga, aa, sadd_inv(su, v, au)),
           Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, z, M.amap(M.aabs(adj))), M.sabs(x), GS.sadd(v, M.sabs(su)), sadd_abs(su, v, au)))),
       put1_inv(True{}, adj, u, x, ga, aa, sadd_inv(su, v, au)))
    case Some{+su} Some{+sv} False{} False{}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +x = G.sadd(su, v)
      +y = G.sadd(sv, u)
      +A = M.amap(M.aabs(adj))
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{False{}, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.put(G.put(adj, u, x), v, y))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sadd(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sadd(v, M.sabs(su)), A)),
         Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(G.put(adj, u, x), v, y))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sadd(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sadd(v, M.sabs(su)), A)),
           put2_eq(adj, u, x, v, y, ga, aa, sadd_inv(su, v, au), sadd_inv(sv, u, av)),
           Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sadd(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sadd(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sadd(v, M.sabs(su)), A)),
             Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, z, S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), M.sabs(y), GS.sadd(u, M.sabs(sv)), sadd_abs(sv, u, av)),
             Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sadd(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, z, A)), M.sabs(x), GS.sadd(v, M.sabs(su)), sadd_abs(su, v, au))))),
       put2_inv(False{}, adj, u, x, v, y, ga, aa, sadd_inv(su, v, au), sadd_inv(sv, u, av)))

def rp_core(p: Bool, d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, +su: B.OrdMap<U32, Unit>, +sv: B.OrdMap<U32, Unit>, +g: {inv(G.G{d, adj}) == True{} : Bool}, +au: {M.sinv(su) == True{} : Bool}, +av: {M.sinv(sv) == True{} : Bool}) -> {view1(G.obs_unit(G.remove_present(p, d, adj, u, v, su, sv))) == GS.remove_present(p, d, M.amap(M.aabs(adj)), u, v, M.sabs(su), M.sabs(sv)) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_present(p, d, adj, u, v, su, sv)))) == True{} : Bool}:
  match p d:
    case False{} _:
      ({==}, g)
    case True{} True{}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +x = G.sdel(su, v)
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{True{}, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.put(adj, u, x))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sdel(v, M.sabs(su)), M.amap(M.aabs(adj))),
         Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(adj, u, x))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), M.amap(M.aabs(adj))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sdel(v, M.sabs(su)), M.amap(M.aabs(adj))),
           put_eq(adj, u, x, ga, aa, M.sdel_inv(su, v, au)),
           Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, z, M.amap(M.aabs(adj))), M.sabs(x), GS.sdel(v, M.sabs(su)), M.sdel_abs(su, v, au)))),
       put1_inv(True{}, adj, u, x, ga, aa, M.sdel_inv(su, v, au)))
    case True{} False{}:
      +ga = L.and_left(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +aa = L.and_right(M.ainv(adj), M.allinv(M.aabs(adj)), g)
      +x = G.sdel(su, v)
      +y = G.sdel(sv, u)
      +A = M.amap(M.aabs(adj))
      (Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => (GS.GM{False{}, z}, E.OUnit{Done{Unit{}}}), M.amap(M.aabs(G.put(G.put(adj, u, x), v, y))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sdel(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sdel(v, M.sabs(su)), A)),
         Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, M.amap(M.aabs(G.put(G.put(adj, u, x), v, y))), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sdel(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sdel(v, M.sabs(su)), A)),
           put2_eq(adj, u, x, v, y, ga, aa, M.sdel_inv(su, v, au), M.sdel_inv(sv, u, av)),
           Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, M.sabs(y), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sdel(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sdel(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, GS.sdel(v, M.sabs(su)), A)),
             Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, z, S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, M.sabs(x), A)), M.sabs(y), GS.sdel(u, M.sabs(sv)), M.sdel_abs(sv, u, av)),
             Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, GS.sdel(u, M.sabs(sv)), S.ins(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, u, z, A)), M.sabs(x), GS.sdel(v, M.sabs(su)), M.sdel_abs(su, v, au))))),
       put2_inv(False{}, adj, u, x, v, y, ga, aa, M.sdel_inv(su, v, au), M.sdel_inv(sv, u, av)))

def re_core(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, +d: Bool, +adj: B.OrdMap<U32, B.OrdMap<U32, Unit>>, +u: U32, +v: U32, +g: {inv(G.G{d, adj}) == True{} : Bool}, +au: {M.allM(mu) == True{} : Bool}, +av: {M.allM(mv) == True{} : Bool}) -> {view1(G.obs_unit(G.remove_edge_at(mu, mv, d, adj, u, v))) == GS.remove_edge_at(M.mapM(mu), M.mapM(mv), d, M.amap(M.aabs(adj)), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_edge_at(mu, mv, d, adj, u, v)))) == True{} : Bool}:
  match mu mv:
    case None{} _:
      ({==}, g)
    case Some{su} None{}:
      ({==}, g)
    case Some{+su} Some{+sv}:
      %Equal.sym(Bool, B.contains(~U32, ~U32.cmp, Unit, su, v), GS.smem(v, M.sabs(su)), API.contains_ok(~U32, ~U32.cmp, ~O.u32_order, Unit, su, v, au)) : {view1(G.obs_unit(G.remove_present(_, d, adj, u, v, su, sv))) == GS.remove_present(GS.smem(v, M.sabs(su)), d, M.amap(M.aabs(adj)), u, v, M.sabs(su), M.sabs(sv)) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_present(_, d, adj, u, v, su, sv)))) == True{} : Bool}
      rp_core(GS.smem(v, M.sabs(su)), d, adj, u, v, su, sv, g, au, av)

# ---- queries ----

def he_eq(mu: Maybe<&2, B.OrdMap<U32, Unit>>, mv: Maybe<&2, B.OrdMap<U32, Unit>>, +v: U32, +au: {M.allM(mu) == True{} : Bool}) -> {G.has_edge_at(mu, mv, v) == GS.has_edge_at(M.mapM(mu), M.mapM(mv), v) : Result<&2, &2, E.Error, Bool>}:
  match mu mv:
    case None{} _:
      {==}
    case Some{su} None{}:
      {==}
    case Some{+su} Some{sv}:
      Equal.cong(Bool, Result<&2, &2, E.Error, Bool>, z => Done{z}, B.contains(~U32, ~U32.cmp, Unit, su, v), GS.smem(v, M.sabs(su)), API.contains_ok(~U32, ~U32.cmp, ~O.u32_order, Unit, su, v, au))

def nb_eq(m: Maybe<&2, B.OrdMap<U32, Unit>>) -> {G.neighbors_at(m) == GS.neighbors_at(M.mapM(m)) : Result<&2, &2, E.Error, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      Equal.cong(List<&2, U32>, Result<&2, &2, E.Error, List<&2, U32>>, z => Done{z}, G.keys(Unit, B.to_list(U32, Unit, s)), GS.keys(Unit, M.sabs(s)), M.nkeys(s))

# ---- every operation ----

def step_ok(+g: G.Graph, +op: E.Op, +h: {inv(g) == True{} : Bool}) -> StepOK(g, op):
  match g op:
    case G.G{+d, +adj} E.AddVertex{+v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {view1(G.obs_unit(G.add_vertex_at(_, d, adj, v))) == GS.add_vertex_at(GS.find(v, M.amap(xs)), d, M.amap(xs), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_vertex_at(_, d, adj, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {view1(G.obs_unit(G.add_vertex_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, v))) == GS.add_vertex_at(_, d, M.amap(xs), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_vertex_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, v)))) == True{} : Bool}
      av_core(d, adj, v, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), h)
    case G.G{+d, +adj} E.RemoveVertex{+v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {view1(G.obs_unit(G.remove_vertex_at(_, d, adj, v))) == GS.remove_vertex_at(GS.find(v, M.amap(xs)), d, M.amap(xs), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_vertex_at(_, d, adj, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {view1(G.obs_unit(G.remove_vertex_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, v))) == GS.remove_vertex_at(_, d, M.amap(xs), v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_vertex_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, v)))) == True{} : Bool}
      rv_core(d, adj, v, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), h)
    case G.G{+d, +adj} E.AddEdge{+u, +v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      +aa = L.and_right(M.ainv(adj), M.allinv(xs), h)
      +lp = Cmp.is_eq(U32.cmp(u, v))
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, u), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, u, ga)) : {view1(G.obs_unit(G.add_edge_at(_, G.get(adj, v), lp, d, adj, u, v))) == GS.add_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), lp, d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_edge_at(_, G.get(adj, v), lp, d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {view1(G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), _, lp, d, adj, u, v))) == GS.add_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), lp, d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), _, lp, d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), M.amap_find(u, xs)) : {view1(G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), lp, d, adj, u, v))) == GS.add_edge_at(_, GS.find(v, M.amap(xs)), lp, d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), lp, d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {view1(G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), lp, d, adj, u, v))) == GS.add_edge_at(M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), _, lp, d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.add_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), lp, d, adj, u, v)))) == True{} : Bool}
      ae_core(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), lp, d, adj, u, v, h, M.allinv_find(u, xs, aa), M.allinv_find(v, xs, aa))
    case G.G{+d, +adj} E.RemoveEdge{+u, +v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      +aa = L.and_right(M.ainv(adj), M.allinv(xs), h)
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, u), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, u, ga)) : {view1(G.obs_unit(G.remove_edge_at(_, G.get(adj, v), d, adj, u, v))) == GS.remove_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_edge_at(_, G.get(adj, v), d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {view1(G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), _, d, adj, u, v))) == GS.remove_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), _, d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), M.amap_find(u, xs)) : {view1(G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, u, v))) == GS.remove_edge_at(_, GS.find(v, M.amap(xs)), d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, u, v)))) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {view1(G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, u, v))) == GS.remove_edge_at(M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), _, d, M.amap(xs), u, v) : GS.Model & E.Obs} & {inv(Pair.fst(G.Graph, E.Obs, G.obs_unit(G.remove_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, u, v)))) == True{} : Bool}
      re_core(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), d, adj, u, v, h, M.allinv_find(u, xs, aa), M.allinv_find(v, xs, aa))
    case G.G{+d, +adj} E.HasVertex{+v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      (Equal.cong(Bool, GS.Model & E.Obs, z => (GS.GM{d, M.amap(xs)}, E.OBool{z}), B.contains(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v), S.is_some(List<&2, BE.Entry<U32, Unit>>, GS.find(v, M.amap(xs))),
         Equal.trans(Bool, B.contains(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj, v), S.is_some(B.OrdMap<U32, Unit>, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), S.is_some(List<&2, BE.Entry<U32, Unit>>, GS.find(v, M.amap(xs))),
           API.contains_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga),
           Equal.trans(Bool, S.is_some(B.OrdMap<U32, Unit>, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), S.is_some(List<&2, BE.Entry<U32, Unit>>, M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))), S.is_some(List<&2, BE.Entry<U32, Unit>>, GS.find(v, M.amap(xs))),
             Equal.sym(Bool, S.is_some(List<&2, BE.Entry<U32, Unit>>, M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))), S.is_some(B.OrdMap<U32, Unit>, S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.is_some_mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))),
             Equal.cong(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, Bool, z => S.is_some(List<&2, BE.Entry<U32, Unit>>, z), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), GS.find(v, M.amap(xs)), Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)))))),
       h)
    case G.G{+d, +adj} E.HasEdge{+u, +v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      +aa = L.and_right(M.ainv(adj), M.allinv(xs), h)
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, u), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, u, ga)) : {(GS.GM{d, M.amap(xs)}, E.OFlag{G.has_edge_at(_, G.get(adj, v), v)}) == (GS.GM{d, M.amap(xs)}, E.OFlag{GS.has_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), v)}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {(GS.GM{d, M.amap(xs)}, E.OFlag{G.has_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), _, v)}) == (GS.GM{d, M.amap(xs)}, E.OFlag{GS.has_edge_at(GS.find(u, M.amap(xs)), GS.find(v, M.amap(xs)), v)}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(u, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), M.amap_find(u, xs)) : {(GS.GM{d, M.amap(xs)}, E.OFlag{G.has_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), v)}) == (GS.GM{d, M.amap(xs)}, E.OFlag{GS.has_edge_at(_, GS.find(v, M.amap(xs)), v)}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {(GS.GM{d, M.amap(xs)}, E.OFlag{G.has_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), v)}) == (GS.GM{d, M.amap(xs)}, E.OFlag{GS.has_edge_at(M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), _, v)}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      (Equal.cong(Result<&2, &2, E.Error, Bool>, GS.Model & E.Obs, z => (GS.GM{d, M.amap(xs)}, E.OFlag{z}), G.has_edge_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), v), GS.has_edge_at(M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), v), he_eq(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, u, xs), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), v, M.allinv_find(u, xs, aa))),
       h)
    case G.G{+d, +adj} E.Neighbors{+v}:
      +xs = M.aabs(adj)
      +ga = L.and_left(M.ainv(adj), M.allinv(xs), h)
      %Equal.sym(Maybe<&2, B.OrdMap<U32, Unit>>, G.get(adj, v), S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs), API.get_ok(~U32, ~U32.cmp, ~O.u32_order, B.OrdMap<U32, Unit>, adj, v, ga)) : {(GS.GM{d, M.amap(xs)}, E.ONeighbors{G.neighbors_at(_)}) == (GS.GM{d, M.amap(xs)}, E.ONeighbors{GS.neighbors_at(GS.find(v, M.amap(xs)))}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, M.amap(xs)), M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), M.amap_find(v, xs)) : {(GS.GM{d, M.amap(xs)}, E.ONeighbors{G.neighbors_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))}) == (GS.GM{d, M.amap(xs)}, E.ONeighbors{GS.neighbors_at(_)}) : GS.Model & E.Obs} & {inv(G.G{d, adj}) == True{} : Bool}
      (Equal.cong(Result<&2, &2, E.Error, List<&2, U32>>, GS.Model & E.Obs, z => (GS.GM{d, M.amap(xs)}, E.ONeighbors{z}), G.neighbors_at(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs)), GS.neighbors_at(M.mapM(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))), nb_eq(S.find(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, v, xs))),
       h)
    case G.G{+d, +adj} E.Vertices{}:
      +xs = M.aabs(adj)
      (Equal.cong(List<&2, U32>, GS.Model & E.Obs, z => (GS.GM{d, M.amap(xs)}, E.OVertices{z}), G.keys(B.OrdMap<U32, Unit>, B.to_list(U32, B.OrdMap<U32, Unit>, adj)), GS.keys(List<&2, BE.Entry<U32, Unit>>, M.amap(xs)),
         Equal.trans(List<&2, U32>, G.keys(B.OrdMap<U32, Unit>, B.to_list(U32, B.OrdMap<U32, Unit>, adj)), G.keys(B.OrdMap<U32, Unit>, xs), GS.keys(List<&2, BE.Entry<U32, Unit>>, M.amap(xs)),
           Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, U32>, z => G.keys(B.OrdMap<U32, Unit>, z), B.to_list(U32, B.OrdMap<U32, Unit>, adj), xs, API.to_list_ok(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj)),
           Equal.trans(List<&2, U32>, G.keys(B.OrdMap<U32, Unit>, xs), GS.keys(B.OrdMap<U32, Unit>, xs), GS.keys(List<&2, BE.Entry<U32, Unit>>, M.amap(xs)), M.keys_eq(B.OrdMap<U32, Unit>, xs), Equal.sym(List<&2, U32>, GS.keys(List<&2, BE.Entry<U32, Unit>>, M.amap(xs)), GS.keys(B.OrdMap<U32, Unit>, xs), M.keys_amap(xs))))),
       h)
    case G.G{+d, +adj} E.Edges{}:
      +xs = M.aabs(adj)
      (Equal.cong(List<&2, E.Edge>, GS.Model & E.Obs, z => (GS.GM{d, M.amap(xs)}, E.OEdges{z}), G.edges_go(d, B.to_list(U32, B.OrdMap<U32, Unit>, adj)), GS.all_edges(d, M.amap(xs)),
         Equal.trans(List<&2, E.Edge>, G.edges_go(d, B.to_list(U32, B.OrdMap<U32, Unit>, adj)), G.edges_go(d, xs), GS.all_edges(d, M.amap(xs)),
           Equal.cong(List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>, List<&2, E.Edge>, z => G.edges_go(d, z), B.to_list(U32, B.OrdMap<U32, Unit>, adj), xs, API.to_list_ok(~U32, ~U32.cmp, B.OrdMap<U32, Unit>, adj)),
           M.edges_ok(d, xs))),
       h)
