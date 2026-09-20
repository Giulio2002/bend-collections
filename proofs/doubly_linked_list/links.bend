import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/balanced_search_tree.bend as B
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./nodes.bend as NS

# The link invariant: items xs are stored in consecutive nodes whose value,
# prev and next fields agree with the sequence (p before the first item, q
# after the last), and walking next links from the first reproduces xs.

def fst(xs: List<&2, Nat>, q: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      q
    case Con{h, t}:
      Some{h}

def lst(xs: List<&2, Nat>, p: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      p
    case Con{h, t}:
      lst(t, Some{h})

def lk(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, xs: List<&2, E.Item<T>>, p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      {True{} == True{} : Bool}
    case Con{E.Item{+i, v}, +t}:
      {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>} & lk(T, nodes, t, Some{i}, q)

def memM(a: Maybe<&2, Nat>, l: List<&2, Nat>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{z}:
      NS.mem(z, l)

def dist(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, +t}:
      Bool.and(Bool.not(NS.mem(h, t)), dist(t))

def or_false_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.true_false(h))
    case False{}:
      h

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

def dist_head(+h: Nat, +t: List<&2, Nat>, +d: {dist(Con{h, t}) == True{} : Bool}) -> {NS.mem(h, t) == False{} : Bool}:
  not_true(NS.mem(h, t), L.and_left(Bool.not(NS.mem(h, t)), dist(t), d))

def dist_tail(+h: Nat, +t: List<&2, Nat>, +d: {dist(Con{h, t}) == True{} : Bool}) -> {dist(t) == True{} : Bool}:
  L.and_right(Bool.not(NS.mem(h, t)), dist(t), d)

def ne_flip(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(b, a), Nat.is_eq(a, b), False{}, NS.is_eq_sym(a, b), h)

# i differs from every member z of a list that does not contain i.
def ne_of_mem(+i: Nat, +z: Nat, +l: List<&2, Nat>, +mz: {NS.mem(z, l) == True{} : Bool}, +mi: {NS.mem(i, l) == False{} : Bool}, b: Bool, +eb: {Nat.is_eq(i, z) == b : Bool}) -> {Nat.is_eq(i, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Nat.is_eq(i, z) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, NS.mem(i, l), False{}, Equal.sym(Bool, NS.mem(i, l), True{}, L.subst(Nat, x => {NS.mem(x, l) == True{} : Bool}, z, i, Equal.sym(Nat, i, z, N.eq_from_is_eq(i, z, eb)), mz)), mi)))

# ---- framing: updates outside the items do not matter ----

def frame_put(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +j: Nat, +x: D.Node<T>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {NS.mem(j, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.put(T, nodes, j, x), xs, p, q):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, q)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.put(T, nodes, j, x), i), D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), q)}}, NS.get_put_other(T, nodes, i, j, x, g, ne_flip(j, i, or_false_l(Nat.is_eq(j, i), NS.mem(j, NS.ids(T, t)), m))), h1),
       frame_put(T, nodes, t, Some{i}, q, j, x, g, or_false_r(Nat.is_eq(j, i), NS.mem(j, NS.ids(T, t)), m), h2))

def frame_drop(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +j: Nat, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {NS.mem(j, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.drop(T, nodes, j), xs, p, q):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, q)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.drop(T, nodes, j), i), D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), q)}}, NS.get_drop_other(T, nodes, i, j, g, ne_flip(j, i, or_false_l(Nat.is_eq(j, i), NS.mem(j, NS.ids(T, t)), m))), h1),
       frame_drop(T, nodes, t, Some{i}, q, j, g, or_false_r(Nat.is_eq(j, i), NS.mem(j, NS.ids(T, t)), m), h2))

def frame_sn(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +z: Nat, +q2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {NS.mem(z, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_next(T, nodes, Some{z}, q2), xs, p, q):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, q)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_next(T, nodes, Some{z}, q2), i), D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), q)}}, NS.wn_other(T, D.node(T, nodes, z), nodes, z, q2, i, g, ne_flip(z, i, or_false_l(Nat.is_eq(z, i), NS.mem(z, NS.ids(T, t)), m))), h1),
       frame_sn(T, nodes, t, Some{i}, q, z, q2, g, or_false_r(Nat.is_eq(z, i), NS.mem(z, NS.ids(T, t)), m), h2))

def frame_sp(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +z: Nat, +p2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {NS.mem(z, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_prev(T, nodes, Some{z}, p2), xs, p, q):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, q)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_prev(T, nodes, Some{z}, p2), i), D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), q)}}, NS.wp_other(T, D.node(T, nodes, z), nodes, z, p2, i, g, ne_flip(z, i, or_false_l(Nat.is_eq(z, i), NS.mem(z, NS.ids(T, t)), m))), h1),
       frame_sp(T, nodes, t, Some{i}, q, z, p2, g, or_false_r(Nat.is_eq(z, i), NS.mem(z, NS.ids(T, t)), m), h2))

# Relinking at a (None: no change) outside the items.
def frame_snM(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, a: Maybe<&2, Nat>, +q2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {memM(a, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_next(T, nodes, a, q2), xs, p, q):
  match a:
    case None{}:
      h
    case Some{+z}:
      frame_sn(T, nodes, xs, p, q, z, q2, g, m, h)

def frame_spM(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +p2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +m: {memM(b, NS.ids(T, xs)) == False{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_prev(T, nodes, b, p2), xs, p, q):
  match b:
    case None{}:
      h
    case Some{+z}:
      frame_sp(T, nodes, xs, p, q, z, p2, g, m, h)

# ---- splitting and joining ----

def fst_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +q: Maybe<&2, Nat>) -> {fst(SC.append(Nat, xs, ys), q) == fst(xs, fst(ys, q)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def lst_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +p: Maybe<&2, Nat>) -> {lst(SC.append(Nat, xs, ys), p) == lst(ys, lst(xs, p)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      lst_app(t, ys, Some{h})

def fst_ids_app(-T: Data, +xs: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>, +q: Maybe<&2, Nat>) -> {fst(NS.ids(T, SC.append(E.Item<T>, xs, ys)), q) == fst(NS.ids(T, xs), fst(NS.ids(T, ys), q)) : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, fst(NS.ids(T, SC.append(E.Item<T>, xs, ys)), q), fst(SC.append(Nat, NS.ids(T, xs), NS.ids(T, ys)), q), fst(NS.ids(T, xs), fst(NS.ids(T, ys), q)),
    Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => fst(z, q), NS.ids(T, SC.append(E.Item<T>, xs, ys)), SC.append(Nat, NS.ids(T, xs), NS.ids(T, ys)), NS.ids_app(T, xs, ys)),
    fst_app(NS.ids(T, xs), NS.ids(T, ys), q))

def lst_ids_app(-T: Data, +xs: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>) -> {lst(NS.ids(T, SC.append(E.Item<T>, xs, ys)), p) == lst(NS.ids(T, ys), lst(NS.ids(T, xs), p)) : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, lst(NS.ids(T, SC.append(E.Item<T>, xs, ys)), p), lst(SC.append(Nat, NS.ids(T, xs), NS.ids(T, ys)), p), lst(NS.ids(T, ys), lst(NS.ids(T, xs), p)),
    Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => lst(z, p), NS.ids(T, SC.append(E.Item<T>, xs, ys)), SC.append(Nat, NS.ids(T, xs), NS.ids(T, ys)), NS.ids_app(T, xs, ys)),
    lst_app(NS.ids(T, xs), NS.ids(T, ys), p))

def Split(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>, xs: List<&2, E.Item<T>>, ys: List<&2, E.Item<T>>, p: Maybe<&2, Nat>, q: Maybe<&2, Nat>) -> Type:
  lk(T, nodes, xs, p, fst(NS.ids(T, ys), q)) & lk(T, nodes, ys, lst(NS.ids(T, xs), p), q)

def cons_split(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +v: T, +t: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +e1: {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), fst(NS.ids(T, ys), q))}} : Maybe<&2, D.Node<T>>}, r: Split(T, nodes, t, ys, Some{i}, q)) -> Split(T, nodes, Con{E.Item{i, v}, t}, ys, p, q):
  match r:
    case Tuple{a, b}:
      ((e1, a), b)

def split(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, h: lk(T, nodes, SC.append(E.Item<T>, xs, ys), p, q)) -> Split(T, nodes, xs, ys, p, q):
  match xs h:
    case Nil{} _:
      ({==}, h)
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      cons_split(T, nodes, i, v, t, ys, p, q, Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, SC.append(E.Item<T>, t, ys)), q)}}, Some{D.N{v, p, fst(NS.ids(T, t), fst(NS.ids(T, ys), q))}}, h1, Equal.cong(Maybe<&2, Nat>, Maybe<&2, D.Node<T>>, z => Some{D.N{v, p, z}}, fst(NS.ids(T, SC.append(E.Item<T>, t, ys)), q), fst(NS.ids(T, t), fst(NS.ids(T, ys), q)), fst_ids_app(T, t, ys, q))), split(T, nodes, t, ys, Some{i}, q, h2))

def join(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, ha: lk(T, nodes, xs, p, fst(NS.ids(T, ys), q)), hb: lk(T, nodes, ys, lst(NS.ids(T, xs), p), q)) -> lk(T, nodes, SC.append(E.Item<T>, xs, ys), p, q):
  match xs ha:
    case Nil{} _:
      hb
    case Con{E.Item{+i, +v}, +t} Tuple{a1, a2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), fst(NS.ids(T, ys), q))}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, fst(NS.ids(T, ys), q))
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), fst(NS.ids(T, ys), q))}}, Some{D.N{v, p, fst(NS.ids(T, SC.append(E.Item<T>, t, ys)), q)}}, a1, Equal.cong(Maybe<&2, Nat>, Maybe<&2, D.Node<T>>, z => Some{D.N{v, p, z}}, fst(NS.ids(T, t), fst(NS.ids(T, ys), q)), fst(NS.ids(T, SC.append(E.Item<T>, t, ys)), q), Equal.sym(Maybe<&2, Nat>, fst(NS.ids(T, SC.append(E.Item<T>, t, ys)), q), fst(NS.ids(T, t), fst(NS.ids(T, ys), q)), fst_ids_app(T, t, ys, q)))),
       join(T, nodes, t, ys, Some{i}, q, a2, hb))

# ---- relinking the ends of a linked run ----

def or_true(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_true_r(+res: Bool, r: Maybe<&2, Nat>, +j: Nat, +h: Nat, +t: List<&2, Nat>, +ih: {memM(r, Con{h, t}) == True{} : Bool}) -> {memM(r, Con{j, Con{h, t}}) == True{} : Bool}:
  match r:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(ih))
    case Some{+z}:
      L.subst(Bool, b => {Bool.or(Nat.is_eq(z, j), b) == True{} : Bool}, True{}, NS.mem(z, Con{h, t}), Equal.sym(Bool, NS.mem(z, Con{h, t}), True{}, ih), or_true(Nat.is_eq(z, j)))

def lst_mem(+xs: List<&2, Nat>, +j: Nat) -> {memM(lst(xs, Some{j}), Con{j, xs}) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subst(Bool, b => {Bool.or(b, False{}) == True{} : Bool}, True{}, Nat.is_eq(j, j), Equal.sym(Bool, Nat.is_eq(j, j), True{}, N.is_eq_refl(j)), {==})
    case Con{+h, +t}:
      +r = lst(t, Some{h})
      or_true_r(memM(r, Con{j, Con{h, t}}), r, j, h, t, lst_mem(t, h))

def node_skip(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, a: Maybe<&2, Nat>, +q2: Maybe<&2, Nat>, +i: Nat, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +ha: {memM(a, l) == True{} : Bool}, +mi: {NS.mem(i, l) == False{} : Bool}) -> {D.node(T, D.set_next(T, nodes, a, q2), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  match a:
    case None{}:
      {==}
    case Some{+z}:
      NS.wn_other(T, D.node(T, nodes, z), nodes, z, q2, i, g, ne_of_mem(i, z, l, ha, mi, Nat.is_eq(i, z), {==}))

# Point the last item's next link at q2.
def retarget_last(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +q2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +d: {dist(NS.ids(T, xs)) == True{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_next(T, nodes, lst(NS.ids(T, xs), p), q2), xs, p, q2):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, Nil{}} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, q}} : Maybe<&2, D.Node<T>>}
      -H2 = {True{} == True{} : Bool}
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_next(T, nodes, Some{i}, q2), i), D.node(T, D.put(T, nodes, i, D.N{v, p, q2}), i), Some{D.N{v, p, q2}},
         Equal.cong(B.OrdMap<Nat, D.Node<T>>, Maybe<&2, D.Node<T>>, z => D.node(T, z, i), D.set_next(T, nodes, Some{i}, q2), D.put(T, nodes, i, D.N{v, p, q2}), NS.sn_put(T, nodes, i, v, p, q, q2, h1)),
         NS.get_put_same(T, nodes, i, D.N{v, p, q2}, g)),
       {==})
    case Con{E.Item{+i, +v}, Con{E.Item{+j, +w}, +t}} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, Some{j}}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, Con{E.Item{j, w}, t}, Some{i}, q)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_next(T, nodes, lst(NS.ids(T, t), Some{j}), q2), i), D.node(T, nodes, i), Some{D.N{v, p, Some{j}}},
         node_skip(T, nodes, lst(NS.ids(T, t), Some{j}), q2, i, Con{j, NS.ids(T, t)}, g, lst_mem(NS.ids(T, t), j), dist_head(i, Con{j, NS.ids(T, t)}, d)),
         h1),
       retarget_last(T, nodes, Con{E.Item{j, w}, t}, Some{i}, q, q2, g, dist_tail(i, Con{j, NS.ids(T, t)}, d), h2))

# Point the first item's prev link at p2.
def retarget_first(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +p2: Maybe<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +d: {dist(NS.ids(T, xs)) == True{} : Bool}, h: lk(T, nodes, xs, p, q)) -> lk(T, D.set_prev(T, nodes, fst(NS.ids(T, xs), None{}), p2), xs, p2, q):
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), q)}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, q)
      +nd = {D.N{v, p2, fst(NS.ids(T, t), q)} : D.Node<T>}
      +ep = NS.sp_put(T, nodes, i, v, p, fst(NS.ids(T, t), q), p2, h1)
      (Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_prev(T, nodes, Some{i}, p2), i), D.node(T, D.put(T, nodes, i, nd), i), Some{nd},
         Equal.cong(B.OrdMap<Nat, D.Node<T>>, Maybe<&2, D.Node<T>>, z => D.node(T, z, i), D.set_prev(T, nodes, Some{i}, p2), D.put(T, nodes, i, nd), ep),
         NS.get_put_same(T, nodes, i, nd, g)),
       L.subst(B.OrdMap<Nat, D.Node<T>>, z => lk(T, z, t, Some{i}, q), D.put(T, nodes, i, nd), D.set_prev(T, nodes, Some{i}, p2), Equal.sym(B.OrdMap<Nat, D.Node<T>>, D.set_prev(T, nodes, Some{i}, p2), D.put(T, nodes, i, nd), ep),
         frame_put(T, nodes, t, Some{i}, q, i, nd, g, dist_head(i, NS.ids(T, t), d), h2)))

# ---- walking the links ----

def witems(-T: Data, fuel: Nat, +nodes: B.OrdMap<Nat, D.Node<T>>, cur: Maybe<&2, Nat>, m: Maybe<&2, D.Node<T>>) -> List<&2, E.Item<T>>:
  match fuel cur m:
    case 0n _ _:
      Nil{}
    case 1n+f None{} _:
      Nil{}
    case 1n+f Some{i} None{}:
      Nil{}
    case 1n+f Some{+i} Some{D.N{v, p, +n}}:
      Con{E.Item{i, v}, witems(T, f, nodes, n, D.nodeM(T, nodes, n))}

def walk_lk(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, h: lk(T, nodes, xs, p, None{})) -> {witems(T, SC.length(E.Item<T>, xs), nodes, fst(NS.ids(T, xs), None{}), D.nodeM(T, nodes, fst(NS.ids(T, xs), None{}))) == xs : List<&2, E.Item<T>>}:
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), None{})}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, None{})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), None{})}}, h1) : {witems(T, 1n+SC.length(E.Item<T>, t), nodes, Some{i}, _) == Con{E.Item{i, v}, t} : List<&2, E.Item<T>>}
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => Con{E.Item{i, v}, z}, witems(T, SC.length(E.Item<T>, t), nodes, fst(NS.ids(T, t), None{}), D.nodeM(T, nodes, fst(NS.ids(T, t), None{}))), t, walk_lk(T, nodes, t, Some{i}, h2))

def walkv_lk(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, h: lk(T, nodes, xs, p, None{})) -> {D.walkv(T, SC.length(E.Item<T>, xs), nodes, D.nodeM(T, nodes, fst(NS.ids(T, xs), None{}))) == DS.vals(T, xs) : List<&2, T>}:
  match xs h:
    case Nil{} _:
      {==}
    case Con{E.Item{+i, +v}, +t} Tuple{h1, h2}:
      -H1 = {D.node(T, nodes, i) == Some{D.N{v, p, fst(NS.ids(T, t), None{})}} : Maybe<&2, D.Node<T>>}
      -H2 = lk(T, nodes, t, Some{i}, None{})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), Some{D.N{v, p, fst(NS.ids(T, t), None{})}}, h1) : {D.walkv(T, 1n+SC.length(E.Item<T>, t), nodes, _) == Con{v, DS.vals(T, t)} : List<&2, T>}
      Equal.cong(List<&2, T>, List<&2, T>, z => Con{v, z}, D.walkv(T, SC.length(E.Item<T>, t), nodes, D.nodeM(T, nodes, fst(NS.ids(T, t), None{}))), DS.vals(T, t), walkv_lk(T, nodes, t, Some{i}, h2))
