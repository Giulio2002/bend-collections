import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/balanced_search_tree.bend as B
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ../../types/balanced_search_tree.bend as BE
import ./nodes.bend as NS
import ./links.bend as LK
import ./facts.bend as F
import ./cut.bend as C
import ./cores.bend as K

# List state: abstraction (walk the next links from head), invariant and
# every public operation.

def W(-T: Data, count: Nat, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>) -> List<&2, E.Item<T>>:
  LK.witems(T, count, nodes, head, D.nodeM(T, nodes, head))

def abs(-T: Data, s: D.DList<T>) -> DS.Model<T>:
  match s:
    case D.DL{tag, fresh, count, +head, tail, +nodes}:
      DS.DM{tag, fresh, W(T, count, nodes, head)}

# Invariant: the walked sequence is exactly linked (values, prev and next of
# every node), head/tail/count agree with it, ids are distinct and below the
# fresh id, every stored node is on the walk, and the store is a valid map.
def Inv(-T: Data, s: D.DList<T>) -> Type:
  match s:
    case D.DL{tag, fresh, +count, +head, +tail, +nodes}:
      F.Good(T, nodes, head, tail, count, fresh, W(T, count, nodes, head))

def view1(-T: Data, r: D.DList<T> & E.Obs<T>) -> DS.Model<T> & E.Obs<T>:
  match r:
    case Tuple{s, o}:
      (abs(T, s), o)

def StepOK(-T: Data, s: D.DList<T>, op: E.Op<T>) -> Type:
  {view1(T, D.step(T, s, op)) == DS.step(T, abs(T, s), op) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.step(T, s, op)))

# ---- a Good sequence is the walked one ----

def wcons(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +v: T, +t: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, +h1: {D.node(T, nodes, i) == Some{D.N{v, p, LK.fst(NS.ids(T, t), None{})}} : Maybe<&2, D.Node<T>>}, r: {W(T, SC.length(E.Item<T>, t), nodes, LK.fst(NS.ids(T, t), None{})) == t : List<&2, E.Item<T>>} & LK.lk(T, nodes, t, Some{i}, None{})) -> {W(T, SC.length(E.Item<T>, Con{E.Item{i, v}, t}), nodes, Some{i}) == Con{E.Item{i, v}, t} : List<&2, E.Item<T>>} & LK.lk(T, nodes, Con{E.Item{i, v}, t}, p, None{}):
  match r:
    case Tuple{+e, l}:
      (Equal.trans(List<&2, E.Item<T>>, LK.witems(T, 1n+SC.length(E.Item<T>, t), nodes, Some{i}, D.node(T, nodes, i)), LK.witems(T, 1n+SC.length(E.Item<T>, t), nodes, Some{i}, Some{D.N{v, p, LK.fst(NS.ids(T, t), None{})}}), Con{E.Item{i, v}, t},
         Equal.cong(Maybe<&2, D.Node<T>>, List<&2, E.Item<T>>, z => LK.witems(T, 1n+SC.length(E.Item<T>, t), nodes, Some{i}, z), D.node(T, nodes, i), Some{D.N{v, p, LK.fst(NS.ids(T, t), None{})}}, h1),
         Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => Con{E.Item{i, v}, z}, W(T, SC.length(E.Item<T>, t), nodes, LK.fst(NS.ids(T, t), None{})), t, e)),
       (h1, l))

def walk2(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +p: Maybe<&2, Nat>, h: LK.lk(T, nodes, xs, p, None{})) -> {W(T, SC.length(E.Item<T>, xs), nodes, LK.fst(NS.ids(T, xs), None{})) == xs : List<&2, E.Item<T>>} & LK.lk(T, nodes, xs, p, None{}):
  match xs h:
    case Nil{} _:
      ({==}, {==})
    case Con{E.Item{+i, +v}, +t} Tuple{+h1, h2}:
      wcons(T, nodes, i, v, t, p, h1, walk2(T, nodes, t, Some{i}, h2))

def Closed(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, count: Nat, fresh: Nat, xs: List<&2, E.Item<T>>) -> Type:
  {W(T, count, nodes, head) == xs : List<&2, E.Item<T>>} & F.Good(T, nodes, head, tail, count, fresh, W(T, count, nodes, head))

def close2(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +xs: List<&2, E.Item<T>>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +eh: {head == LK.fst(NS.ids(T, xs), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, xs), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, xs) : Nat}, +d: {LK.dist(NS.ids(T, xs)) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, xs)) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, xs), fresh) == True{} : Bool}, r: {W(T, SC.length(E.Item<T>, xs), nodes, LK.fst(NS.ids(T, xs), None{})) == xs : List<&2, E.Item<T>>} & LK.lk(T, nodes, xs, None{}, None{})) -> Closed(T, nodes, head, tail, count, fresh, xs):
  match r:
    case Tuple{+w, l}:
      +w2 = Equal.trans(List<&2, E.Item<T>>, W(T, count, nodes, head), W(T, SC.length(E.Item<T>, xs), nodes, head), xs,
        Equal.cong(Nat, List<&2, E.Item<T>>, z => W(T, z, nodes, head), count, SC.length(E.Item<T>, xs), ec),
        Equal.trans(List<&2, E.Item<T>>, W(T, SC.length(E.Item<T>, xs), nodes, head), W(T, SC.length(E.Item<T>, xs), nodes, LK.fst(NS.ids(T, xs), None{})), xs,
          Equal.cong(Maybe<&2, Nat>, List<&2, E.Item<T>>, z => W(T, SC.length(E.Item<T>, xs), nodes, z), head, LK.fst(NS.ids(T, xs), None{}), eh), w))
      (w2, L.subst(List<&2, E.Item<T>>, z => F.Good(T, nodes, head, tail, count, fresh, z), xs, W(T, count, nodes, head), Equal.sym(List<&2, E.Item<T>>, W(T, count, nodes, head), xs, w2), (g, (l, (eh, (et, (ec, (d, (a, lt)))))))))

def close(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +xs: List<&2, E.Item<T>>, G: F.Good(T, nodes, head, tail, count, fresh, xs)) -> Closed(T, nodes, head, tail, count, fresh, xs):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      close2(T, nodes, head, tail, count, fresh, xs, g, eh, et, ec, d, a, lt, walk2(T, nodes, xs, None{}, l))

def Fin(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, xs: List<&2, E.Item<T>>, o: E.Obs<T>) -> Type:
  {view1(T, (D.DL{tag, fresh, count, head, tail, nodes}, o)) == (DS.DM{tag, fresh, xs}, o) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})

def fin2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +o: E.Obs<T>, r: Closed(T, nodes, head, tail, count, fresh, xs)) -> Fin(T, tag, fresh, count, head, tail, nodes, xs, o):
  match r:
    case Tuple{+w, g2}:
      (Equal.cong(List<&2, E.Item<T>>, DS.Model<T> & E.Obs<T>, z => (DS.DM{tag, fresh, z}, o), W(T, count, nodes, head), xs, w), g2)

# A Good state for the sequence xs has that sequence as its abstraction.
def fin(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +xs: List<&2, E.Item<T>>, +o: E.Obs<T>, G: F.Good(T, nodes, head, tail, count, fresh, xs)) -> Fin(T, tag, fresh, count, head, tail, nodes, xs, o):
  fin2(T, tag, fresh, count, head, tail, nodes, xs, o, close(T, nodes, head, tail, count, fresh, xs, G))

# ---- the invariant with the link run split in two ----

def SG(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, count: Nat, fresh: Nat, P: List<&2, E.Item<T>>, Q: List<&2, E.Item<T>>) -> Type:
  {NS.ninv(T, nodes) == True{} : Bool} & (LK.lk(T, nodes, P, None{}, LK.fst(NS.ids(T, Q), None{})) & (LK.lk(T, nodes, Q, LK.lst(NS.ids(T, P), None{}), None{}) & ({head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>} & ({tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>} & ({count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)) : Nat} & ({LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool} & ({NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool} & {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Q)), fresh) == True{} : Bool})))))))

def mk_sg2(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Q)), fresh) == True{} : Bool}, sp: LK.Split(T, nodes, P, Q, None{}, None{})) -> SG(T, nodes, head, tail, count, fresh, P, Q):
  match sp:
    case Tuple{lp, lq}:
      (g, (lp, (lq, (eh, (et, (ec, (d, (a, lt))))))))

def mk_sg(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, G: F.Good(T, nodes, head, tail, count, fresh, SC.append(E.Item<T>, P, Q))) -> SG(T, nodes, head, tail, count, fresh, P, Q):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      mk_sg2(T, nodes, head, tail, count, fresh, P, Q, g, eh, et, ec, d, a, lt, LK.split(T, nodes, P, Q, None{}, None{}, l))

def link_sg(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, +x: T, s: SG(T, nodes, head, tail, count, fresh, P, Q)) -> F.Good(T, D.link(T, nodes, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{}), fresh, x), D.end_link(LK.lst(NS.ids(T, P), None{}), fresh, head), D.end_link(LK.fst(NS.ids(T, Q), None{}), fresh, tail), 1n+count, 1n+fresh, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})):
  match s:
    case Tuple{g, Tuple{lp, Tuple{lq, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}}:
      K.link_core(T, nodes, head, tail, count, fresh, P, Q, x, g, lp, lq, eh, et, ec, d, a, lt)

# ---- operations without handles ----

def len_ok2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +g: {NS.ninv(T, nodes) == True{} : Bool}, l: LK.lk(T, nodes, W(T, count, nodes, head), None{}, None{}), +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Length{}):
  (Equal.cong(Nat, DS.Model<T> & E.Obs<T>, z => (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONat{z}), count, SC.length(E.Item<T>, W(T, count, nodes, head)), ec),
   (g, (l, (eh, (et, (ec, (d, (a, lt))))))))

def len_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Length{}):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      len_ok2(T, tag, fresh, count, head, tail, nodes, g, l, eh, et, ec, d, a, lt)

def vals_walk_c(-T: Data, +f: Nat, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, m: Maybe<&2, D.Node<T>>, +em: {D.node(T, nodes, i) == m : Maybe<&2, D.Node<T>>}, ih: @+c: Maybe<&2, Nat> -> {D.walkv(T, f, nodes, D.nodeM(T, nodes, c)) == DS.vals(T, W(T, f, nodes, c)) : List<&2, T>}) -> {D.walkv(T, 1n+f, nodes, D.node(T, nodes, i)) == DS.vals(T, LK.witems(T, 1n+f, nodes, Some{i}, D.node(T, nodes, i))) : List<&2, T>}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, em) : {D.walkv(T, 1n+f, nodes, _) == DS.vals(T, LK.witems(T, 1n+f, nodes, Some{i}, _)) : List<&2, T>}
      {==}
    case Some{D.N{+v, +p, +n}}:
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), Some{D.N{v, p, n}}, em) : {D.walkv(T, 1n+f, nodes, _) == DS.vals(T, LK.witems(T, 1n+f, nodes, Some{i}, _)) : List<&2, T>}
      Equal.cong(List<&2, T>, List<&2, T>, z => Con{v, z}, D.walkv(T, f, nodes, D.nodeM(T, nodes, n)), DS.vals(T, W(T, f, nodes, n)), ih(n))

# to_list reads the values of the walked sequence.
def vals_walk(-T: Data, +f: Nat, +nodes: B.OrdMap<Nat, D.Node<T>>, +c: Maybe<&2, Nat>) -> {D.walkv(T, f, nodes, D.nodeM(T, nodes, c)) == DS.vals(T, W(T, f, nodes, c)) : List<&2, T>}:
  match f c:
    case 0n _:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+ +g Some{+i}:
      vals_walk_c(T, g, nodes, i, D.node(T, nodes, i), {==}, c2 => vals_walk(T, g, nodes, c2))

def pf_ok2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +x: T, +g: {NS.ninv(T, nodes) == True{} : Bool}, l: LK.lk(T, nodes, W(T, count, nodes, head), None{}, None{}), +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.PushFront{x}):
  +Wx = W(T, count, nodes, head)
  fin(T, tag, 1n+fresh, 1n+count, D.end_link(None{}, fresh, head), D.end_link(head, fresh, tail), D.link(T, nodes, None{}, head, fresh, x), Con{E.Item{fresh, x}, Wx}, E.OHandle{E.H{tag, fresh}},
    L.subst(Maybe<&2, Nat>, z => F.Good(T, D.link(T, nodes, None{}, z, fresh, x), D.end_link(None{}, fresh, head), D.end_link(z, fresh, tail), 1n+count, 1n+fresh, Con{E.Item{fresh, x}, Wx}), LK.fst(NS.ids(T, Wx), None{}), head, Equal.sym(Maybe<&2, Nat>, head, LK.fst(NS.ids(T, Wx), None{}), eh),
      K.link_core(T, nodes, head, tail, count, fresh, Nil{}, Wx, x, g, {==}, l, eh, et, ec, d, a, lt)))

def pf_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +x: T, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.PushFront{x}):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      pf_ok2(T, tag, fresh, count, head, tail, nodes, x, g, l, eh, et, ec, d, a, lt)

def pb_ok2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +x: T, +g: {NS.ninv(T, nodes) == True{} : Bool}, l: LK.lk(T, nodes, W(T, count, nodes, head), None{}, None{}), +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.PushBack{x}):
  +Wx = W(T, count, nodes, head)
  +en = Equal.sym(List<&2, E.Item<T>>, SC.append(E.Item<T>, Wx, Nil{}), Wx, LL.append_nil(E.Item<T>, Wx))
  G2 = {(g, (L.subst(List<&2, E.Item<T>>, z => LK.lk(T, nodes, z, None{}, None{}), Wx, SC.append(E.Item<T>, Wx, Nil{}), en, l),
           (L.subst(List<&2, E.Item<T>>, z => {head == LK.fst(NS.ids(T, z), None{}) : Maybe<&2, Nat>}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, eh),
            (L.subst(List<&2, E.Item<T>>, z => {tail == LK.lst(NS.ids(T, z), None{}) : Maybe<&2, Nat>}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, et),
             (L.subst(List<&2, E.Item<T>>, z => {count == SC.length(E.Item<T>, z) : Nat}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, ec),
              (L.subst(List<&2, E.Item<T>>, z => {LK.dist(NS.ids(T, z)) == True{} : Bool}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, d),
               (L.subst(List<&2, E.Item<T>>, z => {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, z)) == True{} : Bool}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, a),
                L.subst(List<&2, E.Item<T>>, z => {F.allLt(NS.ids(T, z), fresh) == True{} : Bool}, Wx, SC.append(E.Item<T>, Wx, Nil{}), en, lt))))))))
         : F.Good(T, nodes, head, tail, count, fresh, SC.append(E.Item<T>, Wx, Nil{}))}
  fin(T, tag, 1n+fresh, 1n+count, D.end_link(tail, fresh, head), D.end_link(None{}, fresh, tail), D.link(T, nodes, tail, None{}, fresh, x), SC.append(E.Item<T>, Wx, Con{E.Item{fresh, x}, Nil{}}), E.OHandle{E.H{tag, fresh}},
    L.subst(Maybe<&2, Nat>, z => F.Good(T, D.link(T, nodes, z, None{}, fresh, x), D.end_link(z, fresh, head), D.end_link(None{}, fresh, tail), 1n+count, 1n+fresh, SC.append(E.Item<T>, Wx, Con{E.Item{fresh, x}, Nil{}})), LK.lst(NS.ids(T, Wx), None{}), tail, Equal.sym(Maybe<&2, Nat>, tail, LK.lst(NS.ids(T, Wx), None{}), et),
      link_sg(T, nodes, head, tail, count, fresh, Wx, Nil{}, x, mk_sg(T, nodes, head, tail, count, fresh, Wx, Nil{}, G2))))

def pb_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +x: T, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.PushBack{x}):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      pb_ok2(T, tag, fresh, count, head, tail, nodes, x, g, l, eh, et, ec, d, a, lt)

# ---- looking up a handle's node through the cut ----

def ids_nil(-T: Data, +P: List<&2, E.Item<T>>) -> {NS.ids(T, SC.append(E.Item<T>, P, Nil{})) == NS.ids(T, P) : List<&2, Nat>}:
  Equal.cong(List<&2, E.Item<T>>, List<&2, Nat>, z => NS.ids(T, z), SC.append(E.Item<T>, P, Nil{}), P, LL.append_nil(E.Item<T>, P))

def absent2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +P: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, Nil{}) : List<&2, E.Item<T>>}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +g: {NS.ninv(T, nodes) == True{} : Bool}, l: LK.lk(T, nodes, W(T, count, nodes, head), None{}, None{}), +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}) -> {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes}):
  +m = L.subst(List<&2, Nat>, z => {NS.mem(i, z) == False{} : Bool}, NS.ids(T, P), NS.ids(T, W(T, count, nodes, head)), Equal.sym(List<&2, Nat>, NS.ids(T, W(T, count, nodes, head)), NS.ids(T, P), Equal.trans(List<&2, Nat>, NS.ids(T, W(T, count, nodes, head)), NS.ids(T, SC.append(E.Item<T>, P, Nil{})), NS.ids(T, P), Equal.cong(List<&2, E.Item<T>>, List<&2, Nat>, z => NS.ids(T, z), W(T, count, nodes, head), SC.append(E.Item<T>, P, Nil{}), ew), ids_nil(T, P))), mP)
  (NS.node_absent(T, nodes, i, NS.ids(T, W(T, count, nodes, head)), g, a, m), (g, (l, (eh, (et, (ec, (d, (a, lt))))))))

# An id not before the (empty) cut has no node.
def absent(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +P: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, Nil{}) : List<&2, E.Item<T>>}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes}):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      absent2(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, g, l, eh, et, ec, d, a, lt)

def Peek(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, P: List<&2, E.Item<T>>, j: Nat, v: T, Q: List<&2, E.Item<T>>) -> Type:
  {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})

def peek3(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}) : List<&2, E.Item<T>>}, +g: {NS.ninv(T, nodes) == True{} : Bool}, +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}, lp: LK.lk(T, nodes, P, None{}, Some{j}), +h1: {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>}, lq: LK.lk(T, nodes, Q, Some{j}, None{})) -> Peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q):
  (h1, (g, (L.subst(List<&2, E.Item<T>>, z => LK.lk(T, nodes, z, None{}, None{}), SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}), W(T, count, nodes, head), Equal.sym(List<&2, E.Item<T>>, W(T, count, nodes, head), SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}), ew), LK.join(T, nodes, P, Con{E.Item{j, v}, Q}, None{}, None{}, lp, (h1, lq))), (eh, (et, (ec, (d, (a, lt))))))))

def peek2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}) : List<&2, E.Item<T>>}, +g: {NS.ninv(T, nodes) == True{} : Bool}, +eh: {head == LK.fst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, W(T, count, nodes, head)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, W(T, count, nodes, head)) : Nat}, +d: {LK.dist(NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, W(T, count, nodes, head))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, W(T, count, nodes, head)), fresh) == True{} : Bool}, sp: LK.Split(T, nodes, P, Con{E.Item{j, v}, Q}, None{}, None{})) -> Peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q):
  match sp:
    case Tuple{lp, Tuple{h1, lq}}:
      peek3(T, tag, fresh, count, head, tail, nodes, P, j, v, Q, ew, g, eh, et, ec, d, a, lt, lp, h1, lq)

# The node of an id at the head of the cut, with the invariant kept.
def peek(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> Peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q):
  match G:
    case Tuple{g, Tuple{l, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}:
      peek2(T, tag, fresh, count, head, tail, nodes, P, j, v, Q, ew, g, eh, et, ec, d, a, lt, LK.split(T, nodes, P, Con{E.Item{j, v}, Q}, None{}, None{}, L.subst(List<&2, E.Item<T>>, z => LK.lk(T, nodes, z, None{}, None{}), W(T, count, nodes, head), SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}), ew, l)))

def handle_eq(+tag: Nat, +m: Maybe<&2, Nat>) -> {D.handle(tag, m) == DS.handle(tag, m) : Maybe<&2, E.Handle>}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      {==}

# ---- get ----

def GetGoal(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, l: Nat, i: Nat, r: List<&2, E.Item<T>>) -> Type:
  {view1(T, D.step(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Get{E.H{l, i}})) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, Nat.is_eq(l, tag), C.gets(T, r))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})

def get_nil(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +es: {Nat.is_eq(l, tag) == True{} : Bool}, pr: {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> GetGoal(T, tag, fresh, count, head, tail, nodes, l, i, Nil{}):
  match pr:
    case Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, _, D.node(T, nodes, i))}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, _, None{})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, True{}, _)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, True{}, None{})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, g2)

def get_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, pr: Peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q)) -> GetGoal(T, tag, fresh, count, head, tail, nodes, l, i, Con{E.Item{j, v}, Q}):
  match pr:
    case Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, _, D.node(T, nodes, i))}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, _, Some{v})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %ej : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, True{}, D.node(T, nodes, _))}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, True{}, Some{v})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, True{}, _)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, True{}, Some{v})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, g2)

def get_core(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, same: Bool, +es: {Nat.is_eq(l, tag) == same : Bool}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +so: {C.sufok(T, r, i) == True{} : Bool}, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> GetGoal(T, tag, fresh, count, head, tail, nodes, l, i, r):
  match r same:
    case Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, _, D.node(T, nodes, i))}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, _, None{})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case Nil{} True{}:
      get_nil(T, tag, fresh, count, head, tail, nodes, l, i, es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{D.value(T, _, D.node(T, nodes, i))}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, _, Some{v})}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case Con{E.Item{+j, +v}, +Q} True{}:
      get_con(T, tag, fresh, count, head, tail, nodes, l, i, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q, ew, G))

def get_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Get{E.H{l, i}}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {view1(T, D.step(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Get{E.H{l, i}})) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OVal{DS.value(T, Nat.is_eq(l, tag), _)}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
  get_core(T, tag, fresh, count, head, tail, nodes, l, i, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), G)

# ---- next / prev ----

def NbrGoal(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, l: Nat, i: Nat, r: List<&2, E.Item<T>>, m: Maybe<&2, Nat>) -> Type:
  {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, after, Nat.is_eq(l, tag), D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, Nat.is_eq(l, tag), C.gets(T, r)), DS.handle(tag, m))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})

def nbr_nil(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, +l: Nat, +i: Nat, +m: Maybe<&2, Nat>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, pr: {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> NbrGoal(T, tag, fresh, count, head, tail, nodes, after, l, i, Nil{}, m):
  match after pr:
    case True{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, None{}), DS.handle(tag, m))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, True{}, _, tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, None{}), DS.handle(tag, m))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, g2)
    case False{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, None{}), DS.handle(tag, m))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, True{}, _, tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, None{}), DS.handle(tag, m))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, g2)

def nbr_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, pr: Peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q)) -> NbrGoal(T, tag, fresh, count, head, tail, nodes, after, l, i, Con{E.Item{j, v}, Q}, DS.pickm(after, LK.fst(NS.ids(T, Q), None{}), LK.lst(NS.ids(T, P), None{}))):
  match after pr:
    case True{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, Some{v}), DS.handle(tag, LK.fst(NS.ids(T, Q), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %ej : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, True{}, D.node(T, nodes, _), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, Some{v}), DS.handle(tag, LK.fst(NS.ids(T, Q), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, True{}, _, tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, Some{v}), DS.handle(tag, LK.fst(NS.ids(T, Q), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      (Equal.cong(Maybe<&2, E.Handle>, DS.Model<T> & E.Obs<T>, z => (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{Done{z}}), D.handle(tag, LK.fst(NS.ids(T, Q), None{})), DS.handle(tag, LK.fst(NS.ids(T, Q), None{})), handle_eq(tag, LK.fst(NS.ids(T, Q), None{}))), g2)
    case False{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, Some{v}), DS.handle(tag, LK.lst(NS.ids(T, P), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %ej : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, True{}, D.node(T, nodes, _), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, Some{v}), DS.handle(tag, LK.lst(NS.ids(T, P), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}}, e) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, True{}, _, tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, True{}, Some{v}), DS.handle(tag, LK.lst(NS.ids(T, P), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      (Equal.cong(Maybe<&2, E.Handle>, DS.Model<T> & E.Obs<T>, z => (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{Done{z}}), D.handle(tag, LK.lst(NS.ids(T, P), None{})), DS.handle(tag, LK.lst(NS.ids(T, P), None{})), handle_eq(tag, LK.lst(NS.ids(T, P), None{}))), g2)

# The neighbour the specification reports, through the cut.
def nsel(-T: Data, after: Bool, r: List<&2, E.Item<T>>, +a: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match after:
    case True{}:
      C.nxs(T, r)
    case False{}:
      C.pvs(T, r, a)

def nbr_core(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, same: Bool, +es: {Nat.is_eq(l, tag) == same : Bool}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +so: {C.sufok(T, r, i) == True{} : Bool}, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> NbrGoal(T, tag, fresh, count, head, tail, nodes, after, l, i, r, nsel(T, after, r, LK.lst(NS.ids(T, P), None{}))):
  match after r same:
    case True{} Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, None{}), DS.handle(tag, None{}))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case False{} Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, None{}), DS.handle(tag, None{}))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case True{} Nil{} True{}:
      nbr_nil(T, tag, fresh, count, head, tail, nodes, True{}, l, i, None{}, es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case False{} Nil{} True{}:
      nbr_nil(T, tag, fresh, count, head, tail, nodes, False{}, l, i, None{}, es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case True{} Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, Some{v}), DS.handle(tag, LK.fst(NS.ids(T, Q), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case False{} Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, _, D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, _, Some{v}), DS.handle(tag, LK.lst(NS.ids(T, P), None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
      ({==}, G)
    case True{} Con{E.Item{+j, +v}, +Q} True{}:
      nbr_con(T, tag, fresh, count, head, tail, nodes, True{}, l, i, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q, ew, G))
    case False{} Con{E.Item{+j, +v}, +Q} True{}:
      nbr_con(T, tag, fresh, count, head, tail, nodes, False{}, l, i, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), peek(T, tag, fresh, count, head, tail, nodes, P, j, v, Q, ew, G))

def next_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Next{E.H{l, i}}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, Nat.is_eq(l, tag), _), DS.handle(tag, DS.next_of(T, W(T, count, nodes, head), i)))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
  %Equal.sym(Maybe<&2, Nat>, DS.next_of(T, W(T, count, nodes, head), i), C.nxs(T, C.suf(T, W(T, count, nodes, head), i)), C.next_cut(T, W(T, count, nodes, head), i)) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, Nat.is_eq(l, tag), C.gets(T, C.suf(T, W(T, count, nodes, head), i))), DS.handle(tag, _))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
  nbr_core(T, tag, fresh, count, head, tail, nodes, True{}, l, i, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), G)

def prev_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Prev{E.H{l, i}}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, Nat.is_eq(l, tag), _), DS.handle(tag, DS.prev_of(T, W(T, count, nodes, head), i, None{})))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
  %Equal.sym(Maybe<&2, Nat>, DS.prev_of(T, W(T, count, nodes, head), i, None{}), C.pvs(T, C.suf(T, W(T, count, nodes, head), i), LK.lst(NS.ids(T, C.pre(T, W(T, count, nodes, head), i)), None{})), C.prev_cut(T, W(T, count, nodes, head), i, None{})) : {(DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{D.nbr(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag)}) == (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.ONbr{DS.nbr(DS.check(T, Nat.is_eq(l, tag), C.gets(T, C.suf(T, W(T, count, nodes, head), i))), DS.handle(tag, _))}) : DS.Model<T> & E.Obs<T>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})
  nbr_core(T, tag, fresh, count, head, tail, nodes, False{}, l, i, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), G)

# ---- set ----

def SetGoal(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, l: Nat, i: Nat, x: T, r: List<&2, E.Item<T>>) -> Type:
  {view1(T, D.obs_unit(T, D.set_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, Nat.is_eq(l, tag), C.gets(T, r)), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))

def set_nil(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +es: {Nat.is_eq(l, tag) == True{} : Bool}, pr: {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> SetGoal(T, tag, fresh, count, head, tail, nodes, l, i, x, Nil{}):
  match pr:
    case Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {view1(T, D.obs_unit(T, D.set_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, True{}, None{}), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, g2)

def set_con2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +esv: {DS.setv(T, W(T, count, nodes, head), i, x) == SC.append(E.Item<T>, P, C.svs(T, Con{E.Item{j, v}, Q}, x)) : List<&2, E.Item<T>>}, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{j}), +h1: {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>}, lkQ: LK.lk(T, nodes, Q, Some{j}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), fresh) == True{} : Bool}) -> SetGoal(T, tag, fresh, count, head, tail, nodes, l, i, x, Con{E.Item{j, v}, Q}):
  %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %Equal.sym(List<&2, E.Item<T>>, DS.setv(T, W(T, count, nodes, head), i, x), SC.append(E.Item<T>, P, C.svs(T, Con{E.Item{j, v}, Q}, x)), esv) : {view1(T, D.obs_unit(T, D.set_checked(T, True{}, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == (DS.DM{tag, fresh, _}, E.OUnit{Done{Unit{}}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, True{}, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %ej : {view1(T, D.obs_unit(T, D.set_checked(T, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))) == (DS.DM{tag, fresh, SC.append(E.Item<T>, P, Con{E.Item{j, x}, Q})}, E.OUnit{Done{Unit{}}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))))
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}}, h1) : {view1(T, D.obs_unit(T, D.set_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, j, x))) == (DS.DM{tag, fresh, SC.append(E.Item<T>, P, Con{E.Item{j, x}, Q})}, E.OUnit{Done{Unit{}}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, j, x))))
  fin(T, tag, fresh, count, head, tail, D.put(T, nodes, j, D.N{x, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}), SC.append(E.Item<T>, P, Con{E.Item{j, x}, Q}), E.OUnit{Done{Unit{}}},
    K.set_core(T, nodes, head, tail, count, fresh, P, j, v, Q, x, g, lkP, lkQ, eh, et, ec, d, a, lt))

def set_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +esv: {DS.setv(T, W(T, count, nodes, head), i, x) == SC.append(E.Item<T>, P, C.svs(T, Con{E.Item{j, v}, Q}, x)) : List<&2, E.Item<T>>}, sg: SG(T, nodes, head, tail, count, fresh, P, Con{E.Item{j, v}, Q})) -> SetGoal(T, tag, fresh, count, head, tail, nodes, l, i, x, Con{E.Item{j, v}, Q}):
  match sg:
    case Tuple{g, Tuple{lkP, Tuple{Tuple{h1, lkQ}, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}}:
      set_con2(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, ej, esv, g, lkP, h1, lkQ, eh, et, ec, d, a, lt)

def to_sg(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +P: List<&2, E.Item<T>>, +r: List<&2, E.Item<T>>, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> SG(T, nodes, head, tail, count, fresh, P, r):
  mk_sg(T, nodes, head, tail, count, fresh, P, r, L.subst(List<&2, E.Item<T>>, z => F.Good(T, nodes, head, tail, count, fresh, z), W(T, count, nodes, head), SC.append(E.Item<T>, P, r), ew, G))

def set_core_op(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, same: Bool, +es: {Nat.is_eq(l, tag) == same : Bool}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +so: {C.sufok(T, r, i) == True{} : Bool}, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, +esv: {DS.setv(T, W(T, count, nodes, head), i, x) == SC.append(E.Item<T>, P, C.svs(T, r, x)) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> SetGoal(T, tag, fresh, count, head, tail, nodes, l, i, x, r):
  match r same:
    case Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case Nil{} True{}:
      set_nil(T, tag, fresh, count, head, tail, nodes, l, i, x, es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case Con{E.Item{+j, +v}, +Q} True{}:
      set_con(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), esv, to_sg(T, tag, fresh, count, head, tail, nodes, P, Con{E.Item{j, v}, Q}, ew, G))

def set_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Set{E.H{l, i}, x}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {view1(T, D.obs_unit(T, D.set_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.set_at(T, DS.check(T, Nat.is_eq(l, tag), _), tag, fresh, W(T, count, nodes, head), i, x) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_unit(T, D.set_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  set_core_op(T, tag, fresh, count, head, tail, nodes, l, i, x, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), C.setv_cut(T, W(T, count, nodes, head), i, x), G)

# ---- remove ----

def RmGoal(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, l: Nat, i: Nat, r: List<&2, E.Item<T>>) -> Type:
  {view1(T, D.obs_val(T, D.remove_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, Nat.is_eq(l, tag), C.gets(T, r), tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))

def rm_nil(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +es: {Nat.is_eq(l, tag) == True{} : Bool}, pr: {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> RmGoal(T, tag, fresh, count, head, tail, nodes, l, i, Nil{}):
  match pr:
    case Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, _, None{}, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {view1(T, D.obs_val(T, D.remove_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, True{}, None{}, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, i))))
      ({==}, g2)

def rm_con2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +edl: {DS.del(T, W(T, count, nodes, head), i) == SC.append(E.Item<T>, P, C.tl(T, Con{E.Item{j, v}, Q})) : List<&2, E.Item<T>>}, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{j}), +h1: {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>}, lkQ: LK.lk(T, nodes, Q, Some{j}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), fresh) == True{} : Bool}) -> RmGoal(T, tag, fresh, count, head, tail, nodes, l, i, Con{E.Item{j, v}, Q}):
  +a0 = LK.lst(NS.ids(T, P), None{})
  +b0 = LK.fst(NS.ids(T, Q), None{})
  %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, _, Some{v}, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
  %Equal.sym(List<&2, E.Item<T>>, DS.del(T, W(T, count, nodes, head), i), SC.append(E.Item<T>, P, C.tl(T, Con{E.Item{j, v}, Q})), edl) : {view1(T, D.obs_val(T, D.remove_checked(T, True{}, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == (DS.DM{tag, fresh, _}, E.OVal{Done{v}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, True{}, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
  %ej : {view1(T, D.obs_val(T, D.remove_checked(T, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _))) == (DS.DM{tag, fresh, SC.append(E.Item<T>, P, Q)}, E.OVal{Done{v}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _))))
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, a0, b0}}, h1) : {view1(T, D.obs_val(T, D.remove_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, j))) == (DS.DM{tag, fresh, SC.append(E.Item<T>, P, Q)}, E.OVal{Done{v}}) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, True{}, _, tag, fresh, count, head, tail, nodes, j))))
  fin(T, tag, fresh, Nat.sub(count, 1n), D.end_unlink(a0, b0, head), D.end_unlink(b0, a0, tail), D.unlink(T, nodes, j, a0, b0), SC.append(E.Item<T>, P, Q), E.OVal{Done{v}},
    K.unlink_core(T, nodes, head, tail, count, fresh, P, j, v, Q, g, lkP, lkQ, eh, et, ec, d, a, lt))

def rm_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +edl: {DS.del(T, W(T, count, nodes, head), i) == SC.append(E.Item<T>, P, C.tl(T, Con{E.Item{j, v}, Q})) : List<&2, E.Item<T>>}, sg: SG(T, nodes, head, tail, count, fresh, P, Con{E.Item{j, v}, Q})) -> RmGoal(T, tag, fresh, count, head, tail, nodes, l, i, Con{E.Item{j, v}, Q}):
  match sg:
    case Tuple{g, Tuple{lkP, Tuple{Tuple{h1, lkQ}, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}}:
      rm_con2(T, tag, fresh, count, head, tail, nodes, l, i, P, j, v, Q, es, ej, edl, g, lkP, h1, lkQ, eh, et, ec, d, a, lt)

def rm_core(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, same: Bool, +es: {Nat.is_eq(l, tag) == same : Bool}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +so: {C.sufok(T, r, i) == True{} : Bool}, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, +edl: {DS.del(T, W(T, count, nodes, head), i) == SC.append(E.Item<T>, P, C.tl(T, r)) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> RmGoal(T, tag, fresh, count, head, tail, nodes, l, i, r):
  match r same:
    case Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, _, None{}, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
      ({==}, G)
    case Nil{} True{}:
      rm_nil(T, tag, fresh, count, head, tail, nodes, l, i, es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, _, Some{v}, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
      ({==}, G)
    case Con{E.Item{+j, +v}, +Q} True{}:
      rm_con(T, tag, fresh, count, head, tail, nodes, l, i, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), edl, to_sg(T, tag, fresh, count, head, tail, nodes, P, Con{E.Item{j, v}, Q}, ew, G))

def rm_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.Remove{E.H{l, i}}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {view1(T, D.obs_val(T, D.remove_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))) == DS.remove_at(T, Nat.is_eq(l, tag), _, tag, fresh, W(T, count, nodes, head), i) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_val(T, D.remove_checked(T, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i))))
  rm_core(T, tag, fresh, count, head, tail, nodes, l, i, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), C.del_cut(T, W(T, count, nodes, head), i), G)

# ---- insert before / after ----

def InsGoal(-T: Data, tag: Nat, fresh: Nat, count: Nat, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, l: Nat, i: Nat, x: T, r: List<&2, E.Item<T>>, ys: List<&2, E.Item<T>>) -> Type:
  {view1(T, D.obs_insert(T, D.insert_checked(T, after, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, Nat.is_eq(l, tag), C.gets(T, r)), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, after, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))

def ins_nil(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, +l: Nat, +i: Nat, +x: T, +ys: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, pr: {D.node(T, nodes, i) == None{} : Maybe<&2, D.Node<T>>} & Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> InsGoal(T, tag, fresh, count, head, tail, nodes, after, l, i, x, Nil{}, ys):
  match after pr:
    case True{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, True{}, _, tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, True{}, None{}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, True{}, _, tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, g2)
    case False{} Tuple{+e, g2}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), None{}, e) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, True{}, _, tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, True{}, None{}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, True{}, _, tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, g2)

def ib_con2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{j}), +h1: {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>}, lkQ: LK.lk(T, nodes, Q, Some{j}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), fresh) == True{} : Bool}) -> InsGoal(T, tag, fresh, count, head, tail, nodes, False{}, l, i, x, Con{E.Item{j, v}, Q}, SC.append(E.Item<T>, P, C.ibs(T, Con{E.Item{j, v}, Q}, E.Item{fresh, x}))):
  +a0 = LK.lst(NS.ids(T, P), None{})
  +ys = SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Con{E.Item{j, v}, Q}})
  %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %ej : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))) == DS.insert_at(T, DS.check(T, True{}, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))))
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, a0, LK.fst(NS.ids(T, Q), None{})}}, h1) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, True{}, _, tag, fresh, count, head, tail, nodes, j, x))) == DS.insert_at(T, DS.check(T, True{}, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, True{}, _, tag, fresh, count, head, tail, nodes, j, x))))
  fin(T, tag, 1n+fresh, 1n+count, D.end_link(a0, fresh, head), D.end_link(Some{j}, fresh, tail), D.link(T, nodes, a0, Some{j}, fresh, x), ys, E.OInsert{Done{E.H{tag, fresh}}},
    K.link_core(T, nodes, head, tail, count, fresh, P, Con{E.Item{j, v}, Q}, x, g, lkP, (h1, lkQ), eh, et, ec, d, a, lt))

def ia_con2(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{j}), +h1: {D.node(T, nodes, j) == Some{D.N{v, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}} : Maybe<&2, D.Node<T>>}, lkQ: LK.lk(T, nodes, Q, Some{j}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, v}, Q})), fresh) == True{} : Bool}) -> InsGoal(T, tag, fresh, count, head, tail, nodes, True{}, l, i, x, Con{E.Item{j, v}, Q}, SC.append(E.Item<T>, P, C.ias(T, Con{E.Item{j, v}, Q}, E.Item{fresh, x}))):
  -IT = E.Item<T>
  -NL = List<&2, Nat>
  +b0 = LK.fst(NS.ids(T, Q), None{})
  +P1 = SC.append(IT, P, Con{E.Item{j, v}, Nil{}})
  +ys = SC.append(IT, P, Con{E.Item{j, v}, Con{E.Item{fresh, x}, Q}})
  +asc = Equal.sym(List<&2, E.Item<T>>, SC.append(IT, P1, Q), SC.append(IT, P, Con{E.Item{j, v}, Q}), LL.append_assoc(IT, P, Con{E.Item{j, v}, Nil{}}, Q))
  +asc2 = LL.append_assoc(IT, P, Con{E.Item{j, v}, Nil{}}, Con{E.Item{fresh, x}, Q})
  +el = Equal.trans(Maybe<&2, Nat>, LK.lst(NS.ids(T, P1), None{}), LK.lst(Con{j, Nil{}}, LK.lst(NS.ids(T, P), None{})), Some{j}, LK.lst_ids_app(T, P, Con{E.Item{j, v}, Nil{}}, None{}), {==})
  %Equal.sym(Bool, Nat.is_eq(l, tag), True{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %ej : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))) == DS.insert_at(T, DS.check(T, True{}, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, True{}, D.node(T, nodes, _), tag, fresh, count, head, tail, nodes, _, x))))
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, j), Some{D.N{v, LK.lst(NS.ids(T, P), None{}), b0}}, h1) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, True{}, _, tag, fresh, count, head, tail, nodes, j, x))) == DS.insert_at(T, DS.check(T, True{}, Some{v}), tag, fresh, W(T, count, nodes, head), ys) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, True{}, _, tag, fresh, count, head, tail, nodes, j, x))))
  fin(T, tag, 1n+fresh, 1n+count, D.end_link(Some{j}, fresh, head), D.end_link(b0, fresh, tail), D.link(T, nodes, Some{j}, b0, fresh, x), ys, E.OInsert{Done{E.H{tag, fresh}}},
    L.subst(List<&2, E.Item<T>>, z => F.Good(T, D.link(T, nodes, Some{j}, b0, fresh, x), D.end_link(Some{j}, fresh, head), D.end_link(b0, fresh, tail), 1n+count, 1n+fresh, z), SC.append(IT, P1, Con{E.Item{fresh, x}, Q}), ys, asc2,
      L.subst(Maybe<&2, Nat>, z => F.Good(T, D.link(T, nodes, z, b0, fresh, x), D.end_link(z, fresh, head), D.end_link(b0, fresh, tail), 1n+count, 1n+fresh, SC.append(IT, P1, Con{E.Item{fresh, x}, Q})), LK.lst(NS.ids(T, P1), None{}), Some{j}, el,
        K.link_core(T, nodes, head, tail, count, fresh, P1, Q, x, g,
          LK.join(T, nodes, P, Con{E.Item{j, v}, Nil{}}, None{}, b0, lkP, (h1, {==})),
          L.subst(Maybe<&2, Nat>, z => LK.lk(T, nodes, Q, z, None{}), Some{j}, LK.lst(NS.ids(T, P1), None{}), Equal.sym(Maybe<&2, Nat>, LK.lst(NS.ids(T, P1), None{}), Some{j}, el), lkQ),
          L.subst(List<&2, E.Item<T>>, z => {head == LK.fst(NS.ids(T, z), None{}) : Maybe<&2, Nat>}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, eh),
          L.subst(List<&2, E.Item<T>>, z => {tail == LK.lst(NS.ids(T, z), None{}) : Maybe<&2, Nat>}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, et),
          L.subst(List<&2, E.Item<T>>, z => {count == SC.length(IT, z) : Nat}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, ec),
          L.subst(List<&2, E.Item<T>>, z => {LK.dist(NS.ids(T, z)) == True{} : Bool}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, d),
          L.subst(List<&2, E.Item<T>>, z => {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, z)) == True{} : Bool}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, a),
          L.subst(List<&2, E.Item<T>>, z => {F.allLt(NS.ids(T, z), fresh) == True{} : Bool}, SC.append(IT, P, Con{E.Item{j, v}, Q}), SC.append(IT, P1, Q), asc, lt)))))

def ib_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, sg: SG(T, nodes, head, tail, count, fresh, P, Con{E.Item{j, v}, Q})) -> InsGoal(T, tag, fresh, count, head, tail, nodes, False{}, l, i, x, Con{E.Item{j, v}, Q}, SC.append(E.Item<T>, P, C.ibs(T, Con{E.Item{j, v}, Q}, E.Item{fresh, x}))):
  match sg:
    case Tuple{g, Tuple{lkP, Tuple{Tuple{h1, lkQ}, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}}:
      ib_con2(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, ej, g, lkP, h1, lkQ, eh, et, ec, d, a, lt)

def ia_con(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, +j: Nat, +v: T, +Q: List<&2, E.Item<T>>, +es: {Nat.is_eq(l, tag) == True{} : Bool}, +ej: {j == i : Nat}, sg: SG(T, nodes, head, tail, count, fresh, P, Con{E.Item{j, v}, Q})) -> InsGoal(T, tag, fresh, count, head, tail, nodes, True{}, l, i, x, Con{E.Item{j, v}, Q}, SC.append(E.Item<T>, P, C.ias(T, Con{E.Item{j, v}, Q}, E.Item{fresh, x}))):
  match sg:
    case Tuple{g, Tuple{lkP, Tuple{Tuple{h1, lkQ}, Tuple{eh, Tuple{et, Tuple{ec, Tuple{d, Tuple{a, lt}}}}}}}}:
      ia_con2(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, ej, g, lkP, h1, lkQ, eh, et, ec, d, a, lt)

def ins_sel(-T: Data, after: Bool, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, +it: E.Item<T>) -> List<&2, E.Item<T>>:
  match after:
    case True{}:
      SC.append(E.Item<T>, P, C.ias(T, r, it))
    case False{}:
      SC.append(E.Item<T>, P, C.ibs(T, r, it))

def ins_core(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, after: Bool, +l: Nat, +i: Nat, +x: T, +P: List<&2, E.Item<T>>, r: List<&2, E.Item<T>>, same: Bool, +es: {Nat.is_eq(l, tag) == same : Bool}, +mP: {NS.mem(i, NS.ids(T, P)) == False{} : Bool}, +so: {C.sufok(T, r, i) == True{} : Bool}, +ew: {W(T, count, nodes, head) == SC.append(E.Item<T>, P, r) : List<&2, E.Item<T>>}, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> InsGoal(T, tag, fresh, count, head, tail, nodes, after, l, i, x, r, ins_sel(T, after, P, r, E.Item{fresh, x})):
  match after r same:
    case True{} Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), SC.append(E.Item<T>, P, Nil{})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case False{} Nil{} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, None{}), tag, fresh, W(T, count, nodes, head), SC.append(E.Item<T>, P, Nil{})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case True{} Nil{} True{}:
      ins_nil(T, tag, fresh, count, head, tail, nodes, True{}, l, i, x, SC.append(E.Item<T>, P, Nil{}), es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case False{} Nil{} True{}:
      ins_nil(T, tag, fresh, count, head, tail, nodes, False{}, l, i, x, SC.append(E.Item<T>, P, Nil{}), es, absent(T, tag, fresh, count, head, tail, nodes, i, P, ew, mP, G))
    case True{} Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), SC.append(E.Item<T>, P, Con{E.Item{j, v}, Con{E.Item{fresh, x}, Q}})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case False{} Con{E.Item{+j, +v}, +Q} False{}:
      %Equal.sym(Bool, Nat.is_eq(l, tag), False{}, es) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, _, Some{v}), tag, fresh, W(T, count, nodes, head), SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Con{E.Item{j, v}, Q}})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, _, D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
      ({==}, G)
    case True{} Con{E.Item{+j, +v}, +Q} True{}:
      ia_con(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), to_sg(T, tag, fresh, count, head, tail, nodes, P, Con{E.Item{j, v}, Q}, ew, G))
    case False{} Con{E.Item{+j, +v}, +Q} True{}:
      ib_con(T, tag, fresh, count, head, tail, nodes, l, i, x, P, j, v, Q, es, N.eq_from_is_eq(j, i, so), to_sg(T, tag, fresh, count, head, tail, nodes, P, Con{E.Item{j, v}, Q}, ew, G))

def ib_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.InsertBefore{E.H{l, i}, x}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, Nat.is_eq(l, tag), _), tag, fresh, W(T, count, nodes, head), DS.ins_before(T, W(T, count, nodes, head), i, E.Item{fresh, x})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %Equal.sym(List<&2, E.Item<T>>, DS.ins_before(T, W(T, count, nodes, head), i, E.Item{fresh, x}), SC.append(E.Item<T>, C.pre(T, W(T, count, nodes, head), i), C.ibs(T, C.suf(T, W(T, count, nodes, head), i), E.Item{fresh, x})), C.ib_cut(T, W(T, count, nodes, head), i, E.Item{fresh, x})) : {view1(T, D.obs_insert(T, D.insert_checked(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, Nat.is_eq(l, tag), C.gets(T, C.suf(T, W(T, count, nodes, head), i))), tag, fresh, W(T, count, nodes, head), _) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, False{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  ins_core(T, tag, fresh, count, head, tail, nodes, False{}, l, i, x, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), G)

def ia_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, +l: Nat, +i: Nat, +x: T, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.InsertAfter{E.H{l, i}, x}):
  %Equal.sym(Maybe<&2, T>, DS.getv(T, W(T, count, nodes, head), i), C.gets(T, C.suf(T, W(T, count, nodes, head), i)), C.getv_cut(T, W(T, count, nodes, head), i)) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, Nat.is_eq(l, tag), _), tag, fresh, W(T, count, nodes, head), DS.ins_after(T, W(T, count, nodes, head), i, E.Item{fresh, x})) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  %Equal.sym(List<&2, E.Item<T>>, DS.ins_after(T, W(T, count, nodes, head), i, E.Item{fresh, x}), SC.append(E.Item<T>, C.pre(T, W(T, count, nodes, head), i), C.ias(T, C.suf(T, W(T, count, nodes, head), i), E.Item{fresh, x})), C.ia_cut(T, W(T, count, nodes, head), i, E.Item{fresh, x})) : {view1(T, D.obs_insert(T, D.insert_checked(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))) == DS.insert_at(T, DS.check(T, Nat.is_eq(l, tag), C.gets(T, C.suf(T, W(T, count, nodes, head), i))), tag, fresh, W(T, count, nodes, head), _) : DS.Model<T> & E.Obs<T>} & Inv(T, Pair.fst(D.DList<T>, E.Obs<T>, D.obs_insert(T, D.insert_checked(T, True{}, Nat.is_eq(l, tag), D.node(T, nodes, i), tag, fresh, count, head, tail, nodes, i, x))))
  ins_core(T, tag, fresh, count, head, tail, nodes, True{}, l, i, x, C.pre(T, W(T, count, nodes, head), i), C.suf(T, W(T, count, nodes, head), i), Nat.is_eq(l, tag), {==}, C.pre_nm(T, W(T, count, nodes, head), i), C.suf_ok(T, W(T, count, nodes, head), i), C.cut_app(T, W(T, count, nodes, head), i), G)

# ---- every operation ----

def to_list_ok(-T: Data, +tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>, G: Inv(T, D.DL{tag, fresh, count, head, tail, nodes})) -> StepOK(T, D.DL{tag, fresh, count, head, tail, nodes}, E.ToList{}):
  (Equal.cong(List<&2, T>, DS.Model<T> & E.Obs<T>, z => (DS.DM{tag, fresh, W(T, count, nodes, head)}, E.OList{z}), D.walkv(T, count, nodes, D.nodeM(T, nodes, head)), DS.vals(T, W(T, count, nodes, head)), vals_walk(T, count, nodes, head)), G)

def step_ok(-T: Data, +s: D.DList<T>, +op: E.Op<T>, G: Inv(T, s)) -> StepOK(T, s, op):
  match s op:
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Length{}:
      len_ok(T, tag, fresh, count, head, tail, nodes, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.PushFront{+x}:
      pf_ok(T, tag, fresh, count, head, tail, nodes, x, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.PushBack{+x}:
      pb_ok(T, tag, fresh, count, head, tail, nodes, x, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.InsertBefore{E.H{+l, +i}, +x}:
      ib_ok(T, tag, fresh, count, head, tail, nodes, l, i, x, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.InsertAfter{E.H{+l, +i}, +x}:
      ia_ok(T, tag, fresh, count, head, tail, nodes, l, i, x, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Remove{E.H{+l, +i}}:
      rm_ok(T, tag, fresh, count, head, tail, nodes, l, i, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Get{E.H{+l, +i}}:
      get_ok(T, tag, fresh, count, head, tail, nodes, l, i, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Set{E.H{+l, +i}, +x}:
      set_ok(T, tag, fresh, count, head, tail, nodes, l, i, x, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Next{E.H{+l, +i}}:
      next_ok(T, tag, fresh, count, head, tail, nodes, l, i, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.Prev{E.H{+l, +i}}:
      prev_ok(T, tag, fresh, count, head, tail, nodes, l, i, G)
    case D.DL{+tag, +fresh, +count, +head, +tail, +nodes} E.ToList{}:
      to_list_ok(T, tag, fresh, count, head, tail, nodes, G)

def new_abs(-T: Data, +tag: Nat) -> {abs(T, D.new(T, tag)) == DS.new(T, tag) : DS.Model<T>}:
  {==}

def new_inv(-T: Data, +tag: Nat) -> Inv(T, D.new(T, tag)):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))
