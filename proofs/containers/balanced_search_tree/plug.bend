import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./path.bend as P

# A path plugged with a subtree: the tree it leads through. Its ids are the
# ids before, the subtree's, and after; it links as the ghost says when the
# subtree does below the path's parent and the path's frames do.
# (source: tools/generators/tm_hand/plug.src)


def plug(c: List<&2, P.Fr>, t: ST.Tr) -> ST.Tr:
  match c:
    case Nil{}:
      t
    case Con{f, u}:
      match f:
        case P.FR{+p, +lft, s}:
          match lft:
            case True{}:
              plug(u, ST.TN{p, t, s})
            case False{}:
              plug(u, ST.TN{p, s, t})

def ids_plug(+c: List<&2, P.Fr>, +t: ST.Tr) -> {ST.ids(plug(c, t)) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>}:
  match c:
    case Nil{}:
      Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(t), Nil{}), ST.ids(t), LL.append_nil(Nat, ST.ids(t)))
    case Con{P.FR{+p, +lft, +s}, +u}:
      match lft:
        case True{}:
          Equal.trans(List<&2, Nat>, ST.ids(plug(u, ST.TN{p, t, s})), SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(ST.TN{p, t, s}), P.after(u))), SC.append(Nat, P.before(Con{P.FR{p, True{}, s}, u}), SC.append(Nat, ST.ids(t), P.after(Con{P.FR{p, True{}, s}, u}))), ids_plug(u, ST.TN{p, t, s}), P.ids_l(u, p, t, s))
        case False{}:
          Equal.trans(List<&2, Nat>, ST.ids(plug(u, ST.TN{p, s, t})), SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(ST.TN{p, s, t}), P.after(u))), SC.append(Nat, P.before(Con{P.FR{p, False{}, s}, u}), SC.append(Nat, ST.ids(t), P.after(Con{P.FR{p, False{}, s}, u}))), ids_plug(u, ST.TN{p, s, t}), P.ids_r(u, p, s, t))


# the plugged tree links when the subtree and the path do
def rep_plug(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +t: ST.Tr, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, +hc: {P.ctxok(~K, c, ST.rid(t), nl) == True{} : Bool}) -> {ST.rep(~K, plug(c, t), 0n, nl) == True{} : Bool}:
  match c:
    case Nil{}:
      hr
    case Con{P.FR{+p, +lft, +s}, +u}:
      match lft:
        case True{}:
          +hk = L.and_left(P.cok1(~K, P.FR{p, True{}, s}, ST.rid(t), P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
          +hu = L.and_right(P.cok1(~K, P.FR{p, True{}, s}, ST.rid(t), P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
          +h0 = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), ST.rep(~K, s, p, nl)), hk)
          +h12 = L.and_right(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), ST.rep(~K, s, p, nl)), hk)
          +hn = L.and_left(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), ST.rep(~K, s, p, nl), h12)
          +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), ST.rep(~K, s, p, nl), h12)
          rep_plug(~K, nl, u, ST.TN{p, t, s}, L.and_intro(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), Bool.and(ST.rep(~K, t, p, nl), ST.rep(~K, s, p, nl))), h0, L.and_intro(ST.is_node(K, ST.nd(K, nl, p), ST.rid(t), ST.rid(s), P.top(u)), Bool.and(ST.rep(~K, t, p, nl), ST.rep(~K, s, p, nl)), hn, L.and_intro(ST.rep(~K, t, p, nl), ST.rep(~K, s, p, nl), hr, hs))), hu)
        case False{}:
          +hk = L.and_left(P.cok1(~K, P.FR{p, False{}, s}, ST.rid(t), P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
          +hu = L.and_right(P.cok1(~K, P.FR{p, False{}, s}, ST.rid(t), P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
          +h0 = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), ST.rep(~K, s, p, nl)), hk)
          +h12 = L.and_right(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), ST.rep(~K, s, p, nl)), hk)
          +hn = L.and_left(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), ST.rep(~K, s, p, nl), h12)
          +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), ST.rep(~K, s, p, nl), h12)
          rep_plug(~K, nl, u, ST.TN{p, s, t}, L.and_intro(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), Bool.and(ST.rep(~K, s, p, nl), ST.rep(~K, t, p, nl))), h0, L.and_intro(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), ST.rid(t), P.top(u)), Bool.and(ST.rep(~K, s, p, nl), ST.rep(~K, t, p, nl)), hn, L.and_intro(ST.rep(~K, s, p, nl), ST.rep(~K, t, p, nl), hs, hr))), hu)
