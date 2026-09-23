import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/lists.bend as LS
import ./state.bend as ST
import ./prim.bend as PR

# Writes to the node list: a write leaves every other id's node as it was,
# so the links, entries and free chain of ids avoiding it; a recolouring
# write keeps every link and entry. (source: tools/generators/tm_hand/frame.src)


def or_f_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.true_false(h))
    case False{}:
      h

def or_f_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(h))
    case False{}:
      {==}

def wo_c(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +x: M.Node<K>, +j: Nat, +hne: {Nat.is_eq(i, j) == False{} : Bool}, +b: Bool) -> {ST.nth_or(M.Node<K>, ST.pk(List<&2, M.Node<K>>, b, SC.update(M.Node<K>, nl, i, x), nl), j, M.Free{0n}) == ST.nth_or(M.Node<K>, nl, j, M.Free{0n}) : M.Node<K>}:
  match b:
    case True{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, SC.update(M.Node<K>, nl, i, x), j, M.Free{0n}), PR.or_else(M.Node<K>, SC.nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), j), M.Free{0n}), PR.nth_or_nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), j, M.Free{0n})) : {_ == ST.nth_or(M.Node<K>, nl, j, M.Free{0n}) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, nl, j, M.Free{0n}), PR.or_else(M.Node<K>, SC.nth(M.Node<K>, nl, j), M.Free{0n}), PR.nth_or_nth(M.Node<K>, nl, j, M.Free{0n})) : {PR.or_else(M.Node<K>, SC.nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), j), M.Free{0n}) == _ : M.Node<K>}
      %Equal.sym(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), j), SC.nth(M.Node<K>, nl, j), LL.nth_update_other(M.Node<K>, nl, i, j, x, hne)) : {PR.or_else(M.Node<K>, _, M.Free{0n}) == PR.or_else(M.Node<K>, SC.nth(M.Node<K>, nl, j), M.Free{0n}) : M.Node<K>}
      {==}
    case False{}:
      {==}

# another id's node is unchanged by a write
def nd_wr_other(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +x: M.Node<K>, +j: Nat, +hne: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.nd(K, PR.wr_nl(K, nl, id, x), j) == ST.nd(K, nl, j) : M.Node<K>}:
  match id j:
    case 0n +j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+jj:
      wo_c(K, nl, i, x, jj, hne, Nat.is_lt(i, SC.length(M.Node<K>, nl)))

# the written id's node is the new one, in range
def nd_wr_same(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +x: M.Node<K>, +h: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {ST.nd(K, PR.wr_nl(K, nl, 1n+i, x), 1n+i) == x : M.Node<K>}:
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, nl)), True{}, h) : {ST.nth_or(M.Node<K>, ST.pk(List<&2, M.Node<K>>, _, SC.update(M.Node<K>, nl, i, x), nl), i, M.Free{0n}) == x : M.Node<K>}
  %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, SC.update(M.Node<K>, nl, i, x), i, M.Free{0n}), PR.or_else(M.Node<K>, SC.nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), i), M.Free{0n}), PR.nth_or_nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), i, M.Free{0n})) : {_ == x : M.Node<K>}
  %Equal.sym(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, SC.update(M.Node<K>, nl, i, x), i), Some{x}, LL.nth_update_same(M.Node<K>, nl, i, x, h)) : {PR.or_else(M.Node<K>, _, M.Free{0n}) == x : M.Node<K>}
  {==}

def ne_sym(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  N.is_eq_sym_false(a, b, h)


# splitting an absent id over a node's ids
def nm_node(+y: Nat, +i: Nat, +l: ST.Tr, +r: ST.Tr, +h: {HT.memn(y, ST.ids(ST.TN{i, l, r})) == False{} : Bool}) -> {Nat.is_eq(i, y) == False{} : Bool} & ({HT.memn(y, ST.ids(l)) == False{} : Bool} & {HT.memn(y, ST.ids(r)) == False{} : Bool}):
  +h2 = L.subst(Bool, z => {z == False{} : Bool}, HT.memn(y, SC.append(Nat, ST.ids(l), Con{i, ST.ids(r)})), Bool.or(HT.memn(y, ST.ids(l)), HT.memn(y, Con{i, ST.ids(r)})), LS.memn_app(y, ST.ids(l), Con{i, ST.ids(r)}), h)
  +h3 = or_f_r(HT.memn(y, ST.ids(l)), HT.memn(y, Con{i, ST.ids(r)}), h2)
  (or_f_l(Nat.is_eq(i, y), HT.memn(y, ST.ids(r)), h3), (or_f_l(HT.memn(y, ST.ids(l)), HT.memn(y, Con{i, ST.ids(r)}), h2), or_f_r(Nat.is_eq(i, y), HT.memn(y, ST.ids(r)), h3)))

def nm_cons(+y: Nat, +i: Nat, +t: List<&2, Nat>, +h: {HT.memn(y, Con{i, t}) == False{} : Bool}) -> {Nat.is_eq(i, y) == False{} : Bool} & {HT.memn(y, t) == False{} : Bool}:
  (or_f_l(Nat.is_eq(i, y), HT.memn(y, t), h), or_f_r(Nat.is_eq(i, y), HT.memn(y, t), h))


# a subtree avoiding the written id keeps its links
def rep_frame(~K: Data, +t: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +id: Nat, +x: M.Node<K>, +hn: {HT.memn(id, ST.ids(t)) == False{} : Bool}) -> {ST.rep(~K, t, p, PR.wr_nl(K, nl, id, x)) == ST.rep(~K, t, p, nl) : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +l, +r}:
      %Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, id, x), i), ST.nd(K, nl, i), nd_wr_other(K, nl, id, x, i, ne_sym(i, id, Pair.fst({Nat.is_eq(i, id) == False{} : Bool}, {HT.memn(id, ST.ids(l)) == False{} : Bool} & {HT.memn(id, ST.ids(r)) == False{} : Bool}, nm_node(id, i, l, r, hn))))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, _, ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, PR.wr_nl(K, nl, id, x)), ST.rep(~K, r, i, PR.wr_nl(K, nl, id, x))))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, l, i, PR.wr_nl(K, nl, id, x)), ST.rep(~K, l, i, nl), rep_frame(~K, l, i, nl, id, x, Pair.fst({HT.memn(id, ST.ids(l)) == False{} : Bool}, {HT.memn(id, ST.ids(r)) == False{} : Bool}, Pair.snd({Nat.is_eq(i, id) == False{} : Bool}, {HT.memn(id, ST.ids(l)) == False{} : Bool} & {HT.memn(id, ST.ids(r)) == False{} : Bool}, nm_node(id, i, l, r, hn))))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(_, ST.rep(~K, r, i, PR.wr_nl(K, nl, id, x))))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, r, i, PR.wr_nl(K, nl, id, x)), ST.rep(~K, r, i, nl), rep_frame(~K, r, i, nl, id, x, Pair.snd({HT.memn(id, ST.ids(l)) == False{} : Bool}, {HT.memn(id, ST.ids(r)) == False{} : Bool}, Pair.snd({Nat.is_eq(i, id) == False{} : Bool}, {HT.memn(id, ST.ids(l)) == False{} : Bool} & {HT.memn(id, ST.ids(r)) == False{} : Bool}, nm_node(id, i, l, r, hn))))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl), _))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      {==}


# entries of ids avoiding the written id are unchanged
def ents_frame(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +x: M.Node<K>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {ST.ents(~K, ~V, xs, PR.wr_nl(K, nl, id, x), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+i, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, id, x), i), ST.nd(K, nl, i), nd_wr_other(K, nl, id, x, i, ne_sym(i, id, Pair.fst({Nat.is_eq(i, id) == False{} : Bool}, {HT.memn(id, t) == False{} : Bool}, nm_cons(id, i, t, hn))))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, _, ST.pv(V, pl, i)), ST.ents(~K, ~V, t, PR.wr_nl(K, nl, id, x), pl)) == ST.ents(~K, ~V, Con{i, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, PR.wr_nl(K, nl, id, x), pl), ST.ents(~K, ~V, t, nl, pl), ents_frame(~K, ~V, t, nl, pl, id, x, Pair.snd({Nat.is_eq(i, id) == False{} : Bool}, {HT.memn(id, t) == False{} : Bool}, nm_cons(id, i, t, hn)))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), _) == ST.ents(~K, ~V, Con{i, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

# the free chain avoiding the written id is unchanged
def fll_frame(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +x: M.Node<K>, +hn: {HT.memn(id, fl) == False{} : Bool}) -> {ST.fll(~K, PR.wr_nl(K, nl, id, x), fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, id, x), f), ST.nd(K, nl, f), nd_wr_other(K, nl, id, x, f, ne_sym(f, id, Pair.fst({Nat.is_eq(f, id) == False{} : Bool}, {HT.memn(id, t) == False{} : Bool}, nm_cons(id, f, t, hn))))) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, PR.wr_nl(K, nl, id, x), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, PR.wr_nl(K, nl, id, x), t), ST.fll(~K, nl, t), fll_frame(~K, t, nl, id, x, Pair.snd({Nat.is_eq(f, id) == False{} : Bool}, {HT.memn(id, t) == False{} : Bool}, nm_cons(id, f, t, hn)))) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}
