import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ./prim.bend as PR
import ./frame.bend as FR
import ./agree.bend as AG
import ./ends.bend as EN

# A list grown by one slot, or rewritten at one: every other position reads
# as before, the slot reads the new value; so the entries, links and free
# chain of ids avoiding the slot are unchanged. (source: tools/generators/tm_hand/slot.src)


def nth_snoc_other(-X: Data, +xs: List<&2, X>, +x: X, +i: Nat, +dv: X, +h: {Nat.is_eq(i, SC.length(X, xs)) == False{} : Bool}) -> {ST.nth_or(X, SC.snoc(X, xs, x), i, dv) == ST.nth_or(X, xs, i, dv) : X}:
  match xs i:
    case Nil{} 0n:
      Empty.absurd({ST.nth_or(X, SC.snoc(X, Nil{}, x), 0n, dv) == ST.nth_or(X, Nil{}, 0n, dv) : X}, L.true_false(h))
    case Nil{} 1n+j:
      {==}
    case Con{+hd, +t} 0n:
      {==}
    case Con{+hd, +t} 1n+j:
      nth_snoc_other(X, t, x, j, dv, h)

def nth_snoc_same(-X: Data, +xs: List<&2, X>, +x: X, +dv: X) -> {ST.nth_or(X, SC.snoc(X, xs, x), SC.length(X, xs), dv) == x : X}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hd, +t}:
      nth_snoc_same(X, t, x, dv)

def nth_upd_c(-X: Data, +xs: List<&2, X>, +i: Nat, +x: X, +j: Nat, +dv: X, +hne: {Nat.is_eq(i, j) == False{} : Bool}, +b: Bool) -> {ST.nth_or(X, ST.pk(List<&2, X>, b, SC.update(X, xs, i, x), xs), j, dv) == ST.nth_or(X, xs, j, dv) : X}:
  match b:
    case True{}:
      %Equal.sym(X, ST.nth_or(X, SC.update(X, xs, i, x), j, dv), PR.or_else(X, SC.nth(X, SC.update(X, xs, i, x), j), dv), PR.nth_or_nth(X, SC.update(X, xs, i, x), j, dv)) : {_ == ST.nth_or(X, xs, j, dv) : X}
      %Equal.sym(X, ST.nth_or(X, xs, j, dv), PR.or_else(X, SC.nth(X, xs, j), dv), PR.nth_or_nth(X, xs, j, dv)) : {PR.or_else(X, SC.nth(X, SC.update(X, xs, i, x), j), dv) == _ : X}
      %Equal.sym(Maybe<&2, X>, SC.nth(X, SC.update(X, xs, i, x), j), SC.nth(X, xs, j), LL.nth_update_other(X, xs, i, j, x, hne)) : {PR.or_else(X, _, dv) == PR.or_else(X, SC.nth(X, xs, j), dv) : X}
      {==}
    case False{}:
      {==}

# ---- the node list ----


def nd_snoc_other(-K: Data, +nl: List<&2, M.Node<K>>, +x: M.Node<K>, +j: Nat, +h: {Nat.is_eq(j, 1n+SC.length(M.Node<K>, nl)) == False{} : Bool}) -> {ST.nd(K, SC.snoc(M.Node<K>, nl, x), j) == ST.nd(K, nl, j) : M.Node<K>}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      nth_snoc_other(M.Node<K>, nl, x, i, M.Free{0n}, h)

def nd_snoc_same(-K: Data, +nl: List<&2, M.Node<K>>, +x: M.Node<K>) -> {ST.nd(K, SC.snoc(M.Node<K>, nl, x), 1n+SC.length(M.Node<K>, nl)) == x : M.Node<K>}:
  nth_snoc_same(M.Node<K>, nl, x, M.Free{0n})


# a new slot agrees off it
def agr_snoc(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +x: M.Node<K>, +hn: {HT.memn(1n+SC.length(M.Node<K>, nl), xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, SC.snoc(M.Node<K>, nl, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.and_intro(AG.ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, SC.snoc(M.Node<K>, nl, x), j)), AG.agr(~K, ~cmp, t, nl, SC.snoc(M.Node<K>, nl, x)), AG.ndeq_of_eq(~K, ~cmp, ~o, ST.nd(K, nl, j), ST.nd(K, SC.snoc(M.Node<K>, nl, x), j), Equal.sym(M.Node<K>, ST.nd(K, SC.snoc(M.Node<K>, nl, x), j), ST.nd(K, nl, j), nd_snoc_other(K, nl, x, j, FR.or_f_l(Nat.is_eq(j, 1n+SC.length(M.Node<K>, nl)), HT.memn(1n+SC.length(M.Node<K>, nl), t), hn)))), agr_snoc(~K, ~cmp, ~o, t, nl, x, FR.or_f_r(Nat.is_eq(j, 1n+SC.length(M.Node<K>, nl)), HT.memn(1n+SC.length(M.Node<K>, nl), t), hn)))

# ---- the payload list ----


def pv_snoc_other(-V: Data, +pl: List<&2, Maybe<&2, V>>, +w: Maybe<&2, V>, +j: Nat, +h: {Nat.is_eq(j, 1n+SC.length(Maybe<&2, V>, pl)) == False{} : Bool}) -> {ST.pv(V, SC.snoc(Maybe<&2, V>, pl, w), j) == ST.pv(V, pl, j) : Maybe<&2, V>}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      nth_snoc_other(Maybe<&2, V>, pl, w, i, None{}, h)

def pv_snoc_same(-V: Data, +pl: List<&2, Maybe<&2, V>>, +w: Maybe<&2, V>) -> {ST.pv(V, SC.snoc(Maybe<&2, V>, pl, w), 1n+SC.length(Maybe<&2, V>, pl)) == w : Maybe<&2, V>}:
  nth_snoc_same(Maybe<&2, V>, pl, w, None{})

def pv_ex_other(-V: Data, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +w: Maybe<&2, V>, +j: Nat, +hne: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.pv(V, PR.ex_pl(V, pl, id, w), j) == ST.pv(V, pl, j) : Maybe<&2, V>}:
  match id j:
    case 0n +j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+jj:
      nth_upd_c(Maybe<&2, V>, pl, i, w, jj, None{}, hne, Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)))

def pv_ex_same(-V: Data, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +w: Maybe<&2, V>, +h: {Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)) == True{} : Bool}) -> {ST.pv(V, PR.ex_pl(V, pl, 1n+i, w), 1n+i) == w : Maybe<&2, V>}:
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)), True{}, h) : {ST.nth_or(Maybe<&2, V>, ST.pk(List<&2, Maybe<&2, V>>, _, SC.update(Maybe<&2, V>, pl, i, w), pl), i, None{}) == w : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, i, w), i, None{}), PR.or_else(Maybe<&2, V>, SC.nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, i, w), i), None{}), PR.nth_or_nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, i, w), i, None{})) : {_ == w : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, Maybe<&2, V>>, SC.nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, i, w), i), Some{w}, LL.nth_update_same(Maybe<&2, V>, pl, i, w, h)) : {PR.or_else(Maybe<&2, V>, _, None{}) == w : Maybe<&2, V>}
  {==}


def ents_psnoc(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +w: Maybe<&2, V>, +hn: {HT.memn(1n+SC.length(Maybe<&2, V>, pl), xs) == False{} : Bool}) -> {ST.ents(~K, ~V, xs, nl, SC.snoc(Maybe<&2, V>, pl, w)) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, V>, ST.pv(V, SC.snoc(Maybe<&2, V>, pl, w), j), ST.pv(V, pl, j), pv_snoc_other(V, pl, w, j, FR.or_f_l(Nat.is_eq(j, 1n+SC.length(Maybe<&2, V>, pl)), HT.memn(1n+SC.length(Maybe<&2, V>, pl), t), hn))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), _), ST.ents(~K, ~V, t, nl, SC.snoc(Maybe<&2, V>, pl, w))) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, nl, SC.snoc(Maybe<&2, V>, pl, w)), ST.ents(~K, ~V, t, nl, pl), ents_psnoc(~K, ~V, t, nl, pl, w, FR.or_f_r(Nat.is_eq(j, 1n+SC.length(Maybe<&2, V>, pl)), HT.memn(1n+SC.length(Maybe<&2, V>, pl), t), hn))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def ents_pex(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +w: Maybe<&2, V>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {ST.ents(~K, ~V, xs, nl, PR.ex_pl(V, pl, id, w)) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, V>, ST.pv(V, PR.ex_pl(V, pl, id, w), j), ST.pv(V, pl, j), pv_ex_other(V, pl, id, w, j, FR.ne_sym(j, id, FR.or_f_l(Nat.is_eq(j, id), HT.memn(id, t), hn)))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), _), ST.ents(~K, ~V, t, nl, PR.ex_pl(V, pl, id, w))) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, nl, PR.ex_pl(V, pl, id, w)), ST.ents(~K, ~V, t, nl, pl), ents_pex(~K, ~V, t, nl, pl, id, w, FR.or_f_r(Nat.is_eq(j, id), HT.memn(id, t), hn))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}
