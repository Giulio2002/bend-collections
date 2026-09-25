import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./ord.bend as OR
import ./tree.bend as TR

# The ghost search finds the specification's value: over a subtree whose
# nodes link as the ghost tree says, have values, and list their entries in
# key order, the payload at the id the search returns is the lookup of the
# key in the subtree's entries. (source: tools/generators/tm_hand/find.src)


def sfound(s: M.Search) -> Nat:
  match s:
    case M.Search{+f, p, lf}:
      f

def cons_m_app(-X: Data, +m: Maybe<&2, X>, +xs: List<&2, X>, +ys: List<&2, X>) -> {SC.append(X, ST.cons_m(X, m, xs), ys) == ST.cons_m(X, m, SC.append(X, xs, ys)) : List<&2, X>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ents_app(~K: Data, ~V: Data, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>) -> {ST.ents(~K, ~V, SC.append(Nat, xs, ys), nl, pl) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, xs, nl, pl), ST.ents(~K, ~V, ys, nl, pl)) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+i, +t}:
      %Equal.sym(List<&2, M.Entry<K, V>>, SC.append(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, t, nl, pl)), ST.ents(~K, ~V, ys, nl, pl)), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, t, nl, pl), ST.ents(~K, ~V, ys, nl, pl))), cons_m_app(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, t, nl, pl), ST.ents(~K, ~V, ys, nl, pl))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, SC.append(Nat, t, ys), nl, pl)) == _ : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, SC.append(Nat, t, ys), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, t, nl, pl), ST.ents(~K, ~V, ys, nl, pl)), ents_app(~K, ~V, t, ys, nl, pl)) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), _) == ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, t, nl, pl), ST.ents(~K, ~V, ys, nl, pl))) : List<&2, M.Entry<K, V>>}
      {==}

def ord_app_l(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{+e2, +u}:
          L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, u}), L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, SC.append(M.Entry<K, V>, u, ys)}), h), ord_app_l(~K, ~V, ~cmp, Con{e2, u}, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, SC.append(M.Entry<K, V>, u, ys)}), h)))

def ord_cons_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m: Maybe<&2, M.Entry<K, V>>, +t: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, ST.cons_m(M.Entry<K, V>, m, t)) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, t) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+e}:
      OR.ord_tail(~K, ~V, ~cmp, e, t, h)


def tf_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +left: Bool, +k: K, +key: K, +v: V, +hpi: {ST.pv(V, pl, i) == Some{v} : Maybe<&2, V>}, +ho: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl)})) == True{} : Bool}, +ihl: {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}))) == S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl)) : Maybe<&2, V>}, +ihr: {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}))) == S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tr), nl, pl)) : Maybe<&2, V>}, +cc: Cmp, +hcc: {cmp(k, key) == cc : Cmp}) -> {ST.pv(V, pl, sfound(TR.pk3(M.Search, cc, TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left}))) == S.find(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl)})) : Maybe<&2, V>}:
  match cc:
    case LT{}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl)})), S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl)), OR.find_mid_lt(~K, ~V, ~cmp, ~o, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl), M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl), ho, hcc)) : {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}))) == S.val_m(K, V, _) : Maybe<&2, V>}
      ihl
    case GT{}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl)})), S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tr), nl, pl)), OR.find_mid_gt(~K, ~V, ~cmp, ~o, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl), M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl), ho, hcc)) : {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}))) == S.val_m(K, V, _) : Maybe<&2, V>}
      ihr
    case EQ{}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl)})), Some{M.Entry{key, v}}, OR.find_mid_eq(~K, ~V, ~cmp, ~o, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl), M.Entry{key, v}, ST.ents(~K, ~V, ST.ids(tr), nl, pl), ho, hcc)) : {ST.pv(V, pl, i) == S.val_m(K, V, _) : Maybe<&2, V>}
      hpi

def tf_node(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +left: Bool, +k: K, +x: M.Node<K>, +m: Maybe<&2, V>, +hx: {ST.is_node(K, x, ST.rid(tl), ST.rid(tr), p) == True{} : Bool}, +hm: {ST.some2(V, m) == True{} : Bool}, +hpi: {ST.pv(V, pl, i) == m : Maybe<&2, V>}, +ho: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, x, m), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))) == True{} : Bool}, +ihl: {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}))) == S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tl), nl, pl)) : Maybe<&2, V>}, +ihr: {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}))) == S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tr), nl, pl)) : Maybe<&2, V>}) -> {ST.pv(V, pl, sfound(TR.pk3(M.Search, TR.kc(~K, ~cmp, k, x), TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left}))) == S.find(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, x, m), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))) : Maybe<&2, V>}:
  match x m:
    case M.Free{fx} _:
      Empty.absurd({ST.pv(V, pl, sfound(TR.pk3(M.Search, EQ{}, TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left}))) == S.find(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, M.Free{fx}, m), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))) : Maybe<&2, V>}, L.false_true(hx))
    case M.N{c, a, b, q, +key} None{}:
      Empty.absurd({ST.pv(V, pl, sfound(TR.pk3(M.Search, cmp(k, key), TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left}))) == S.find(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, M.N{c, a, b, q, key}, None{}), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))) : Maybe<&2, V>}, L.false_true(hm))
    case M.N{c, a, b, q, +key} Some{+v}:
      tf_c(~K, ~V, ~cmp, ~o, nl, pl, i, tl, tr, p, left, k, key, v, hpi, ho, ihl, ihr, cmp(k, key), {==})


def pay_parts(~V: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +pl: List<&2, Maybe<&2, V>>, +h: {ST.pay(~V, ST.TN{i, tl, tr}, pl) == True{} : Bool}) -> {ST.some2(V, ST.pv(V, pl, i)) == True{} : Bool} & ({ST.pay(~V, tl, pl) == True{} : Bool} & {ST.pay(~V, tr, pl) == True{} : Bool}):
  +h2 = L.and_right(ST.some2(V, ST.pv(V, pl, i)), Bool.and(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl)), h)
  (L.and_left(ST.some2(V, ST.pv(V, pl, i)), Bool.and(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl)), h), (L.and_left(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl), h2), L.and_right(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl), h2)))

def pay_node(~V: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +pl: List<&2, Maybe<&2, V>>, +h: {ST.pay(~V, ST.TN{i, tl, tr}, pl) == True{} : Bool}) -> {ST.some2(V, ST.pv(V, pl, i)) == True{} : Bool}:
  L.and_left(ST.some2(V, ST.pv(V, pl, i)), Bool.and(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl)), h)

def pay_l(~V: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +pl: List<&2, Maybe<&2, V>>, +h: {ST.pay(~V, ST.TN{i, tl, tr}, pl) == True{} : Bool}) -> {ST.pay(~V, tl, pl) == True{} : Bool}:
  L.and_left(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl), L.and_right(ST.some2(V, ST.pv(V, pl, i)), Bool.and(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl)), h))

def pay_r(~V: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +pl: List<&2, Maybe<&2, V>>, +h: {ST.pay(~V, ST.TN{i, tl, tr}, pl) == True{} : Bool}) -> {ST.pay(~V, tr, pl) == True{} : Bool}:
  L.and_right(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl), L.and_right(ST.some2(V, ST.pv(V, pl, i)), Bool.and(ST.pay(~V, tl, pl), ST.pay(~V, tr, pl)), h))


# the entries of a node's subtree: the left ones, its own, the right ones
def ents_node(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr) -> {ST.ents(~K, ~V, ST.ids(ST.TN{i, tl, tr}), nl, pl) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl))) : List<&2, M.Entry<K, V>>}:
  ents_app(~K, ~V, ST.ids(tl), Con{i, ST.ids(tr)}, nl, pl)

# the value at the ghost search's id is the lookup of the key
def tfind(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +p: Nat, +left: Bool, +k: K, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}, +hp: {ST.pay(~V, t, pl) == True{} : Bool}, +ho: {ST.ordered(~K, ~V, ~cmp, ST.ents(~K, ~V, ST.ids(t), nl, pl)) == True{} : Bool}) -> {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, t, nl, k, p, left))) == S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(t), nl, pl)) : Maybe<&2, V>}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +tl, +tr}:
      +ho2 = L.subst(List<&2, M.Entry<K, V>>, z => {ST.ordered(~K, ~V, ~cmp, z) == True{} : Bool}, ST.ents(~K, ~V, ST.ids(ST.TN{i, tl, tr}), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl))), ents_node(~K, ~V, nl, pl, i, tl, tr), ho)
      +ihl = tfind(~K, ~V, ~cmp, ~o, nl, pl, tl, i, True{}, k, TR.rep_l(~K, i, tl, tr, p, nl, hr), pay_l(~V, i, tl, tr, pl, hp), ord_app_l(~K, ~V, ~cmp, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl)), ho2))
      +ihr = tfind(~K, ~V, ~cmp, ~o, nl, pl, tr, i, False{}, k, TR.rep_r(~K, i, tl, tr, p, nl, hr), pay_r(~V, i, tl, tr, pl, hp), ord_cons_m(~K, ~V, ~cmp, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl), OR.ord_app_r(~K, ~V, ~cmp, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl)), ho2)))
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(ST.TN{i, tl, tr}), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl))), ents_node(~K, ~V, nl, pl, i, tl, tr)) : {ST.pv(V, pl, sfound(TR.tsearch(~K, ~V, ~cmp, ST.TN{i, tl, tr}, nl, k, p, left))) == S.find(~K, ~V, ~cmp, k, _) : Maybe<&2, V>}
      tf_node(~K, ~V, ~cmp, ~o, nl, pl, i, tl, tr, p, left, k, ST.nd(K, nl, i), ST.pv(V, pl, i), TR.rep_node(~K, i, tl, tr, p, nl, hr), pay_node(~V, i, tl, tr, pl, hp), {==}, ho2, ihl, ihr)
