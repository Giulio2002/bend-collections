import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./ord.bend as OR

# Insertion at a gap of a sorted list: the specification's ins puts the
# entry there, lookup misses, and order holds; the node and payload lists
# grown by a slot or rewritten at one. (source: tools/generators/tm_hand/ins.src)


def ins_nil(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +v: V, +ys: List<&2, M.Entry<K, V>>, +hg: {OR.gtall(~K, ~V, ~cmp, k, ys) == True{} : Bool}) -> {S.ins(~K, ~V, ~cmp, k, v, ys) == Con{M.Entry{k, v}, ys} : List<&2, M.Entry<K, V>>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), LT{}, O.lt_is(cmp(k, S.key(K, V, e)), L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, t), hg))) : {S.pick(List<&2, M.Entry<K, V>>, Cmp.is_lt(_), Con{M.Entry{k, v}, Con{e, t}}, Con{e, S.ins(~K, ~V, ~cmp, k, v, t)}) == Con{M.Entry{k, v}, Con{e, t}} : List<&2, M.Entry<K, V>>}
      {==}

# inserting k between the entries below and above it
def ins_gap(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +v: V, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +hl: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, k, ys) == True{} : Bool}) -> {S.ins(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, xs, ys)) == SC.append(M.Entry<K, V>, xs, Con{M.Entry{k, v}, ys}) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      ins_nil(~K, ~V, ~cmp, k, v, ys, hg)
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), GT{}, OR.lt_gt(~K, ~cmp, ~o, S.key(K, V, e), k, L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl))) : {S.pick(List<&2, M.Entry<K, V>>, Cmp.is_lt(_), Con{M.Entry{k, v}, Con{e, SC.append(M.Entry<K, V>, t, ys)}}, Con{e, S.ins(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, t, ys))}) == Con{e, SC.append(M.Entry<K, V>, t, Con{M.Entry{k, v}, ys})} : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, S.ins(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, t, ys)), SC.append(M.Entry<K, V>, t, Con{M.Entry{k, v}, ys}), ins_gap(~K, ~V, ~cmp, ~o, k, v, t, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl), hg)) : {Con{e, _} == Con{e, SC.append(M.Entry<K, V>, t, Con{M.Entry{k, v}, ys})} : List<&2, M.Entry<K, V>>}
      {==}

# k is found neither below nor above it
def find_gap(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +hl: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, k, ys) == True{} : Bool}) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == None{} : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)), OR.orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.find_e(~K, ~V, ~cmp, k, ys)), OR.find_app(~K, ~V, ~cmp, k, xs, ys)) : {_ == None{} : Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, xs), None{}, OR.lt_none(~K, ~V, ~cmp, ~o, k, xs, hl)) : {OR.orm(M.Entry<K, V>, _, S.find_e(~K, ~V, ~cmp, k, ys)) == None{} : Maybe<&2, M.Entry<K, V>>}
  OR.gt_none(~K, ~V, ~cmp, k, ys, hg)

def ord_cons(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, ys) == True{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, S.key(K, V, e), ys) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, Con{e, ys}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+e2, +u}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, u}), L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), OR.gtall(~K, ~V, ~cmp, S.key(K, V, e), u), hg), h)

def ord_step(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +a: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +hae: {Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))) == True{} : Bool}, +h: {ST.ordered(~K, ~V, ~cmp, Con{a, SC.append(M.Entry<K, V>, t, ys)}) == True{} : Bool}, +ih: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, t, Con{e, ys})) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, Con{a, SC.append(M.Entry<K, V>, t, Con{e, ys})}) == True{} : Bool}:
  match t:
    case Nil{}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ST.ordered(~K, ~V, ~cmp, Con{e, ys}), hae, ih)
    case Con{+b, +u}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, SC.append(M.Entry<K, V>, u, Con{e, ys})}), L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, SC.append(M.Entry<K, V>, u, ys)}), h), ih)

# an entry between the entries below and above it keeps the order
def ord_ins(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}, +hl: {OR.ltall(~K, ~V, ~cmp, S.key(K, V, e), xs) == True{} : Bool}, +hg: {OR.gtall(~K, ~V, ~cmp, S.key(K, V, e), ys) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      ord_cons(~K, ~V, ~cmp, e, ys, h, hg)
    case Con{+a, +t}:
      +ht = OR.ord_tail(~K, ~V, ~cmp, a, SC.append(M.Entry<K, V>, t, ys), h)
      +ih = ord_ins(~K, ~V, ~cmp, ~o, t, e, ys, ht, L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), OR.ltall(~K, ~V, ~cmp, S.key(K, V, e), t), hl), hg)
      ord_step(~K, ~V, ~cmp, a, t, e, ys, L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), OR.ltall(~K, ~V, ~cmp, S.key(K, V, e), t), hl), h, ih)

