import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./ord.bend as OR

# Deleting a key from sorted entries: del removes exactly the entry holding
# it when the entries before are smaller, and dropping an entry keeps the
# entries sorted. (source: tools/generators/tm_hand/dord.src)


def del_mid(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +hl: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}, +hc: {cmp(k, S.key(K, V, e)) == EQ{} : Cmp}) -> {S.del(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == SC.append(M.Entry<K, V>, xs, ys) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), EQ{}, hc) : {S.pick(List<&2, M.Entry<K, V>>, S.is_eq(_), ys, Con{e, S.del(~K, ~V, ~cmp, k, ys)}) == ys : List<&2, M.Entry<K, V>>}
      {==}
    case Con{+a, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, a)), GT{}, OR.lt_gt(~K, ~cmp, ~o, S.key(K, V, a), k, L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl))) : {S.pick(List<&2, M.Entry<K, V>>, S.is_eq(_), SC.append(M.Entry<K, V>, t, Con{e, ys}), Con{a, S.del(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, Con{e, ys}))}) == Con{a, SC.append(M.Entry<K, V>, t, ys)} : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, S.del(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, Con{e, ys})), SC.append(M.Entry<K, V>, t, ys), del_mid(~K, ~V, ~cmp, ~o, k, t, e, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl), hc)) : {Con{a, _} == Con{a, SC.append(M.Entry<K, V>, t, ys)} : List<&2, M.Entry<K, V>>}
      {==}

# the first of the entries after one dropped
def ord_tail(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, ys}) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+b, +u}:
      L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, u}), h)

def ord_skip(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: M.Entry<K, V>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{a, Con{e, ys}}) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, Con{a, ys}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+b, +u}:
      +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ST.ordered(~K, ~V, ~cmp, Con{e, Con{b, u}}), h)
      +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ST.ordered(~K, ~V, ~cmp, Con{e, Con{b, u}}), h)
      +h3 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, u}), h2)
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, u}), OR.slt_trans(~K, ~cmp, ~o, S.key(K, V, a), S.key(K, V, e), S.key(K, V, b), h1, h3), L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, u}), h2))

# dropping an entry keeps the order
def ord_drop(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ord_tail(~K, ~V, ~cmp, ~o, e, ys, h)
    case Con{+a, +t}:
      match t:
        case Nil{}:
          ord_skip(~K, ~V, ~cmp, ~o, a, e, ys, h)
        case Con{+a2, +u}:
          +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, Con{e, ys})}), h)
          +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, Con{e, ys})}), h)
          L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, ys)}), h1, ord_drop(~K, ~V, ~cmp, ~o, Con{a2, u}, e, ys, h2))


def del_ab_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {S.find(~K, ~V, ~cmp, k, Con{e, t}) == None{} : Maybe<&2, V>}, +b: Bool, +hb: {S.is_eq(cmp(k, S.key(K, V, e))) == b : Bool}, ih: @+ht: {S.find(~K, ~V, ~cmp, k, t) == None{} : Maybe<&2, V>} -> {S.del(~K, ~V, ~cmp, k, t) == t : List<&2, M.Entry<K, V>>}) -> {S.del(~K, ~V, ~cmp, k, Con{e, t}) == Con{e, t} : List<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      +h1 = L.subst(Bool, z => {S.val_m(K, V, S.pick(Maybe<&2, M.Entry<K, V>>, z, Some{e}, S.find_e(~K, ~V, ~cmp, k, t))) == None{} : Maybe<&2, V>}, S.is_eq(cmp(k, S.key(K, V, e))), True{}, hb, h)
      Empty.absurd({S.del(~K, ~V, ~cmp, k, Con{e, t}) == Con{e, t} : List<&2, M.Entry<K, V>>}, L.false_true(L.subst(Maybe<&2, V>, z => {S.is_some(V, z) == True{} : Bool}, Some{S.val(K, V, e)}, None{}, h1, {==})))
    case False{}:
      +h1 = L.subst(Bool, z => {S.val_m(K, V, S.pick(Maybe<&2, M.Entry<K, V>>, z, Some{e}, S.find_e(~K, ~V, ~cmp, k, t))) == None{} : Maybe<&2, V>}, S.is_eq(cmp(k, S.key(K, V, e))), False{}, hb, h)
      %Equal.sym(Bool, S.is_eq(cmp(k, S.key(K, V, e))), False{}, hb) : {S.pick(List<&2, M.Entry<K, V>>, _, t, Con{e, S.del(~K, ~V, ~cmp, k, t)}) == Con{e, t} : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, S.del(~K, ~V, ~cmp, k, t), t, ih(h1)) : {Con{e, _} == Con{e, t} : List<&2, M.Entry<K, V>>}
      {==}

# deleting an absent key changes nothing
def del_absent(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +es: List<&2, M.Entry<K, V>>, +h: {S.find(~K, ~V, ~cmp, k, es) == None{} : Maybe<&2, V>}) -> {S.del(~K, ~V, ~cmp, k, es) == es : List<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      del_ab_c(~K, ~V, ~cmp, ~o, k, e, t, h, S.is_eq(cmp(k, S.key(K, V, e))), {==}, ht => del_absent(~K, ~V, ~cmp, ~o, k, t, ht))
