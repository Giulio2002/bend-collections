import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../../spec/balanced_search_tree.bend as S
import ../../types/balanced_search_tree.bend as E

# The four finite-map laws of the specification's association-list model
# (spec/balanced_search_tree.bend), which the graph's well-formedness proof
# needs at two levels: the vertex map (values are neighbour sets) and a
# neighbour set (values are Unit).
#
#   find(k, ins(k, v, xs)) = Some v
#   find(j, ins(k, v, xs)) = find(j, xs)        when j and k differ
#   find(k, del(k, xs))    = None
#   find(j, del(k, xs))    = find(j, xs)        when j and k differ
#
# `S.find` and `S.del` scan the whole list, so none of these needs the list to
# be sorted; only the total-order laws ~o are used (to turn cmp(k, key e) = EQ
# into k = key e).

# ---- "the keys differ" ----

def ne_of_lt(~K: Data, ~cmp: K -> K -> Cmp, +a: K, +b: K, +h: {cmp(a, b) == LT{} : Cmp}) -> {Cmp.is_eq(cmp(a, b)) == False{} : Bool}:
  %Equal.sym(Cmp, cmp(a, b), LT{}, h) : {Cmp.is_eq(_) == False{} : Bool}
  {==}

def ne_of_gt(~K: Data, ~cmp: K -> K -> Cmp, +a: K, +b: K, +h: {cmp(a, b) == GT{} : Cmp}) -> {Cmp.is_eq(cmp(a, b)) == False{} : Bool}:
  %Equal.sym(Cmp, cmp(a, b), GT{}, h) : {Cmp.is_eq(_) == False{} : Bool}
  {==}

def eq_of_is_eq(c: Cmp, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(h))

# j differs from k, and k is the key of e, so j differs from the key of e
def ne_move(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +j: K, +k: K, +e: E.Entry<K, V>, +hk: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}, +ne: {Cmp.is_eq(cmp(j, k)) == False{} : Bool}) -> {Cmp.is_eq(cmp(j, E.key(K, V, e))) == False{} : Bool}:
  L.subst(K, x => {Cmp.is_eq(cmp(j, x)) == False{} : Bool}, k, E.key(K, V, e),
    O.antisym(~K, ~cmp, o, k, E.key(K, V, e), hk), ne)

# ---- one more step lemma for each operation ----

def find_ne_c(-K: Data, -V: Data, c: Cmp, +e: E.Entry<K, V>, +rest: Maybe<&2, V>, +ne: {Cmp.is_eq(c) == False{} : Bool}) -> {S.find_at(K, V, c, e, rest) == rest : Maybe<&2, V>}:
  match c e:
    case LT{} E.Entry{a, b}:
      {==}
    case EQ{} E.Entry{a, b}:
      Empty.absurd({Some{b} == rest : Maybe<&2, V>}, L.true_false(ne))
    case GT{} E.Entry{a, b}:
      {==}

def find_ne(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +j: K, +ne: {Cmp.is_eq(cmp(j, E.key(K, V, e))) == False{} : Bool}) -> {S.find(~K, ~cmp, V, j, Con{e, r}) == S.find(~K, ~cmp, V, j, r) : Maybe<&2, V>}:
  find_ne_c(K, V, cmp(j, E.key(K, V, e)), e, S.find(~K, ~cmp, V, j, r), ne)

def ins_lt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == LT{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, Con{e, r}) == Con{E.Entry{k, v}, Con{e, r}} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{E.Entry{k, v}, Con{e, r}} : List<&2, E.Entry<K, V>>}
  {==}

def ins_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, Con{e, r}) == Con{E.Entry{k, v}, r} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{E.Entry{k, v}, r} : List<&2, E.Entry<K, V>>}
  {==}

def ins_gt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, Con{e, r}) == Con{e, S.ins(~K, ~cmp, V, k, v, r)} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{e, S.ins(~K, ~cmp, V, k, v, r)} : List<&2, E.Entry<K, V>>}
  {==}

def del_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {S.del(~K, ~cmp, V, k, Con{e, r}) == S.del(~K, ~cmp, V, k, r) : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, h) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == S.del(~K, ~cmp, V, k, r) : List<&2, E.Entry<K, V>>}
  {==}

def del_ne_c(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, c: Cmp, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +ne: {Cmp.is_eq(c) == False{} : Bool}, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}) -> {S.del(~K, ~cmp, V, k, Con{e, r}) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, ec) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}
      {==}
    case EQ{}:
      Empty.absurd({S.del(~K, ~cmp, V, k, Con{e, r}) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}, L.true_false(ne))
    case GT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, ec) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}
      {==}

# ---- the four laws ----

def find_ins_same_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +v: V, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ih: {S.find(~K, ~cmp, V, k, S.ins(~K, ~cmp, V, k, v, t)) == Some{v} : Maybe<&2, V>}) -> {S.find(~K, ~cmp, V, k, S.ins(~K, ~cmp, V, k, v, Con{e, t})) == Some{v} : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, Con{e, t}}, ins_lt(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, k, _) == Some{v} : Maybe<&2, V>}
      %Equal.sym(Cmp, cmp(k, k), EQ{}, O.refl(~K, ~cmp, ~o, k)) : {S.find_at(K, V, _, E.Entry{k, v}, S.find(~K, ~cmp, V, k, Con{e, t})) == Some{v} : Maybe<&2, V>}
      {==}
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, t}, ins_eq(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, k, _) == Some{v} : Maybe<&2, V>}
      %Equal.sym(Cmp, cmp(k, k), EQ{}, O.refl(~K, ~cmp, ~o, k)) : {S.find_at(K, V, _, E.Entry{k, v}, S.find(~K, ~cmp, V, k, t)) == Some{v} : Maybe<&2, V>}
      {==}
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{e, S.ins(~K, ~cmp, V, k, v, t)}, ins_gt(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, k, _) == Some{v} : Maybe<&2, V>}
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, ec) : {S.find_at(K, V, _, e, S.find(~K, ~cmp, V, k, S.ins(~K, ~cmp, V, k, v, t))) == Some{v} : Maybe<&2, V>}
      ih

def find_ins_same(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +k: K, +v: V, xs: List<&2, E.Entry<K, V>>) -> {S.find(~K, ~cmp, V, k, S.ins(~K, ~cmp, V, k, v, xs)) == Some{v} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, cmp(k, k), EQ{}, O.refl(~K, ~cmp, ~o, k)) : {S.find_at(K, V, _, E.Entry{k, v}, None{}) == Some{v} : Maybe<&2, V>}
      {==}
    case Con{+e, +t}:
      find_ins_same_c(~K, ~cmp, ~o, V, e, t, k, v, cmp(k, E.key(K, V, e)), {==},
        find_ins_same(~K, ~cmp, ~o, V, k, v, t))

def find_ins_other_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +j: K, +k: K, +v: V, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ne: {Cmp.is_eq(cmp(j, k)) == False{} : Bool}, +ih: {S.find(~K, ~cmp, V, j, S.ins(~K, ~cmp, V, k, v, t)) == S.find(~K, ~cmp, V, j, t) : Maybe<&2, V>}) -> {S.find(~K, ~cmp, V, j, S.ins(~K, ~cmp, V, k, v, Con{e, t})) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, Con{e, t}}, ins_lt(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      find_ne(~K, ~cmp, V, E.Entry{k, v}, Con{e, t}, j, ne)
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, t}, ins_eq(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, j, Con{E.Entry{k, v}, t}), S.find(~K, ~cmp, V, j, t), S.find(~K, ~cmp, V, j, Con{e, t}),
        find_ne(~K, ~cmp, V, E.Entry{k, v}, t, j, ne),
        Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, j, Con{e, t}), S.find(~K, ~cmp, V, j, t),
          find_ne(~K, ~cmp, V, e, t, j, ne_move(~K, ~cmp, ~o, V, j, k, e, ec, ne))))
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{e, S.ins(~K, ~cmp, V, k, v, t)}, ins_gt(~K, ~cmp, V, e, t, k, v, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => S.find_at(K, V, cmp(j, E.key(K, V, e)), e, z),
        S.find(~K, ~cmp, V, j, S.ins(~K, ~cmp, V, k, v, t)), S.find(~K, ~cmp, V, j, t), ih)

def find_ins_other(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +j: K, +k: K, +v: V, xs: List<&2, E.Entry<K, V>>, +ne: {Cmp.is_eq(cmp(j, k)) == False{} : Bool}) -> {S.find(~K, ~cmp, V, j, S.ins(~K, ~cmp, V, k, v, xs)) == S.find(~K, ~cmp, V, j, xs) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      find_ne(~K, ~cmp, V, E.Entry{k, v}, Nil{}, j, ne)
    case Con{+e, +t}:
      find_ins_other_c(~K, ~cmp, ~o, V, e, t, j, k, v, cmp(k, E.key(K, V, e)), {==}, ne,
        find_ins_other(~K, ~cmp, ~o, V, j, k, v, t, ne))

def find_del_same_c(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ih: {S.find(~K, ~cmp, V, k, S.del(~K, ~cmp, V, k, t)) == None{} : Maybe<&2, V>}) -> {S.find(~K, ~cmp, V, k, S.del(~K, ~cmp, V, k, Con{e, t})) == None{} : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, del_ne_c(~K, ~cmp, V, LT{}, e, t, k, {==}, ec)) : {S.find(~K, ~cmp, V, k, _) == None{} : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, S.del(~K, ~cmp, V, k, t)}), S.find(~K, ~cmp, V, k, S.del(~K, ~cmp, V, k, t)), None{},
        find_ne(~K, ~cmp, V, e, S.del(~K, ~cmp, V, k, t), k, ne_of_lt(~K, ~cmp, k, E.key(K, V, e), ec)), ih)
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), S.del(~K, ~cmp, V, k, t), del_eq(~K, ~cmp, V, e, t, k, ec)) : {S.find(~K, ~cmp, V, k, _) == None{} : Maybe<&2, V>}
      ih
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, del_ne_c(~K, ~cmp, V, GT{}, e, t, k, {==}, ec)) : {S.find(~K, ~cmp, V, k, _) == None{} : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, S.del(~K, ~cmp, V, k, t)}), S.find(~K, ~cmp, V, k, S.del(~K, ~cmp, V, k, t)), None{},
        find_ne(~K, ~cmp, V, e, S.del(~K, ~cmp, V, k, t), k, ne_of_gt(~K, ~cmp, k, E.key(K, V, e), ec)), ih)

def find_del_same(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, xs: List<&2, E.Entry<K, V>>) -> {S.find(~K, ~cmp, V, k, S.del(~K, ~cmp, V, k, xs)) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      find_del_same_c(~K, ~cmp, V, e, t, k, cmp(k, E.key(K, V, e)), {==},
        find_del_same(~K, ~cmp, V, k, t))

def find_del_other_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +j: K, +k: K, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ne: {Cmp.is_eq(cmp(j, k)) == False{} : Bool}, +ih: {S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, t)) == S.find(~K, ~cmp, V, j, t) : Maybe<&2, V>}) -> {S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, Con{e, t})) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, del_ne_c(~K, ~cmp, V, LT{}, e, t, k, {==}, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => S.find_at(K, V, cmp(j, E.key(K, V, e)), e, z),
        S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, t)), S.find(~K, ~cmp, V, j, t), ih)
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), S.del(~K, ~cmp, V, k, t), del_eq(~K, ~cmp, V, e, t, k, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, t)), S.find(~K, ~cmp, V, j, t), S.find(~K, ~cmp, V, j, Con{e, t}),
        ih,
        Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, j, Con{e, t}), S.find(~K, ~cmp, V, j, t),
          find_ne(~K, ~cmp, V, e, t, j, ne_move(~K, ~cmp, ~o, V, j, k, e, ec, ne))))
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, del_ne_c(~K, ~cmp, V, GT{}, e, t, k, {==}, ec)) : {S.find(~K, ~cmp, V, j, _) == S.find(~K, ~cmp, V, j, Con{e, t}) : Maybe<&2, V>}
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => S.find_at(K, V, cmp(j, E.key(K, V, e)), e, z),
        S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, t)), S.find(~K, ~cmp, V, j, t), ih)

def find_del_other(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +j: K, +k: K, xs: List<&2, E.Entry<K, V>>, +ne: {Cmp.is_eq(cmp(j, k)) == False{} : Bool}) -> {S.find(~K, ~cmp, V, j, S.del(~K, ~cmp, V, k, xs)) == S.find(~K, ~cmp, V, j, xs) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      find_del_other_c(~K, ~cmp, ~o, V, e, t, j, k, cmp(k, E.key(K, V, e)), {==}, ne,
        find_del_other(~K, ~cmp, ~o, V, j, k, t, ne))
