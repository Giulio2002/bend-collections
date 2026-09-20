import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../../spec/balanced_search_tree.bend as S
import ../../src/balanced_search_tree.bend as B
import ../../src/doubly_linked_list.bend as D
import ../../types/balanced_search_tree.bend as BE
import ../../types/doubly_linked_list.bend as E
import ../../spec/common.bend as SC
import ../balanced_search_tree/steps.bend as ST
import ../balanced_search_tree/api.bend as API

# The node store: the Nat instance of the checked ordered map. Lookups after
# put/drop, the effect of relinking one neighbour, and key membership.

def ninv(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>) -> Bool:
  ST.inv(~Nat, ~Nat.cmp, D.Node<T>, nodes)

def nabs(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>) -> List<&2, BE.Entry<Nat, D.Node<T>>>:
  ST.abs(~Nat, ~Nat.cmp, D.Node<T>, nodes)

def mem(+k: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(k, h), mem(k, t))

def keys(-T: Data, xs: List<&2, BE.Entry<Nat, D.Node<T>>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{BE.key(Nat, D.Node<T>, e), keys(T, t)}

# Every key is a member of l.
def allin(-T: Data, xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +l: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l))

def nrefl(+k: Nat) -> {Nat.cmp(k, k) == EQ{} : Cmp}:
  O.refl(~Nat, ~Nat.cmp, ~O.nat_order, k)

def eq_flip(+c: Cmp) -> {Cmp.is_eq(O.flipc(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def is_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(b, a) == Nat.is_eq(a, b) : Bool}:
  %Equal.sym(Cmp, Nat.cmp(b, a), O.flipc(Nat.cmp(a, b)), O.nat_flip(a, b)) : {Cmp.is_eq(_) == Cmp.is_eq(Nat.cmp(a, b)) : Bool}
  eq_flip(Nat.cmp(a, b))

# ---- the finite-map model ----

def fat(-T: Data, c: Cmp, +e: BE.Entry<Nat, D.Node<T>>, +rest: Maybe<&2, D.Node<T>>, +h: {Cmp.is_eq(c) == False{} : Bool}) -> {S.find_at(Nat, D.Node<T>, c, e, rest) == rest : Maybe<&2, D.Node<T>>}:
  match c:
    case EQ{}:
      Empty.absurd({S.find_at(Nat, D.Node<T>, EQ{}, e, rest) == rest : Maybe<&2, D.Node<T>>}, L.true_false(h))
    case LT{}:
      {==}
    case GT{}:
      {==}

def fis_c(-T: Data, +k: Nat, +v: D.Node<T>, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, c: Cmp, +ec: {Nat.cmp(k, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +ih: {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, t)) == Some{v} : Maybe<&2, D.Node<T>>}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, Con{e, t})) == Some{v} : Maybe<&2, D.Node<T>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, k, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, t))) == Some{v} : Maybe<&2, D.Node<T>>}
      %Equal.sym(Cmp, Nat.cmp(k, k), EQ{}, nrefl(k)) : {S.find_at(Nat, D.Node<T>, _, BE.Entry{k, v}, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t})) == Some{v} : Maybe<&2, D.Node<T>>}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, k, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, t))) == Some{v} : Maybe<&2, D.Node<T>>}
      %Equal.sym(Cmp, Nat.cmp(k, k), EQ{}, nrefl(k)) : {S.find_at(Nat, D.Node<T>, _, BE.Entry{k, v}, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t)) == Some{v} : Maybe<&2, D.Node<T>>}
      {==}
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, k, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, t))) == Some{v} : Maybe<&2, D.Node<T>>}
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find_at(Nat, D.Node<T>, _, e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, t))) == Some{v} : Maybe<&2, D.Node<T>>}
      ih

def find_ins_same(-T: Data, +k: Nat, +v: D.Node<T>, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, k, v, xs)) == Some{v} : Maybe<&2, D.Node<T>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, Nat.cmp(k, k), EQ{}, nrefl(k)) : {S.find_at(Nat, D.Node<T>, _, BE.Entry{k, v}, None{}) == Some{v} : Maybe<&2, D.Node<T>>}
      {==}
    case Con{+e, +t}:
      fis_c(T, k, v, e, t, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), {==}, find_ins_same(T, k, v, t))

def fio_c(-T: Data, +k: Nat, +j: Nat, +v: D.Node<T>, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, +ne: {Nat.is_eq(k, j) == False{} : Bool}, c: Cmp, +ec: {Nat.cmp(j, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +ih: {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, t)) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t) : Maybe<&2, D.Node<T>>}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, Con{e, t})) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      fat(T, Nat.cmp(k, j), BE.Entry{j, v}, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}), ne)
    case EQ{}:
      +ej = O.nat_eq(j, BE.key(Nat, D.Node<T>, e), ec)
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      Equal.trans(Maybe<&2, D.Node<T>>, S.find_at(Nat, D.Node<T>, Nat.cmp(k, j), BE.Entry{j, v}, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}),
        fat(T, Nat.cmp(k, j), BE.Entry{j, v}, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), ne),
        Equal.sym(Maybe<&2, D.Node<T>>, S.find_at(Nat, D.Node<T>, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), fat(T, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), L.subst(Nat, z => {Nat.is_eq(k, z) == False{} : Bool}, j, BE.key(Nat, D.Node<T>, e), ej, ne))))
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, v, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      Equal.cong(Maybe<&2, D.Node<T>>, Maybe<&2, D.Node<T>>, z => S.find_at(Nat, D.Node<T>, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, z), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), ih)

def find_ins_other(-T: Data, +k: Nat, +j: Nat, +v: D.Node<T>, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +ne: {Nat.is_eq(k, j) == False{} : Bool}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, v, xs)) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, xs) : Maybe<&2, D.Node<T>>}:
  match xs:
    case Nil{}:
      fat(T, Nat.cmp(k, j), BE.Entry{j, v}, None{}, ne)
    case Con{+e, +t}:
      fio_c(T, k, j, v, e, t, ne, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), {==}, find_ins_other(T, k, j, v, t, ne))

def fds_c(-T: Data, +k: Nat, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, c: Cmp, +ec: {Nat.cmp(k, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +ih: {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t)) == None{} : Maybe<&2, D.Node<T>>}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t})) == None{} : Maybe<&2, D.Node<T>>}:
  match c:
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t))) == None{} : Maybe<&2, D.Node<T>>}
      ih
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t))) == None{} : Maybe<&2, D.Node<T>>}
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find_at(Nat, D.Node<T>, _, e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t))) == None{} : Maybe<&2, D.Node<T>>}
      ih
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t))) == None{} : Maybe<&2, D.Node<T>>}
      %Equal.sym(Cmp, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find_at(Nat, D.Node<T>, _, e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, t))) == None{} : Maybe<&2, D.Node<T>>}
      ih

def find_del_same(-T: Data, +k: Nat, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, k, xs)) == None{} : Maybe<&2, D.Node<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fds_c(T, k, e, t, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), {==}, find_del_same(T, k, t))

def fdo_c(-T: Data, +k: Nat, +j: Nat, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, +ne: {Nat.is_eq(k, j) == False{} : Bool}, c: Cmp, +ec: {Nat.cmp(j, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +ih: {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t)) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t) : Maybe<&2, D.Node<T>>}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, Con{e, t})) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}:
  match c:
    case EQ{}:
      +ej = O.nat_eq(j, BE.key(Nat, D.Node<T>, e), ec)
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}), ih,
        Equal.sym(Maybe<&2, D.Node<T>>, S.find_at(Nat, D.Node<T>, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), fat(T, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), L.subst(Nat, z => {Nat.is_eq(k, z) == False{} : Bool}, j, BE.key(Nat, D.Node<T>, e), ej, ne))))
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      Equal.cong(Maybe<&2, D.Node<T>>, Maybe<&2, D.Node<T>>, z => S.find_at(Nat, D.Node<T>, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, z), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), ih)
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t))) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, Con{e, t}) : Maybe<&2, D.Node<T>>}
      Equal.cong(Maybe<&2, D.Node<T>>, Maybe<&2, D.Node<T>>, z => S.find_at(Nat, D.Node<T>, Nat.cmp(k, BE.key(Nat, D.Node<T>, e)), e, z), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, t)), S.find(~Nat, ~Nat.cmp, D.Node<T>, k, t), ih)

def find_del_other(-T: Data, +k: Nat, +j: Nat, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +ne: {Nat.is_eq(k, j) == False{} : Bool}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, k, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, xs)) == S.find(~Nat, ~Nat.cmp, D.Node<T>, k, xs) : Maybe<&2, D.Node<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fdo_c(T, k, j, e, t, ne, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), {==}, find_del_other(T, k, j, t, ne))

# ---- lookups in the node store ----

def get_eq(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +g: {ninv(T, nodes) == True{} : Bool}) -> {D.node(T, nodes, i) == S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, nodes)) : Maybe<&2, D.Node<T>>}:
  API.get_ok(~Nat, ~Nat.cmp, ~O.nat_order, D.Node<T>, nodes, i, g)

def put_inv(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +x: D.Node<T>, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.put(T, nodes, j, x)) == True{} : Bool}:
  API.insert_inv(~Nat, ~Nat.cmp, ~O.nat_order, D.Node<T>, nodes, j, x, g)

def put_abs(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +x: D.Node<T>, +g: {ninv(T, nodes) == True{} : Bool}) -> {nabs(T, D.put(T, nodes, j, x)) == S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes)) : List<&2, BE.Entry<Nat, D.Node<T>>>}:
  API.insert_abs(~Nat, ~Nat.cmp, ~O.nat_order, D.Node<T>, nodes, j, x, g)

def drop_abs(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +g: {ninv(T, nodes) == True{} : Bool}) -> {nabs(T, D.drop(T, nodes, j)) == S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes)) : List<&2, BE.Entry<Nat, D.Node<T>>>}:
  Pair.fst({nabs(T, D.drop(T, nodes, j)) == S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes)) : List<&2, BE.Entry<Nat, D.Node<T>>>}, {ninv(T, D.drop(T, nodes, j)) == True{} : Bool}, API.remove_ok(~Nat, ~Nat.cmp, ~O.nat_order, D.Node<T>, nodes, j, g))

def drop_inv(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.drop(T, nodes, j)) == True{} : Bool}:
  Pair.snd({nabs(T, D.drop(T, nodes, j)) == S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes)) : List<&2, BE.Entry<Nat, D.Node<T>>>}, {ninv(T, D.drop(T, nodes, j)) == True{} : Bool}, API.remove_ok(~Nat, ~Nat.cmp, ~O.nat_order, D.Node<T>, nodes, j, g))

def get_put_same(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +x: D.Node<T>, +g: {ninv(T, nodes) == True{} : Bool}) -> {D.node(T, D.put(T, nodes, j, x), j) == Some{x} : Maybe<&2, D.Node<T>>}:
  Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.put(T, nodes, j, x), j), S.find(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, D.put(T, nodes, j, x))), Some{x},
    get_eq(T, D.put(T, nodes, j, x), j, put_inv(T, nodes, j, x, g)),
    Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, D.put(T, nodes, j, x))), S.find(~Nat, ~Nat.cmp, D.Node<T>, j, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes))), Some{x},
      Equal.cong(List<&2, BE.Entry<Nat, D.Node<T>>>, Maybe<&2, D.Node<T>>, z => S.find(~Nat, ~Nat.cmp, D.Node<T>, j, z), nabs(T, D.put(T, nodes, j, x)), S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes)), put_abs(T, nodes, j, x, g)),
      find_ins_same(T, j, x, nabs(T, nodes))))

def get_put_other(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +j: Nat, +x: D.Node<T>, +g: {ninv(T, nodes) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {D.node(T, D.put(T, nodes, j, x), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.put(T, nodes, j, x), i), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, D.put(T, nodes, j, x))), D.node(T, nodes, i),
    get_eq(T, D.put(T, nodes, j, x), i, put_inv(T, nodes, j, x, g)),
    Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, D.put(T, nodes, j, x))), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes))), D.node(T, nodes, i),
      Equal.cong(List<&2, BE.Entry<Nat, D.Node<T>>>, Maybe<&2, D.Node<T>>, z => S.find(~Nat, ~Nat.cmp, D.Node<T>, i, z), nabs(T, D.put(T, nodes, j, x)), S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes)), put_abs(T, nodes, j, x, g)),
      Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, i, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes))), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, nodes)), D.node(T, nodes, i),
        find_ins_other(T, i, j, x, nabs(T, nodes), ne),
        Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, nodes)), get_eq(T, nodes, i, g)))))

def get_drop_same(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +g: {ninv(T, nodes) == True{} : Bool}) -> {D.node(T, D.drop(T, nodes, j), j) == None{} : Maybe<&2, D.Node<T>>}:
  Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.drop(T, nodes, j), j), S.find(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, D.drop(T, nodes, j))), None{},
    get_eq(T, D.drop(T, nodes, j), j, drop_inv(T, nodes, j, g)),
    Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, D.drop(T, nodes, j))), S.find(~Nat, ~Nat.cmp, D.Node<T>, j, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes))), None{},
      Equal.cong(List<&2, BE.Entry<Nat, D.Node<T>>>, Maybe<&2, D.Node<T>>, z => S.find(~Nat, ~Nat.cmp, D.Node<T>, j, z), nabs(T, D.drop(T, nodes, j)), S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes)), drop_abs(T, nodes, j, g)),
      find_del_same(T, j, nabs(T, nodes))))

def get_drop_other(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +i: Nat, +j: Nat, +g: {ninv(T, nodes) == True{} : Bool}, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {D.node(T, D.drop(T, nodes, j), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.drop(T, nodes, j), i), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, D.drop(T, nodes, j))), D.node(T, nodes, i),
    get_eq(T, D.drop(T, nodes, j), i, drop_inv(T, nodes, j, g)),
    Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, D.drop(T, nodes, j))), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes))), D.node(T, nodes, i),
      Equal.cong(List<&2, BE.Entry<Nat, D.Node<T>>>, Maybe<&2, D.Node<T>>, z => S.find(~Nat, ~Nat.cmp, D.Node<T>, i, z), nabs(T, D.drop(T, nodes, j)), S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes)), drop_abs(T, nodes, j, g)),
      Equal.trans(Maybe<&2, D.Node<T>>, S.find(~Nat, ~Nat.cmp, D.Node<T>, i, S.del(~Nat, ~Nat.cmp, D.Node<T>, j, nabs(T, nodes))), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, nodes)), D.node(T, nodes, i),
        find_del_other(T, i, j, nabs(T, nodes), ne),
        Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, i), S.find(~Nat, ~Nat.cmp, D.Node<T>, i, nabs(T, nodes)), get_eq(T, nodes, i, g)))))

# Relinking a known node is a put.
def sn_put(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, +v: T, +p: Maybe<&2, Nat>, +n: Maybe<&2, Nat>, +q: Maybe<&2, Nat>, +e: {D.node(T, nodes, z) == Some{D.N{v, p, n}} : Maybe<&2, D.Node<T>>}) -> {D.set_next(T, nodes, Some{z}, q) == D.put(T, nodes, z, D.N{v, p, q}) : B.OrdMap<Nat, D.Node<T>>}:
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, z), Some{D.N{v, p, n}}, e) : {D.with_next(T, _, nodes, z, q) == D.put(T, nodes, z, D.N{v, p, q}) : B.OrdMap<Nat, D.Node<T>>}
  {==}

def sp_put(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, +v: T, +p: Maybe<&2, Nat>, +n: Maybe<&2, Nat>, +p2: Maybe<&2, Nat>, +e: {D.node(T, nodes, z) == Some{D.N{v, p, n}} : Maybe<&2, D.Node<T>>}) -> {D.set_prev(T, nodes, Some{z}, p2) == D.put(T, nodes, z, D.N{v, p2, n}) : B.OrdMap<Nat, D.Node<T>>}:
  %Equal.sym(Maybe<&2, D.Node<T>>, D.node(T, nodes, z), Some{D.N{v, p, n}}, e) : {D.with_prev(T, _, nodes, z, p2) == D.put(T, nodes, z, D.N{v, p2, n}) : B.OrdMap<Nat, D.Node<T>>}
  {==}

def wn_inv(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, q: Maybe<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.with_next(T, m, nodes, z, q)) == True{} : Bool}:
  match m:
    case None{}:
      g
    case Some{D.N{v, p, n}}:
      put_inv(T, nodes, z, D.N{v, p, q}, g)

def sn_inv(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, a: Maybe<&2, Nat>, q: Maybe<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.set_next(T, nodes, a, q)) == True{} : Bool}:
  match a:
    case None{}:
      g
    case Some{+z}:
      wn_inv(T, D.node(T, nodes, z), nodes, z, q, g)

def wp_inv(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, p2: Maybe<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.with_prev(T, m, nodes, z, p2)) == True{} : Bool}:
  match m:
    case None{}:
      g
    case Some{D.N{v, p, n}}:
      put_inv(T, nodes, z, D.N{v, p2, n}, g)

def sp_inv(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, b: Maybe<&2, Nat>, p2: Maybe<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}) -> {ninv(T, D.set_prev(T, nodes, b, p2)) == True{} : Bool}:
  match b:
    case None{}:
      g
    case Some{+z}:
      wp_inv(T, D.node(T, nodes, z), nodes, z, p2, g)

def wn_other(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, q: Maybe<&2, Nat>, +i: Nat, +g: {ninv(T, nodes) == True{} : Bool}, +ne: {Nat.is_eq(i, z) == False{} : Bool}) -> {D.node(T, D.with_next(T, m, nodes, z, q), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  match m:
    case None{}:
      {==}
    case Some{D.N{v, p, n}}:
      get_put_other(T, nodes, i, z, D.N{v, p, q}, g, ne)

def wp_other(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, p2: Maybe<&2, Nat>, +i: Nat, +g: {ninv(T, nodes) == True{} : Bool}, +ne: {Nat.is_eq(i, z) == False{} : Bool}) -> {D.node(T, D.with_prev(T, m, nodes, z, p2), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  match m:
    case None{}:
      {==}
    case Some{D.N{v, p, n}}:
      get_put_other(T, nodes, i, z, D.N{v, p2, n}, g, ne)

# ---- keys ----

def nkeys(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>) -> List<&2, Nat>:
  keys(T, nabs(T, nodes))

def allin_ins_c(-T: Data, +j: Nat, +x: D.Node<T>, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, +l: List<&2, Nat>, c: Cmp, +ec: {Nat.cmp(j, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +a: {allin(T, Con{e, t}, l) == True{} : Bool}, +m: {mem(j, l) == True{} : Bool}, +ih: {allin(T, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, t), l) == True{} : Bool}) -> {allin(T, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, Con{e, t}), l) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {allin(T, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, x, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, t)), l) == True{} : Bool}
      L.and_intro(mem(j, l), allin(T, Con{e, t}, l), m, a)
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {allin(T, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, x, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, t)), l) == True{} : Bool}
      L.and_intro(mem(j, l), allin(T, t, l), m, L.and_right(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l), a))
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {allin(T, S.ins_at(~Nat, ~Nat.cmp, D.Node<T>, _, j, x, e, t, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, t)), l) == True{} : Bool}
      L.and_intro(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, t), l), L.and_left(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l), a), ih)

def allin_ins(-T: Data, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +j: Nat, +x: D.Node<T>, +l: List<&2, Nat>, +a: {allin(T, xs, l) == True{} : Bool}, +m: {mem(j, l) == True{} : Bool}) -> {allin(T, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, xs), l) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(mem(j, l), True{}, m, {==})
    case Con{+e, +t}:
      allin_ins_c(T, j, x, e, t, l, Nat.cmp(j, BE.key(Nat, D.Node<T>, e)), {==}, a, m, allin_ins(T, t, j, x, l, L.and_right(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l), a), m))

def allin_put(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +j: Nat, +x: D.Node<T>, +l: List<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}, +a: {allin(T, nabs(T, nodes), l) == True{} : Bool}, +m: {mem(j, l) == True{} : Bool}) -> {allin(T, nabs(T, D.put(T, nodes, j, x)), l) == True{} : Bool}:
  L.subst(List<&2, BE.Entry<Nat, D.Node<T>>>, xs => {allin(T, xs, l) == True{} : Bool}, S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes)), nabs(T, D.put(T, nodes, j, x)), Equal.sym(List<&2, BE.Entry<Nat, D.Node<T>>>, nabs(T, D.put(T, nodes, j, x)), S.ins(~Nat, ~Nat.cmp, D.Node<T>, j, x, nabs(T, nodes)), put_abs(T, nodes, j, x, g)), allin_ins(T, nabs(T, nodes), j, x, l, a, m))

def ids(-T: Data, xs: List<&2, E.Item<T>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{E.Item{i, v}, t}:
      Con{i, ids(T, t)}

def ids_app(-T: Data, +xs: List<&2, E.Item<T>>, +ys: List<&2, E.Item<T>>) -> {ids(T, SC.append(E.Item<T>, xs, ys)) == SC.append(Nat, ids(T, xs), ids(T, ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{E.Item{+i, +v}, +t}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{i, z}, ids(T, SC.append(E.Item<T>, t, ys)), SC.append(Nat, ids(T, t), ids(T, ys)), ids_app(T, t, ys))

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_app(+k: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {mem(k, SC.append(Nat, xs, ys)) == Bool.or(mem(k, xs), mem(k, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(k, h), mem(k, SC.append(Nat, t, ys))), Bool.or(Nat.is_eq(k, h), Bool.or(mem(k, t), mem(k, ys))), Bool.or(Bool.or(Nat.is_eq(k, h), mem(k, t)), mem(k, ys)),
        Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(k, h), z), mem(k, SC.append(Nat, t, ys)), Bool.or(mem(k, t), mem(k, ys)), mem_app(k, t, ys)),
        Equal.sym(Bool, Bool.or(Bool.or(Nat.is_eq(k, h), mem(k, t)), mem(k, ys)), Bool.or(Nat.is_eq(k, h), Bool.or(mem(k, t), mem(k, ys))), or_assoc(Nat.is_eq(k, h), mem(k, t), mem(k, ys))))

# Membership in P ++ h :: Q of something other than h is membership in P ++ Q.
def mem_skip(-T: Data, +k: Nat, +h: Nat, +P: List<&2, E.Item<T>>, +v: T, +Q: List<&2, E.Item<T>>, +ne: {Nat.is_eq(h, k) == False{} : Bool}, +m: {mem(k, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))) == True{} : Bool}) -> {mem(k, ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}:
  +m1 = L.subst(List<&2, Nat>, z => {mem(k, z) == True{} : Bool}, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), SC.append(Nat, ids(T, P), Con{h, ids(T, Q)}), ids_app(T, P, Con{E.Item{h, v}, Q}), m)
  +m2 = L.subst(Bool, z => {z == True{} : Bool}, mem(k, SC.append(Nat, ids(T, P), Con{h, ids(T, Q)})), Bool.or(mem(k, ids(T, P)), Bool.or(Nat.is_eq(k, h), mem(k, ids(T, Q)))), mem_app(k, ids(T, P), Con{h, ids(T, Q)}), m1)
  +nk = Equal.trans(Bool, Nat.is_eq(k, h), Nat.is_eq(h, k), False{}, is_eq_sym(h, k), ne)
  +m3 = L.subst(Bool, z => {Bool.or(mem(k, ids(T, P)), Bool.or(z, mem(k, ids(T, Q)))) == True{} : Bool}, Nat.is_eq(k, h), False{}, nk, m2)
  L.subst(List<&2, Nat>, z => {mem(k, z) == True{} : Bool}, SC.append(Nat, ids(T, P), ids(T, Q)), ids(T, SC.append(E.Item<T>, P, Q)), Equal.sym(List<&2, Nat>, ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, ids(T, P), ids(T, Q)), ids_app(T, P, Q)),
    L.subst(Bool, z => {z == True{} : Bool}, Bool.or(mem(k, ids(T, P)), mem(k, ids(T, Q))), mem(k, SC.append(Nat, ids(T, P), ids(T, Q))), Equal.sym(Bool, mem(k, SC.append(Nat, ids(T, P), ids(T, Q))), Bool.or(mem(k, ids(T, P)), mem(k, ids(T, Q))), mem_app(k, ids(T, P), ids(T, Q))), m3))

def allin_del_c(-T: Data, +h: Nat, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, +P: List<&2, E.Item<T>>, +v: T, +Q: List<&2, E.Item<T>>, c: Cmp, +ec: {Nat.cmp(h, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +a: {allin(T, Con{e, t}, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))) == True{} : Bool}, +ih: {allin(T, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}) -> {allin(T, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, Con{e, t}), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}:
  match c:
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), EQ{}, ec) : {allin(T, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t)), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}
      ih
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {allin(T, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t)), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}
      L.and_intro(mem(BE.key(Nat, D.Node<T>, e), ids(T, SC.append(E.Item<T>, P, Q))), allin(T, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t), ids(T, SC.append(E.Item<T>, P, Q))), mem_skip(T, BE.key(Nat, D.Node<T>, e), h, P, v, Q, L.subst(Cmp, z => {Cmp.is_eq(z) == False{} : Bool}, LT{}, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), Equal.sym(Cmp, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), LT{}, ec), {==}), L.and_left(mem(BE.key(Nat, D.Node<T>, e), ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), allin(T, t, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), a)), ih)
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {allin(T, S.keep_at(Nat, D.Node<T>, S.keep(_), e, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t)), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}
      L.and_intro(mem(BE.key(Nat, D.Node<T>, e), ids(T, SC.append(E.Item<T>, P, Q))), allin(T, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, t), ids(T, SC.append(E.Item<T>, P, Q))), mem_skip(T, BE.key(Nat, D.Node<T>, e), h, P, v, Q, L.subst(Cmp, z => {Cmp.is_eq(z) == False{} : Bool}, GT{}, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), Equal.sym(Cmp, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), GT{}, ec), {==}), L.and_left(mem(BE.key(Nat, D.Node<T>, e), ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), allin(T, t, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), a)), ih)

# Keys surviving del(h) of a store whose keys lie in P ++ h :: Q lie in P ++ Q.
def allin_del(-T: Data, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +h: Nat, +P: List<&2, E.Item<T>>, +v: T, +Q: List<&2, E.Item<T>>, +a: {allin(T, xs, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))) == True{} : Bool}) -> {allin(T, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, xs), ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      allin_del_c(T, h, e, t, P, v, Q, Nat.cmp(h, BE.key(Nat, D.Node<T>, e)), {==}, a, allin_del(T, t, h, P, v, Q, L.and_right(mem(BE.key(Nat, D.Node<T>, e), ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), allin(T, t, ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))), a)))

# A key outside l is absent from a store whose keys all lie in l.
def find_absent_c(-T: Data, +n: Nat, +e: BE.Entry<Nat, D.Node<T>>, +t: List<&2, BE.Entry<Nat, D.Node<T>>>, +l: List<&2, Nat>, c: Cmp, +ec: {Nat.cmp(n, BE.key(Nat, D.Node<T>, e)) == c : Cmp}, +a: {allin(T, Con{e, t}, l) == True{} : Bool}, +m: {mem(n, l) == False{} : Bool}, +ih: {S.find(~Nat, ~Nat.cmp, D.Node<T>, n, t) == None{} : Maybe<&2, D.Node<T>>}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, n, Con{e, t}) == None{} : Maybe<&2, D.Node<T>>}:
  match c:
    case EQ{}:
      Empty.absurd({S.find(~Nat, ~Nat.cmp, D.Node<T>, n, Con{e, t}) == None{} : Maybe<&2, D.Node<T>>}, L.true_false(Equal.trans(Bool, True{}, mem(n, l), False{}, Equal.sym(Bool, mem(n, l), True{}, L.subst(Nat, z => {mem(z, l) == True{} : Bool}, BE.key(Nat, D.Node<T>, e), n, Equal.sym(Nat, n, BE.key(Nat, D.Node<T>, e), O.nat_eq(n, BE.key(Nat, D.Node<T>, e), ec)), L.and_left(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l), a))), m)))
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(n, BE.key(Nat, D.Node<T>, e)), LT{}, ec) : {S.find_at(Nat, D.Node<T>, _, e, S.find(~Nat, ~Nat.cmp, D.Node<T>, n, t)) == None{} : Maybe<&2, D.Node<T>>}
      ih
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(n, BE.key(Nat, D.Node<T>, e)), GT{}, ec) : {S.find_at(Nat, D.Node<T>, _, e, S.find(~Nat, ~Nat.cmp, D.Node<T>, n, t)) == None{} : Maybe<&2, D.Node<T>>}
      ih

def find_absent(-T: Data, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +n: Nat, +l: List<&2, Nat>, +a: {allin(T, xs, l) == True{} : Bool}, +m: {mem(n, l) == False{} : Bool}) -> {S.find(~Nat, ~Nat.cmp, D.Node<T>, n, xs) == None{} : Maybe<&2, D.Node<T>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      find_absent_c(T, n, e, t, l, Nat.cmp(n, BE.key(Nat, D.Node<T>, e)), {==}, a, m, find_absent(T, t, n, l, L.and_right(mem(BE.key(Nat, D.Node<T>, e), l), allin(T, t, l), a), m))

def node_absent(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +n: Nat, +l: List<&2, Nat>, +g: {ninv(T, nodes) == True{} : Bool}, +a: {allin(T, nabs(T, nodes), l) == True{} : Bool}, +m: {mem(n, l) == False{} : Bool}) -> {D.node(T, nodes, n) == None{} : Maybe<&2, D.Node<T>>}:
  Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, nodes, n), S.find(~Nat, ~Nat.cmp, D.Node<T>, n, nabs(T, nodes)), None{}, get_eq(T, nodes, n, g), find_absent(T, nabs(T, nodes), n, l, a, m))
