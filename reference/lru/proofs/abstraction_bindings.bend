import Base
import ./refinement.bend as F
import ./map_lookup.bend as L
import ./map_routing.bend as R
import ../src/cache.bend as C
import ../spec/cache.bend as S
import ../types/model.bend as T

# Exact entry membership, preserving original key, value and deadline together.
def contains(-E: Data, xs: List<&2, E>, entry: E) -> Type:
  match xs:
    case Nil{}: Empty
    case Con{head, tail}: Either<&1, &1, {entry == head : E}, contains(E, tail, entry)>

law binding_head:
  for -K: Data
  for -V: Data
  for item: Maybe<&2, T.Entry<K, V>>
  for rest: List<&2, T.Entry<K, V>>
  for entry: T.Entry<K, V>
  for same: {Some{entry} == item : Maybe<&2, T.Entry<K, V>>}
  contains(T.Entry<K, V>, F.binding_cons(K, V, item, rest), entry)
def binding_head(K, V, item, rest, entry, same):
  match item:
    case None{}:
      Empty.absurd(contains(T.Entry<K, V>, rest, entry), R.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, T.Entry<K, V>>, Bool, m => Maybe.is_some(&2, T.Entry<K, V>, m), Some{entry}, None{}, same))))
    case Some{head}:
      Inl{Equal.cong(Maybe<&2, T.Entry<K, V>>, T.Entry<K, V>, m => Maybe.default(&2, T.Entry<K, V>, m, entry), Some{entry}, Some{head}, same)}

law binding_tail:
  for -K: Data
  for -V: Data
  for item: Maybe<&2, T.Entry<K, V>>
  for rest: List<&2, T.Entry<K, V>>
  for entry: T.Entry<K, V>
  for member: contains(T.Entry<K, V>, rest, entry)
  contains(T.Entry<K, V>, F.binding_cons(K, V, item, rest), entry)
def binding_tail(K, V, item, rest, entry, member):
  match item:
    case None{}: member
    case Some{head}: Inr{member}

law retains_listed_entry:
  for -K: Data
  for -V: Data
  for xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for +code: String
  for +entry: T.Entry<K, V>
  for member: L.listed(T.Entry<K, V>, xs, code, entry)
  contains(T.Entry<K, V>, F.bindings(K, V, xs), entry)
def retains_listed_entry(K, V, xs, code, entry, member):
  match xs:
    case Nil{}: Empty.absurd(contains(T.Entry<K, V>, Nil{}, entry), member)
    case Con{Tuple{stored, +item}, +tail}:
      match member:
        case Inl{pair}:
          (key_same, value_same) = pair
          binding_head(K, V, item, F.bindings(K, V, tail), entry, value_same)
        case Inr{in_tail}:
          binding_tail(K, V, item, F.bindings(K, V, tail), entry, retains_listed_entry(K, V, tail, code, entry, in_tail))

def model_bindings(-K: Data, -V: Data, s: S.Model<K, V>) -> List<&2, T.Entry<K, V>>:
  S.Abstract{cap, bindings, order, lifetime, counts, cb} = s
  bindings

# Actual successful lookup cannot be discarded by the actual abstraction.
# This does not yet establish full recency faithfulness or reachability.
law lookup_retained_by_abstraction:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  contains(T.Entry<K, V>, model_bindings(K, V, F.abstract(K, V, c)), entry)
def lookup_retained_by_abstraction(K, V, c, code, entry, found):
  match c:
    case C.State{+cap, +table, +order, +lifetime, +counts, +cb}:
      retains_listed_entry(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), code, entry, F.lookup_enumerated(K, V, cap, table, order, lifetime, counts, cb, code, entry, found))

def origin(-K: Data, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, entry: T.Entry<K, V>) -> Type:
  Sigma<&2, &1, String, code => L.listed(T.Entry<K, V>, xs, code, entry)>

law lift_origin:
  for -K: Data
  for -V: Data
  for stored: String
  for item: Maybe<&2, T.Entry<K, V>>
  for tail: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for entry: T.Entry<K, V>
  for source: origin(K, V, tail, entry)
  origin(K, V, Con{Tuple{stored, item}, tail}, entry)
def lift_origin(K, V, stored, item, tail, entry, source):
  (code, member) = source
  (code, Inr{member})

law binding_origin:
  for -K: Data
  for -V: Data
  for xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>
  for +entry: T.Entry<K, V>
  for member: contains(T.Entry<K, V>, F.bindings(K, V, xs), entry)
  origin(K, V, xs, entry)
def binding_origin(K, V, xs, entry, member):
  match xs:
    case Nil{}: Empty.absurd(origin(K, V, Nil{}, entry), member)
    case Con{Tuple{+stored, None{}}, +tail}:
      lift_origin(K, V, stored, None{}, tail, entry, binding_origin(K, V, tail, entry, member))
    case Con{Tuple{+stored, Some{+head}}, +tail}:
      match member:
        case Inl{same}:
          (stored, Inl{({==}, Equal.cong(T.Entry<K, V>, Maybe<&2, T.Entry<K, V>>, e => Some{e}, entry, head, same))})
        case Inr{rest}:
          lift_origin(K, V, stored, Some{head}, tail, entry, binding_origin(K, V, tail, entry, rest))


def origin_at(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>) -> Type:
  C.State{cap, table, order, life, counts, cb} = c
  L.listed(T.Entry<K, V>, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), code, entry)

# The abstraction cannot invent entries either: each abstract binding is an
# exact native enumerated binding at some encoded key, without a validity premise.
law abstraction_binding_origin:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +entry: T.Entry<K, V>
  for member: contains(T.Entry<K, V>, model_bindings(K, V, F.abstract(K, V, c)), entry)
  Sigma<&2, &1, String, code => origin_at(K, V, c, code, entry)>
def abstraction_binding_origin(K, V, c, entry, member):
  match c:
    case C.State{cap, +table, order, life, counts, cb}:
      binding_origin(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), entry, member)
