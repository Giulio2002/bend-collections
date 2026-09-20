import Base
import ./map_lookup.bend as L
import ./map_enumeration.bend as E
import ./map_insert.bend as I
import ./refinement.bend as F
import ../src/cache.bend as C
import ../types/model.bend as T

def entries(-K: Data, -V: Data, c: C.Cache<K, V>) -> List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>:
  C.State{cap, table, order, life, counts, cb} = c
  Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)

law append_cons:
  for -A: Data
  for xs: List<&2, A>
  for +head: A
  for +tail: List<&2, A>
  {List.append(&2, A, xs, Con{head, tail}) == List.append(&2, A, List.append(&2, A, xs, Con{head, Nil{}}), tail) : List<&2, A>}
def append_cons(A, xs, head, tail):
  match xs:
    case Nil{}: {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, A>, List<&2, A>, ys => Con{x, ys}, List.append(&2, A, rest, Con{head, tail}), List.append(&2, A, List.append(&2, A, rest, Con{head, Nil{}}), tail), append_cons(A, rest, head, tail))

law listed_prefix:
  for -V: Data
  for prefix: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for key: String
  for value: V
  for member: L.listed(V, xs, key, value)
  L.listed(V, List.append(&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>, prefix, xs), key, value)
def listed_prefix(V, prefix, xs, key, value, member):
  match prefix:
    case Nil{}: member
    case Con{Tuple{stored, item}, tail}: Inr{listed_prefix(V, tail, xs, key, value, member)}

law lookup:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for member: L.listed(T.Entry<K, V>, entries(K, V, c), code, entry)
  {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
def lookup(K, V, c, code, entry, valid, member):
  C.State{cap, +table, order, life, counts, cb} = c
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), Some{entry}, F.lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), E.enumerated_lookup(T.Entry<K, V>, table, code, entry, valid, member))
