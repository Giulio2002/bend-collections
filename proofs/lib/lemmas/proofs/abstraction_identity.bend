import Base
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_lookup.bend as L
import ./map_routing.bend as R
import ./recency_unique.bend as U

# Original-key identity at an exact enumerated binding. The encoder is a static
# template parameter, as in the representation predicate; no injectivity is
# assumed by this direction of correspondence.
def entry_code(~K: Data, ~encode: K -> String, -V: Data, entry: T.Entry<K, V>) -> String:
  T.Item{key, value, deadline} = entry
  encode(key)

def head_identity(~K: Data, ~encode: K -> String, -V: Data, +stored: String, item: Maybe<&2, T.Entry<K, V>>, +tail: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +code: String, +entry: T.Entry<K, V>, valid: {Inv.identities(~K, ~encode, V, Con{Tuple{stored, item}, tail}) == True{} : Bool}, same_code: {code == stored : String}, same_entry: {Some{entry} == item : Maybe<&2, T.Entry<K, V>>}) -> {code == entry_code(~K, ~encode, V, entry) : String}:
  match item:
    case None{}:
      Empty.absurd({code == entry_code(~K, ~encode, V, entry) : String}, R.false_true(valid))
    case Some{T.Item{+key, +value, +deadline}}:
      %Equal.sym(String, code, stored, same_code) : {_ == entry_code(~K, ~encode, V, entry) : String}
      %Equal.sym(T.Entry<K, V>, entry, T.Item{key, value, deadline}, Equal.cong(Maybe<&2, T.Entry<K, V>>, T.Entry<K, V>, m => Maybe.default(&2, T.Entry<K, V>, m, entry), Some{entry}, Some{T.Item{key, value, deadline}}, same_entry)) : {stored == entry_code(~K, ~encode, V, _) : String}
      U.equal_boolean(stored, encode(key), R.and_left(String.eq(stored, encode(key)), Inv.identities(~K, ~encode, V, tail), valid))

def tail_identity(~K: Data, ~encode: K -> String, -V: Data, stored: String, item: Maybe<&2, T.Entry<K, V>>, +tail: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, valid: {Inv.identities(~K, ~encode, V, Con{Tuple{stored, item}, tail}) == True{} : Bool}) -> {Inv.identities(~K, ~encode, V, tail) == True{} : Bool}:
  match item:
    case None{}: Empty.absurd({Inv.identities(~K, ~encode, V, tail) == True{} : Bool}, R.false_true(valid))
    case Some{T.Item{key, value, deadline}}:
      R.and_right(String.eq(stored, encode(key)), Inv.identities(~K, ~encode, V, tail), valid)

def listed_identity(~K: Data, ~encode: K -> String, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +code: String, +entry: T.Entry<K, V>, valid: {Inv.identities(~K, ~encode, V, xs) == True{} : Bool}, member: L.listed(T.Entry<K, V>, xs, code, entry)) -> {code == entry_code(~K, ~encode, V, entry) : String}:
  match xs:
    case Nil{}: Empty.absurd({code == entry_code(~K, ~encode, V, entry) : String}, member)
    case Con{Tuple{+stored, +item}, +tail}:
      match member:
        case Inl{pair}:
          (same_code, same_entry) = pair
          head_identity(~K, ~encode, V, stored, item, tail, code, entry, valid, same_code, same_entry)
        case Inr{rest}:
          listed_identity(~K, ~encode, V, tail, code, entry, tail_identity(~K, ~encode, V, stored, item, tail, valid), rest)
