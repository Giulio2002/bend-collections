import Base
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./abstraction_bindings.bend as B
import ./map_routing.bend as Logic

def key(-K: Data, -V: Data, entry: T.Entry<K, V>) -> K:
  T.Item{k, value, deadline} = entry
  k

def certificate(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, query: K, result: Maybe<&2, T.Entry<K, V>>) -> Type:
  match result:
    case None{}: Unit
    case Some{+entry}:
      B.contains(T.Entry<K, V>, bindings, entry) & {same(key(K, V, entry))(query) == True{} : Bool}

def lift(~K: Data, ~same: K -> K -> Bool, -V: Data, head: T.Entry<K, V>, rest: List<&2, T.Entry<K, V>>, query: K, result: Maybe<&2, T.Entry<K, V>>, proof: certificate(~K, ~same, V, rest, query, result)) -> certificate(~K, ~same, V, Con{head, rest}, query, result):
  match result:
    case None{}: Unit{}
    case Some{entry}:
      (member, matches) = proof
      (Inr{member}, matches)

def choose(~K: Data, ~same: K -> K -> Bool, -V: Data, +head: T.Entry<K, V>, rest: List<&2, T.Entry<K, V>>, query: K, result: Maybe<&2, T.Entry<K, V>>, flag: Bool, checked: {same(key(K, V, head))(query) == flag : Bool}, proof: certificate(~K, ~same, V, rest, query, result)) -> certificate(~K, ~same, V, Con{head, rest}, query, S.choose_entry(K, V, head, result, flag)):
  match flag:
    case False{}: lift(~K, ~same, V, head, rest, query, result, proof)
    case True{}: (Inl{{==}}, checked)

# The independent finite-map lookup returns only an actual matching binding.
def sound(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, +query: K) -> certificate(~K, ~same, V, bindings, query, S.find(~K, ~same, V, bindings, query)):
  match bindings:
    case Nil{}: Unit{}
    case Con{T.Item{+k, +value, +deadline}, +rest}:
      choose(~K, ~same, V, T.Item{k, value, deadline}, rest, query, S.find(~K, ~same, V, rest, query), same(k)(query), {==}, sound(~K, ~same, V, rest, query))

def returned(~K: Data, ~same: K -> K -> Bool, -V: Data, +bindings: List<&2, T.Entry<K, V>>, +query: K, +entry: T.Entry<K, V>, found: {S.find(~K, ~same, V, bindings, query) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> B.contains(T.Entry<K, V>, bindings, entry) & {same(key(K, V, entry))(query) == True{} : Bool}:
  %found : certificate(~K, ~same, V, bindings, query, _)
  sound(~K, ~same, V, bindings, query)

def string_same(a: String) -> String -> Bool:
  b => String.eq(a, b)

def string_returned(-V: Data, bindings: List<&2, T.Entry<String, V>>, query: String, entry: T.Entry<String, V>, found: {S.find(~String, ~string_same, V, bindings, query) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> B.contains(T.Entry<String, V>, bindings, entry) & {String.eq(key(String, V, entry), query) == True{} : Bool}:
  returned(~String, ~string_same, V, bindings, query, entry, found)

def choose_presence(-K: Data, -V: Data, head: T.Entry<K, V>, +result: Maybe<&2, T.Entry<K, V>>, flag: Bool) -> {Maybe.is_some(&2, T.Entry<K, V>, S.choose_entry(K, V, head, result, flag)) == Bool.or(flag, Maybe.is_some(&2, T.Entry<K, V>, result)) : Bool}:
  match flag:
    case False{}: {==}
    case True{}: {==}

def or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def head_present(~K: Data, ~same: K -> K -> Bool, -V: Data, +original: K, +value: V, +deadline: T.Int64, +rest: List<&2, T.Entry<K, V>>, +query: K, matched: {same(original)(query) == True{} : Bool}) -> {Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, Con{T.Item{original, value, deadline}, rest}, query)) == True{} : Bool}:
  Equal.trans(Bool, Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, Con{T.Item{original, value, deadline}, rest}, query)), Bool.or(same(original)(query), Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query))), True{}, choose_presence(K, V, T.Item{original, value, deadline}, S.find(~K, ~same, V, rest, query), same(original)(query)), Equal.cong(Bool, Bool, b => Bool.or(b, Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query))), same(original)(query), True{}, matched))

def tail_present(~K: Data, ~same: K -> K -> Bool, -V: Data, +original: K, +value: V, +deadline: T.Int64, +rest: List<&2, T.Entry<K, V>>, +query: K, present: {Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query)) == True{} : Bool}) -> {Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, Con{T.Item{original, value, deadline}, rest}, query)) == True{} : Bool}:
  Equal.trans(Bool, Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, Con{T.Item{original, value, deadline}, rest}, query)), Bool.or(same(original)(query), Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query))), True{}, choose_presence(K, V, T.Item{original, value, deadline}, S.find(~K, ~same, V, rest, query), same(original)(query)), Equal.trans(Bool, Bool.or(same(original)(query), Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query))), Bool.or(same(original)(query), True{}), True{}, Equal.cong(Bool, Bool, b => Bool.or(same(original)(query), b), Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, rest, query)), True{}, present), or_true(same(original)(query))))

# A matching member prevents an abstract lookup miss, irrespective of binding
# list order and without assuming keys are unique.
def member_present(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, +query: K, +entry: T.Entry<K, V>, matched: {same(key(K, V, entry))(query) == True{} : Bool}, member: B.contains(T.Entry<K, V>, bindings, entry)) -> {Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, bindings, query)) == True{} : Bool}:
  match bindings:
    case Nil{}: Empty.absurd({False{} == True{} : Bool}, member)
    case Con{T.Item{+original, +value, +deadline}, +rest}:
      match member:
        case Inl{eq}:
          head_present(~K, ~same, V, original, value, deadline, rest, query, Equal.trans(Bool, same(original)(query), same(key(K, V, entry))(query), True{}, Equal.cong(T.Entry<K, V>, Bool, e => same(key(K, V, e))(query), T.Item{original, value, deadline}, entry, Equal.sym(T.Entry<K, V>, entry, T.Item{original, value, deadline}, eq)), matched))
        case Inr{tail}:
          tail_present(~K, ~same, V, original, value, deadline, rest, query, member_present(~K, ~same, V, rest, query, entry, matched, tail))

def string_member_present(-V: Data, bindings: List<&2, T.Entry<String, V>>, query: String, entry: T.Entry<String, V>, matched: {String.eq(key(String, V, entry), query) == True{} : Bool}, member: B.contains(T.Entry<String, V>, bindings, entry)) -> {Maybe.is_some(&2, T.Entry<String, V>, S.find(~String, ~string_same, V, bindings, query)) == True{} : Bool}:
  member_present(~String, ~string_same, V, bindings, query, entry, matched, member)
