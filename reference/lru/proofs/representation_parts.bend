import Base
import ./cache_key_identity.bend as KeyIdentity
import ../src/codec.bend as Codec
import ./refinement.bend as F
import ../src/cache.bend as C
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./abstraction_identity.bend as Identity
import ./abstraction_size.bend as Size
import ./map_populated_inverse.bend as PopInverse
import ./cache_add_capacity.bend as Add
import ./abstraction_recency.bend as Recency

def identities_packed(~K: Data, ~encode: K -> String, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>, +valid: {Inv.identities(~K, ~encode, V, xs) == True{} : Bool}) -> {Size.packed(K, V, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{code, None{}}, tail}:
      Empty.absurd({False{} == True{} : Bool}, R.false_true(valid))
    case Con{Tuple{+code, Some{+entry}}, +tail}:
      identities_packed(~K, ~encode, V, tail, Identity.tail_identity(~K, ~encode, V, code, Some{entry}, tail, valid))

def components(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, life: T.Int64, counts: T.Metrics, cb: Bool, +valid: {Inv.representation(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}) -> {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}:
  +e7 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), valid)
  +e6 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), e7)
  +e5 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), e6)
  +e4 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), e5)
  +e3 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), e4)
  +e2 = R.and_left(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap), Inv.unique(order), e3)
  +e1 = R.and_left(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap), e2)
  (e1, R.and_right(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap), e2), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap), Inv.unique(order), e3), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), e4), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), e5), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), e6), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), e7), R.and_right(Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && Inv.unique(order) && Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) && Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), valid))

# All capacity premises are extracted from the existing joint predicate. Its
# preservation/reachability is a separate, still-open theorem.
def add_bounded_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, key: K, value: V, ns: T.Int64, now: T.Int64, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, C.State{cap, table, order, life, counts, cb}, key, value, ns, now))), C.capacity(K, V, C.State{cap, table, order, life, counts, cb})) == True{} : Bool}:
  (positive, bound, order_unique, keys_unique, included, reverse, critbit, identities) = facts
  Add.add_with_lifetime_bounded(K, V, encode, C.State{cap, table, order, life, counts, cb}, key, value, ns, now, positive, bound, critbit, PopInverse.packed_tree(K, V, table, identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), included, reverse)

def add_bounded(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, key: K, value: V, ns: T.Int64, now: T.Int64, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))), C.capacity(K, V, c)) == True{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  add_bounded_parts(~K, ~encode, V, cap, table, order, life, counts, cb, key, value, ns, now, components(~K, ~encode, V, cap, table, order, life, counts, cb, valid))

def recency_finish(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, critbit: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, included: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, C.State{cap, table, order, life, counts, cb}))) == order : List<&2, String>}:
  Recency.faithful(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, critbit, PopInverse.packed_tree(K, V, table, identities_packed(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), identities)), identities, included)

def recency_faithful_parts(~K: Data, ~encode: K -> String, -V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool} & {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, C.State{cap, table, order, life, counts, cb}))) == Recency.native_order(K, V, C.State{cap, table, order, life, counts, cb}) : List<&2, String>}:
  (positive, bound, order_unique, keys_unique, included, reverse, critbit, identities) = facts
  recency_finish(~K, ~encode, V, cap, table, order, life, counts, cb, critbit, identities, included)

def recency_faithful(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> {Recency.encode_keys(~K, ~encode, Recency.model_order(K, V, F.abstract(K, V, c))) == Recency.native_order(K, V, c) : List<&2, String>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  recency_faithful_parts(~K, ~encode, V, cap, table, order, life, counts, cb, components(~K, ~encode, V, cap, table, order, life, counts, cb, valid))

def initialized(~K: Data, ~encode: K -> String, -V: Data, n: Nat) -> {Inv.representation(~K, ~encode, V, C.init(K, V, 1n+n)) == True{} : Bool}:
  {==}

law string_add_bounded:
  for -V: Data
  for c: C.Cache<String, V>
  for key: String
  for value: V
  for ns: T.Int64
  for now: T.Int64
  for valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  {Nat.is_le(C.len(String, V, C.step_cache(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now))), C.capacity(String, V, c)) == True{} : Bool}
def string_add_bounded(V, c, key, value, ns, now, valid):
  add_bounded(~String, ~Codec.string_encode, V, c, key, value, ns, now, valid)

law string_recency:
  for -V: Data
  for c: C.Cache<String, V>
  for valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  {Recency.encode_keys(~String, ~Codec.string_encode, Recency.model_order(String, V, F.abstract(String, V, c))) == Recency.native_order(String, V, c) : List<&2, String>}
def string_recency(V, c, valid):
  recency_faithful(~String, ~Codec.string_encode, V, c, valid)

law string_initialized:
  for -V: Data
  for n: Nat
  {Inv.representation(~String, ~Codec.string_encode, V, C.init(String, V, 1n+n)) == True{} : Bool}
def string_initialized(V, n):
  initialized(~String, ~Codec.string_encode, V, n)

law integer_add_bounded:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for key: T.Integer
  for value: V
  for ns: T.Int64
  for now: T.Int64
  for valid: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  {Nat.is_le(C.len(T.Integer, V, C.step_cache(T.Integer, V, C.add_with_lifetime(T.Integer, V, Codec.integer_encode, c, key, value, ns, now))), C.capacity(T.Integer, V, c)) == True{} : Bool}
def integer_add_bounded(V, c, key, value, ns, now, valid):
  add_bounded(~T.Integer, ~Codec.integer_encode, V, c, key, value, ns, now, valid)

law integer_recency:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for valid: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  {Recency.encode_keys(~T.Integer, ~Codec.integer_encode, Recency.model_order(T.Integer, V, F.abstract(T.Integer, V, c))) == Recency.native_order(T.Integer, V, c) : List<&2, String>}
def integer_recency(V, c, valid):
  recency_faithful(~T.Integer, ~Codec.integer_encode, V, c, valid)

law integer_initialized:
  for -V: Data
  for n: Nat
  {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.init(T.Integer, V, 1n+n)) == True{} : Bool}
def integer_initialized(V, n):
  initialized(~T.Integer, ~Codec.integer_encode, V, n)

law word64_add_bounded:
  for -V: Data
  for c: C.Cache<Word(64n), V>
  for key: Word(64n)
  for value: V
  for ns: T.Int64
  for now: T.Int64
  for valid: {Inv.representation(~Word(64n), ~KeyIdentity.word64_encode, V, c) == True{} : Bool}
  {Nat.is_le(C.len(Word(64n), V, C.step_cache(Word(64n), V, C.add_with_lifetime(Word(64n), V, KeyIdentity.word64_encode, c, key, value, ns, now))), C.capacity(Word(64n), V, c)) == True{} : Bool}
def word64_add_bounded(V, c, key, value, ns, now, valid):
  add_bounded(~Word(64n), ~KeyIdentity.word64_encode, V, c, key, value, ns, now, valid)

law word64_recency:
  for -V: Data
  for c: C.Cache<Word(64n), V>
  for valid: {Inv.representation(~Word(64n), ~KeyIdentity.word64_encode, V, c) == True{} : Bool}
  {Recency.encode_keys(~Word(64n), ~KeyIdentity.word64_encode, Recency.model_order(Word(64n), V, F.abstract(Word(64n), V, c))) == Recency.native_order(Word(64n), V, c) : List<&2, String>}
def word64_recency(V, c, valid):
  recency_faithful(~Word(64n), ~KeyIdentity.word64_encode, V, c, valid)

law word64_initialized:
  for -V: Data
  for n: Nat
  {Inv.representation(~Word(64n), ~KeyIdentity.word64_encode, V, C.init(Word(64n), V, 1n+n)) == True{} : Bool}
def word64_initialized(V, n):
  initialized(~Word(64n), ~KeyIdentity.word64_encode, V, n)
