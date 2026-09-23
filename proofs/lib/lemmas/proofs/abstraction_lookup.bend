import Base
import ./representation_access.bend as Access
import ./cache_populated.bend as Pop
import ./cache_delete_membership.bend as D
import ./map_routing.bend as R
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./refinement.bend as F
import ./abstraction_bindings.bend as B
import ./abstraction_identity.bend as Identity
import ./abstraction_recency.bend as Recency
import ./enumeration_suffix.bend as Enum
import ./cache_key_identity.bend as Key
import ./invariants.bend as Inv
import ./representation_parts.bend as Parts

# An abstract binding's exact key, value and deadline correspond to an actual
# lookup. This is independent of native enumeration order and needs no injective
# codec premise: encoded identity and native lookup uniqueness suffice here.
def from_origin(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, +entry: T.Entry<K, V>, valid: {F.storage_critbit(K, V, c) == True{} : Bool}, identities: {Recency.cache_identities(~K, ~encode, V, c) == True{} : Bool}, origin: Sigma<&2, &1, String, code => B.origin_at(K, V, c, code, entry)>) -> {C.lookup(K, V, c, Identity.entry_code(~K, ~encode, V, entry)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  (+code, member) = origin
  +found = Enum.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, valid, member)
  same = Key.lookup_code_identity(~K, ~encode, V, C.State{cap, table, order, life, counts, cb}, code, entry, identities, found)
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, Identity.entry_code(~K, ~encode, V, entry)), C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code), Some{entry}, Equal.cong(String, Maybe<&2, T.Entry<K, V>>, x => C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, x), Identity.entry_code(~K, ~encode, V, entry), code, Equal.sym(String, code, Identity.entry_code(~K, ~encode, V, entry), same)), found)

def binding(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +entry: T.Entry<K, V>, +valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, member: B.contains(T.Entry<K, V>, B.model_bindings(K, V, F.abstract(K, V, c)), entry)) -> {C.lookup(K, V, c, Identity.entry_code(~K, ~encode, V, entry)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}:
  from_origin(~K, ~encode, V, c, entry, R.and_left(F.storage_critbit(K, V, c), Pop.storage_populated(K, V, c) && D.membership(K, V, c), Access.get_storage(~K, ~encode, V, c, valid)), Access.get_identities(~K, ~encode, V, c, valid), B.abstraction_binding_origin(K, V, c, entry, member))

def string_binding(-V: Data, c: C.Cache<String, V>, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, member: B.contains(T.Entry<String, V>, B.model_bindings(String, V, F.abstract(String, V, c)), entry)) -> {C.lookup(String, V, c, Identity.entry_code(~String, ~Codec.string_encode, V, entry)) == Some{entry} : Maybe<&2, T.Entry<String, V>>}:
  binding(~String, ~Codec.string_encode, V, c, entry, valid, member)

def integer_binding(-V: Data, c: C.Cache<T.Integer, V>, entry: T.Entry<T.Integer, V>, valid: {Inv.representation(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}, member: B.contains(T.Entry<T.Integer, V>, B.model_bindings(T.Integer, V, F.abstract(T.Integer, V, c)), entry)) -> {C.lookup(T.Integer, V, c, Identity.entry_code(~T.Integer, ~Codec.integer_encode, V, entry)) == Some{entry} : Maybe<&2, T.Entry<T.Integer, V>>}:
  binding(~T.Integer, ~Codec.integer_encode, V, c, entry, valid, member)

def word64_binding(-V: Data, c: C.Cache<Word(64n), V>, entry: T.Entry<Word(64n), V>, valid: {Inv.representation(~Word(64n), ~Key.word64_encode, V, c) == True{} : Bool}, member: B.contains(T.Entry<Word(64n), V>, B.model_bindings(Word(64n), V, F.abstract(Word(64n), V, c)), entry)) -> {C.lookup(Word(64n), V, c, Identity.entry_code(~Word(64n), ~Key.word64_encode, V, entry)) == Some{entry} : Maybe<&2, T.Entry<Word(64n), V>>}:
  binding(~Word(64n), ~Key.word64_encode, V, c, entry, valid, member)
