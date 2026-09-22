import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./abstraction_lookup.bend as Abstract
import ./abstraction_bindings.bend as B
import ./abstraction_identity.bend as Identity
import ./cache_key_identity.bend as Key
import ./representation_access.bend as Access
import ./map_routing.bend as Logic
import ./recency_unique.bend as Unique
import ./map_key_membership.bend as Keys

def reflects(~K: Data, ~same: K -> K -> Bool) -> Type:
  @+a: K -> @+b: K -> {same(a)(b) == True{} : Bool} -> {a == b : K}

def reflexive(~K: Data, ~same: K -> K -> Bool) -> Type:
  @+a: K -> {same(a)(a) == True{} : Bool}

def matching(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, entry: T.Entry<K, V>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, reflection: reflects(~K, ~same), proof: B.contains(T.Entry<K, V>, B.model_bindings(K, V, F.abstract(K, V, c)), entry) & {same(Lookup.key(K, V, entry))(query) == True{} : Bool}) -> {C.lookup(K, V, c, encode(query)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}:
  T.Item{+original, +value, +deadline} = entry
  (member, matched) = proof
  eq = reflection(original, query, matched)
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, c, encode(query)), C.lookup(K, V, c, encode(original)), Some{T.Item{original, value, deadline}}, Equal.cong(K, Maybe<&2, T.Entry<K, V>>, k => C.lookup(K, V, c, encode(k)), query, original, Equal.sym(K, original, query, eq)), Abstract.binding(~K, ~encode, V, c, T.Item{original, value, deadline}, valid, member))

def model_found(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, +entry: T.Entry<K, V>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, reflection: reflects(~K, ~same), found: {S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {C.lookup(K, V, c, encode(query)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}:
  matching(~K, ~encode, ~same, V, c, query, entry, valid, reflection, Lookup.returned(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query, entry, found))

def native_present(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, entry: T.Entry<K, V>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, injective: Key.injective(~K, ~encode), reflexivity: reflexive(~K, ~same), +found: {C.lookup(K, V, c, encode(query)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> {Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query)) == True{} : Bool}:
  T.Item{+original, +value, +deadline} = entry
  eq = Key.lookup_original_key(~K, ~encode, V, c, query, original, value, deadline, injective, Access.get_identities(~K, ~encode, V, c, valid), found)
  matched = Equal.trans(Bool, same(original)(query), same(query)(query), True{}, Equal.cong(K, Bool, k => same(k)(query), original, query, Equal.sym(K, query, original, eq)), reflexivity(query))
  Lookup.member_present(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query, T.Item{original, value, deadline}, matched, B.lookup_retained_by_abstraction(K, V, c, encode(query), T.Item{original, value, deadline}, found))

def native_missing(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, injective: Key.injective(~K, ~encode), reflexivity: reflexive(~K, ~same), missing: {S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query) == None{} : Maybe<&2, T.Entry<K, V>>}, native: Maybe<&2, T.Entry<K, V>>, checked: {C.lookup(K, V, c, encode(query)) == native : Maybe<&2, T.Entry<K, V>>}) -> {C.lookup(K, V, c, encode(query)) == None{} : Maybe<&2, T.Entry<K, V>>}:
  match native:
    case None{}: checked
    case Some{entry}:
      Empty.absurd({C.lookup(K, V, c, encode(query)) == None{} : Maybe<&2, T.Entry<K, V>>}, Logic.false_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query)), True{}, Equal.sym(Bool, Maybe.is_some(&2, T.Entry<K, V>, S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query)), False{}, Equal.cong(Maybe<&2, T.Entry<K, V>>, Bool, m => Maybe.is_some(&2, T.Entry<K, V>, m), S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query), None{}, missing)), native_present(~K, ~encode, ~same, V, c, query, entry, valid, injective, reflexivity, checked))))

def decision(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, injective: Key.injective(~K, ~encode), reflection: reflects(~K, ~same), reflexivity: reflexive(~K, ~same), model: Maybe<&2, T.Entry<K, V>>, checked: {S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query) == model : Maybe<&2, T.Entry<K, V>>}) -> {C.lookup(K, V, c, encode(query)) == model : Maybe<&2, T.Entry<K, V>>}:
  match model:
    case None{}: native_missing(~K, ~encode, ~same, V, c, query, valid, injective, reflexivity, checked, C.lookup(K, V, c, encode(query)), {==})
    case Some{entry}: model_found(~K, ~encode, ~same, V, c, query, entry, valid, reflection, checked)

# Exact finite-map lookup, including absence, with independently specified key
# equality. Representation and custom-codec/equality contracts are explicit.
def correspondence(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, +c: C.Cache<K, V>, +query: K, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, injective: Key.injective(~K, ~encode), reflection: reflects(~K, ~same), reflexivity: reflexive(~K, ~same)) -> {C.lookup(K, V, c, encode(query)) == S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query) : Maybe<&2, T.Entry<K, V>>}:
  decision(~K, ~encode, ~same, V, c, query, valid, injective, reflection, reflexivity, S.find(~K, ~same, V, B.model_bindings(K, V, F.abstract(K, V, c)), query), {==})

def string_reflexive(+key: String) -> {String.eq(key, key) == True{} : Bool}:
  Keys.eq_true(key, key, {==})

def string_lookup(-V: Data, c: C.Cache<String, V>, query: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, c, Codec.string_encode(query)) == S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), query) : Maybe<&2, T.Entry<String, V>>}:
  correspondence(~String, ~Codec.string_encode, ~Lookup.string_same, V, c, query, valid, Codec.string_injective, Unique.equal_boolean, string_reflexive)
