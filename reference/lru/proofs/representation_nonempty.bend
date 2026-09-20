import Base
import ./cache_key_identity.bend as KeyIdentity
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_key_membership.bend as Keys

# A universally quantified nonempty public-core witness. This does not replace
# induction over arbitrary operations; it shows the joint predicate is realized
# by actual nonempty states, with arbitrary keys, values, time and lifetime.
def first_add(~K: Data, ~encode: K -> String, -V: Data, +key: K, value: V, ns: T.Int64, now: T.Int64) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, C.init(K, V, 1n), key, value, ns, now))) == True{} : Bool}:
  +code = encode(key)
  %Equal.sym(Bool, String.eq(code, code), True{}, Keys.eq_true(code, code, {==})) : {((_ || False{}) && True{}) && ((_ || False{}) && True{}) && True{} && (_ && True{}) == True{} : Bool}
  {==}

law string_first_add:
  for -V: Data
  for key: String
  for value: V
  for ns: T.Int64
  for now: T.Int64
  {Inv.representation(~String, ~Codec.string_encode, V, C.step_cache(String, V, C.add_with_lifetime(String, V, Codec.string_encode, C.init(String, V, 1n), key, value, ns, now))) == True{} : Bool}
def string_first_add(V, key, value, ns, now):
  first_add(~String, ~Codec.string_encode, V, key, value, ns, now)

law integer_first_add:
  for -V: Data
  for key: T.Integer
  for value: V
  for ns: T.Int64
  for now: T.Int64
  {Inv.representation(~T.Integer, ~Codec.integer_encode, V, C.step_cache(T.Integer, V, C.add_with_lifetime(T.Integer, V, Codec.integer_encode, C.init(T.Integer, V, 1n), key, value, ns, now))) == True{} : Bool}
def integer_first_add(V, key, value, ns, now):
  first_add(~T.Integer, ~Codec.integer_encode, V, key, value, ns, now)

law word64_first_add:
  for -V: Data
  for key: Word(64n)
  for value: V
  for ns: T.Int64
  for now: T.Int64
  {Inv.representation(~Word(64n), ~KeyIdentity.word64_encode, V, C.step_cache(Word(64n), V, C.add_with_lifetime(Word(64n), V, KeyIdentity.word64_encode, C.init(Word(64n), V, 1n), key, value, ns, now))) == True{} : Bool}
def word64_first_add(V, key, value, ns, now):
  first_add(~Word(64n), ~KeyIdentity.word64_encode, V, key, value, ns, now)
