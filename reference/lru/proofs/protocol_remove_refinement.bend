import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./remove_refinement.bend as Remove

# The existing native conditional uses the detached step's actual flag, just
# as the facade's post-commit branch does. This is not a TS execution model.
def present(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, evict: Bool) -> {P.finish_detached(K, V, P.detach_present(K, V, c, code, entry), evict) == C.remove_present(K, V, c, code, evict, entry) : C.Step<K, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def branch(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, result: Maybe<&2, T.Entry<K, V>>, evict: Bool) -> {P.finish_detached(K, V, P.detach_found(K, V, c, code, result), evict) == C.remove_found(K, V, c, code, evict, result) : C.Step<K, V>}:
  match result:
    case None{}: {==}
    case Some{entry}: present(K, V, c, code, entry, evict)

# Arbitrary actual state and encoded key; no successful-lookup assumption.
def composition(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String, evict: Bool) -> {P.finish_detached(K, V, P.detach(K, V, c, code), evict) == C.remove_encoded(K, V, c, code, evict) : C.Step<K, V>}:
  branch(K, V, c, code, C.lookup(K, V, c, code), evict)

def string_operation(-V: Data, +c: C.Cache<String, V>, +key: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, P.finish_detached(String, V, P.detach(String, V, c, key), False{})), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key)):
  %Equal.sym(C.Step<String, V>, P.finish_detached(String, V, P.detach(String, V, c, key), False{}), C.remove_encoded(String, V, c, key, False{}), composition(String, V, c, key, False{})) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, _), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key))
  Remove.operation(V, c, key, valid, disabled)
