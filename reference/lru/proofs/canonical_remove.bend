import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./canonical.bend as Can
import ./spec_lookup.bend as Lookup
import ./recency_unique.bend as Unique

# String instance of the canonical Remove congruence (kept separate so that
# removal-state proofs do not depend on it).
def remove_congruence(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, +key: String, related: E.states(~String, ~Lookup.string_same, V, a, b)) -> E.states(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, a, key)), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, b, key))):
  Can.remove_congruence(~String, ~Lookup.string_same, ~Unique.equal_boolean, V, a, b, key, related)

