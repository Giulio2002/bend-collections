import Base
import ../spec/public_commands.bend as Public
import ../spec/traces.bend as Traces
import ../types/model.bend as T
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/effectful_operations.bend as E
import ../spec/effectful_aggregate.bend as A

# Properties of the independent failure specification, not host refinement.
def same(a: String) -> String -> Bool:
  b => String.eq(a, b)

def add_rejection(-V: Data, prepared: S.Model<String, V>, key: String, value: V, ns: T.Int64, evicted: Bool, error: Clock.Error, remaining: List<&2, Clock.Event>) -> {E.sampled_add(~String, ~same, V, E.Prepared{prepared, key, evicted}, value, ns, Clock.Rejected{error, remaining}) == E.Failed{prepared, error, remaining, 1n} : E.Outcome<String, V>}:
  {==}

def refresh_rejection(-V: Data, prepared: S.Model<String, V>, entry: T.Entry<String, V>, ns: T.Int64, error: Clock.Error, remaining: List<&2, Clock.Event>) -> {E.sampled_refresh(~String, ~same, V, prepared, entry, ns, Clock.Rejected{error, remaining}) == E.Failed{prepared, error, remaining, 1n} : E.Outcome<String, V>}:
  {==}

def invalid_request(reason: String, remaining: List<&2, Clock.Event>) -> {Clock.request(Con{Clock.InvalidSample{reason}, remaining}) == Clock.Rejected{Clock.Invalid{reason}, remaining} : Clock.Reply}:
  {==}

def throwing_request(reason: String, remaining: List<&2, Clock.Event>) -> {Clock.request(Con{Clock.ProviderException{reason}, remaining}) == Clock.Rejected{Clock.Thrown{reason}, remaining} : Clock.Reply}:
  {==}

def failed_prefix_keeps_removal(-K: Data, -V: Data, entry: T.Entry<K, V>, error: Clock.Error, removed: List<&2, T.Entry<K, V>>, retained: List<&2, T.Entry<K, V>>, remaining: List<&2, Clock.Event>, requests: Nat) -> {A.prepend(K, V, entry, A.Failed{error, removed, retained, remaining, requests}) == A.Failed{error, Con{entry, removed}, retained, remaining, 1n+requests} : A.Prefix<K, V>}:
  {==}

def immortal_preserves_next_event(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>, unused: A.Prefix<K, V>) -> {A.sentinel(K, V, entry, tail, events, unused, True{}) == A.Finished{Nil{}, Con{entry, tail}, events, 0n} : A.Prefix<K, V>}:
  {==}

def expired_oldest_keeps_key(-V: Data, s: S.Model<String, V>, zero_key: String, zero_value: V, original: String, oldkey: String, stale: V, deadline: T.Int64) -> {Public.project(~String, ~same, V, s, zero_key, zero_value, Some{T.Item{oldkey, stale, deadline}}, False{}, Public.CapturedOldest{original}) == Public.Oldest{original, zero_value, False{}} : Public.Reply<String, V>}:
  {==}

def public_failure_retains_state(-V: Data, s: S.Model<String, V>, zero_key: String, zero_value: V, kind: Public.Projection<String>, error: Clock.Error, remaining: List<&2, Clock.Event>, requests: Nat) -> {Public.effect(~String, ~same, V, zero_key, zero_value, kind, E.Failed{s, error, remaining, requests}) == Public.Failed{s, error, remaining, requests} : Public.Result<String, V>}:
  {==}

def failed_trace_state(-K: Data, -V: Data, s: S.Model<K, V>, error: Clock.Error, remaining: List<&2, Clock.Event>, requests: Nat) -> {Traces.state(K, V, Public.Failed{s, error, remaining, requests}) == s : S.Model<K, V>}:
  {==}
