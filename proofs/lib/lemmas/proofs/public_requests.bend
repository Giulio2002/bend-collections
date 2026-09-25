import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/clock.bend as Clock
import ../spec/public_commands.bend as PC
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_read.bend as PublicRead
import ./public_simple.bend as PublicSimple
import ./public_config.bend as PublicConfig
import ./public_oldest_ops.bend as PublicOldest
import ./public_add.bend as PublicAdd
import ./public_refresh.bend as PublicRefresh
import ./public_aggregate.bend as PublicAggregate
import ./public_diagnostics.bend as PublicDiagnostics

# Every public request of the actual start/drive machine refines the
# independent typed command semantics, for every provider-event list.
def string_request(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, request: Pub.Request<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, R.command(String, V, request))):
  match request:
    case Pub.Add{+k, +v}: PublicAdd.add(V, zero_key, zero_value, c, k, v, events, valid, disabled)
    case Pub.AddWithLifetime{+k, +v, +ns}: PublicAdd.with_lifetime(V, zero_key, zero_value, c, k, v, ns, events, valid, disabled)
    case Pub.Get{+k}: PublicRead.read(V, zero_key, zero_value, c, k, True{}, Pub.ValueOnly{}, events, valid, disabled, {==})
    case Pub.GetAndRefresh{+k, +ns}: PublicRefresh.string_refresh(V, zero_key, zero_value, c, k, ns, events, valid)
    case Pub.Peek{+k}: PublicRead.read(V, zero_key, zero_value, c, k, False{}, Pub.ValueOnly{}, events, valid, disabled, {==})
    case Pub.Contains{+k}: PublicRead.read(V, zero_key, zero_value, c, k, False{}, Pub.Flag{}, events, valid, disabled, {==})
    case Pub.Remove{+k}: PublicSimple.remove(V, zero_key, zero_value, c, k, events, valid, disabled)
    case Pub.RemoveOldest{}: PublicOldest.string_remove_oldest(V, zero_key, zero_value, c, events, valid, disabled)
    case Pub.GetOldest{}: PublicOldest.string_get_oldest(V, zero_key, zero_value, c, events, valid, disabled)
    case Pub.Keys{}: PublicAggregate.string_keys(V, zero_key, zero_value, c, events, valid)
    case Pub.Values{}: PublicAggregate.string_values(V, zero_key, zero_value, c, events, valid)
    case Pub.Purge{}: PublicConfig.purge(~String, ~Codec.string_encode, ~Lookup.string_same, V, zero_key, zero_value, c, events)
    case Pub.PurgeExpired{}: PublicAggregate.string_purge_expired(V, zero_key, zero_value, c, events, valid)
    case Pub.Len{}: PublicConfig.len(~String, ~Codec.string_encode, ~Lookup.string_same, V, zero_key, zero_value, c, events, valid)
    case Pub.SetLifetime{+ns}: PublicConfig.set_lifetime(~String, ~Codec.string_encode, ~Lookup.string_same, V, zero_key, zero_value, c, ns, events)
    case Pub.Metrics{}: PublicConfig.metrics(~String, ~Codec.string_encode, ~Lookup.string_same, V, zero_key, zero_value, c, events)
    case Pub.ResetMetrics{}: PublicConfig.reset_metrics(~String, ~Codec.string_encode, ~Lookup.string_same, V, zero_key, zero_value, c, events)
    case Pub.Diagnostics{}: PublicDiagnostics.string_diagnostics(V, zero_key, zero_value, c, events, valid)
