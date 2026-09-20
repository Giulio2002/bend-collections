import Base
import ../src/cache.bend as C
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F

# Translation of the executable request/answer vocabulary into the independent
# specification vocabulary. These are constructor renamings; they inspect no
# cache state and cannot repair a wrong answer.
def command(-K: Data, -V: Data, request: Pub.Request<K, V>) -> S.Command<K, V>:
  match request:
    case Pub.Add{k, v}: S.Add{k, v}
    case Pub.AddWithLifetime{k, v, ns}: S.AddWithLifetime{k, v, ns}
    case Pub.Get{k}: S.Get{k}
    case Pub.GetAndRefresh{k, ns}: S.GetAndRefresh{k, ns}
    case Pub.Peek{k}: S.Peek{k}
    case Pub.Contains{k}: S.Contains{k}
    case Pub.Remove{k}: S.Remove{k}
    case Pub.RemoveOldest{}: S.RemoveOldest{}
    case Pub.GetOldest{}: S.GetOldest{}
    case Pub.Keys{}: S.Keys{}
    case Pub.Values{}: S.Values{}
    case Pub.Purge{}: S.Purge{}
    case Pub.PurgeExpired{}: S.PurgeExpired{}
    case Pub.Len{}: S.Len{}
    case Pub.SetLifetime{ns}: S.SetLifetime{ns}
    case Pub.Metrics{}: S.Metrics{}
    case Pub.ResetMetrics{}: S.ResetMetrics{}
    case Pub.Diagnostics{}: S.Diagnostics{}

def reply(-K: Data, -V: Data, answer: Pub.Answer<K, V>) -> PC.Reply<K, V>:
  match answer:
    case Pub.Empty{}: PC.Unit{}
    case Pub.Boolean{b}: PC.Boolean{b}
    case Pub.Value{v, found}: PC.Value{v, found}
    case Pub.Oldest{k, v, found}: PC.Oldest{k, v, found}
    case Pub.KeyList{keys}: PC.KeyList{keys}
    case Pub.ValueList{values}: PC.ValueList{values}
    case Pub.Length{n}: PC.Length{n}
    case Pub.Counters{m}: PC.Counters{m}
    case Pub.Storage{leaves, recency, cap, m}: PC.Storage{leaves, recency, cap, m}

# Executed outcome versus independent result: same success/failure class, exact
# reply or error, exact unused provider events and request count, and
# extensionally equal finite-map state with exact recency and metrics.
def results(~K: Data, ~same: K -> K -> Bool, -V: Data, actual: D.Outcome<K, V>, expected: PC.Result<K, V>) -> Type:
  match actual expected:
    case D.Returned{c, answer, events, count} PC.Returned{s, expected_reply, expected_events, expected_count}:
      E.states(~K, ~same, V, F.abstract(K, V, c), s) & {reply(K, V, answer) == expected_reply : PC.Reply<K, V>} & {events == expected_events : List<&2, Clock.Event>} & {count == expected_count : Nat}
    case D.Failed{c, error, events, count} PC.Failed{s, expected_error, expected_events, expected_count}:
      E.states(~K, ~same, V, F.abstract(K, V, c), s) & {error == expected_error : Clock.Error} & {events == expected_events : List<&2, Clock.Event>} & {count == expected_count : Nat}
    case D.Returned{c, answer, events, count} PC.Failed{s, expected_error, expected_events, expected_count}: Empty
    case D.Failed{c, error, events, count} PC.Returned{s, expected_reply, expected_events, expected_count}: Empty
