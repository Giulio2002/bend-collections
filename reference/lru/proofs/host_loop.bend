import Base
import ../src/cache.bend as C
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../src/host.bend as H
import ../spec/clock.bend as Clock

# The adapter's loop: begin once; while the action asks for the clock, obtain
# one provider event and apply H.answer; finally adopt Return/Raise. This
# model of that loop over the sequence of provider events equals D.drive, so
# the adapter's executions are exactly the driver executions of the theorems.
def loop(-K: Data, -V: Data, +zero_value: V, events: List<&2, Clock.Event>, action: H.Action<K, V>) -> D.Outcome<K, V>:
  match events:
    case Nil{}:
      match action:
        case H.Return{c, a}: D.Returned{c, a, Nil{}, 0n}
        case H.Raise{c, e}: D.Failed{c, e, Nil{}, 0n}
        case H.Ask{p}: D.Failed{Pub.abandon(K, V, p), Clock.Exhausted{}, Nil{}, 1n}
    case Con{+ev, +t}:
      match action:
        case H.Return{c, a}: D.Returned{c, a, Con{ev, t}, 0n}
        case H.Raise{c, e}: D.Failed{c, e, Con{ev, t}, 0n}
        case H.Ask{p}: D.bump(K, V, loop(K, V, zero_value, t, H.answer(K, V, zero_value, p, ev)))

def raised(-K: Data, -V: Data, +zero_value: V, t: List<&2, Clock.Event>, c: C.Cache<K, V>, e: Clock.Error) -> {D.bump(K, V, loop(K, V, zero_value, t, H.Raise{c, e})) == D.Failed{c, e, t, 1n} : D.Outcome<K, V>}:
  match t:
    case Nil{}: {==}
    case Con{ev, rest}: {==}

def drives(-K: Data, -V: Data, +zero_value: V, events: List<&2, Clock.Event>, progress: Pub.Progress<K, V>) -> {loop(K, V, zero_value, events, H.act(K, V, progress)) == D.drive(K, V, zero_value, events, progress) : D.Outcome<K, V>}:
  match events:
    case Nil{}:
      match progress:
        case Pub.Finished{c, a}: {==}
        case Pub.Waiting{p}: {==}
    case Con{ev, +t}:
      match ev:
        case Clock.Sample{+now}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{+p}: Equal.cong(D.Outcome<K, V>, D.Outcome<K, V>, o => D.bump(K, V, o), loop(K, V, zero_value, t, H.act(K, V, Pub.resume(K, V, zero_value, p, now))), D.drive(K, V, zero_value, t, Pub.resume(K, V, zero_value, p, now)), drives(K, V, zero_value, t, Pub.resume(K, V, zero_value, p, now)))
        case Clock.InvalidSample{+reason}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{p}: raised(K, V, zero_value, t, Pub.abandon(K, V, p), Clock.Invalid{reason})
        case Clock.ProviderException{+reason}:
          match progress:
            case Pub.Finished{c, a}: {==}
            case Pub.Waiting{p}: raised(K, V, zero_value, t, Pub.abandon(K, V, p), Clock.Thrown{reason})

# One public request through the adapter's steps is D.execute.
def executes(~K: Data, ~encode: K -> String, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, events: List<&2, Clock.Event>, request: Pub.Request<K, V>) -> {loop(K, V, zero_value, events, H.begin(K, V, encode, zero_key, zero_value, c, request)) == D.execute(~K, ~encode, V, zero_key, zero_value, c, events, request) : D.Outcome<K, V>}:
  drives(K, V, zero_value, events, Pub.start(K, V, encode, zero_key, zero_value, c, request))
