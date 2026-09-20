import Base
import ../src/cache.bend as C
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/clock.bend as Clock

# Unfolding lemmas for the Bend driver: D.drive returns on a Finished progress
# and, on a Waiting progress, consumes one event through D.advance. They say
# nothing about src/adapter.ts; its loop is proved in host_loop.bend.
def continue(-K: Data, -V: Data, +zero_value: V, step: D.Step<K, V>, tail: List<&2, Clock.Event>) -> D.Outcome<K, V>:
  match step:
    case D.Continue{progress}: D.bump(K, V, D.drive(K, V, zero_value, tail, progress))
    case D.Stopped{c, error}: D.Failed{c, error, tail, 1n}

def finished(-K: Data, -V: Data, +zero_value: V, events: List<&2, Clock.Event>, c: C.Cache<K, V>, answer: Pub.Answer<K, V>) -> {D.drive(K, V, zero_value, events, Pub.Finished{c, answer}) == D.Returned{c, answer, events, 0n} : D.Outcome<K, V>}:
  match events:
    case Nil{}: {==}
    case Con{e, tail}:
      match e:
        case Clock.Sample{now}: {==}
        case Clock.InvalidSample{reason}: {==}
        case Clock.ProviderException{reason}: {==}

def waiting(-K: Data, -V: Data, +zero_value: V, event: Clock.Event, tail: List<&2, Clock.Event>, pending: Pub.Pending<K, V>) -> {D.drive(K, V, zero_value, Con{event, tail}, Pub.Waiting{pending}) == continue(K, V, zero_value, D.advance(K, V, zero_value, pending, event), tail) : D.Outcome<K, V>}:
  match event:
    case Clock.Sample{now}: {==}
    case Clock.InvalidSample{reason}: {==}
    case Clock.ProviderException{reason}: {==}
