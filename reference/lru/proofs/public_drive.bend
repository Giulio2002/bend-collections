import Base
import ../src/cache.bend as C
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/clock.bend as Clock
import ../types/model.bend as T

# Reduction facts for the actual event-list driver.
def finished(-K: Data, -V: Data, zero_value: V, events: List<&2, Clock.Event>, c: C.Cache<K, V>, answer: Pub.Answer<K, V>) -> {D.drive(K, V, zero_value, events, Pub.Finished{c, answer}) == D.Returned{c, answer, events, 0n} : D.Outcome<K, V>}:
  match events:
    case Nil{}: {==}
    case Con{Clock.Sample{now}, tail}: {==}
    case Con{Clock.InvalidSample{reason}, tail}: {==}
    case Con{Clock.ProviderException{reason}, tail}: {==}
