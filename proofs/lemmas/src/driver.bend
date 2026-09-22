import Base
import ../types/model.bend as T
import ../spec/clock.bend as Clock
import ./cache.bend as C
import ./public.bend as Pub

# Deterministic model of the host clock loop over an explicit provider-event
# list. Only the neutral Clock.Event/Clock.Error datatypes are imported from the
# clock specification; no specification function is used. The adapter runs
# this machine through src/host.bend begin/answer (proofs/host_loop.bend).
type Outcome<-K: Data, -V: Data> is Data:
  Returned{cache: C.Cache<K, V>, answer: Pub.Answer<K, V>, remaining: List<&2, Clock.Event>, requests: Nat}
  Failed{cache: C.Cache<K, V>, error: Clock.Error, remaining: List<&2, Clock.Event>, requests: Nat}

def bump(-K: Data, -V: Data, outcome: Outcome<K, V>) -> Outcome<K, V>:
  match outcome:
    case Returned{c, answer, events, requests}: Returned{c, answer, events, 1n+requests}
    case Failed{c, error, events, requests}: Failed{c, error, events, 1n+requests}

# One step: the provider event answering a Waiting progress either resumes the
# machine or stops it with the retained state and the error. drive is its
# iteration (drive_advance in END_TO_END.bend); src/host.bend answer uses it.
type Step<-K: Data, -V: Data> is Data:
  Continue{progress: Pub.Progress<K, V>}
  Stopped{cache: C.Cache<K, V>, error: Clock.Error}

def advance(-K: Data, -V: Data, zero_value: V, pending: Pub.Pending<K, V>, event: Clock.Event) -> Step<K, V>:
  match event:
    case Clock.Sample{now}: Continue{Pub.resume(K, V, zero_value, pending, now)}
    case Clock.InvalidSample{reason}: Stopped{Pub.abandon(K, V, pending), Clock.Invalid{reason}}
    case Clock.ProviderException{reason}: Stopped{Pub.abandon(K, V, pending), Clock.Thrown{reason}}

def drive(-K: Data, -V: Data, +zero_value: V, events: List<&2, Clock.Event>, progress: Pub.Progress<K, V>) -> Outcome<K, V>:
  match events progress:
    case remaining Pub.Finished{c, answer}: Returned{c, answer, remaining, 0n}
    case Nil{} Pub.Waiting{pending}: Failed{Pub.abandon(K, V, pending), Clock.Exhausted{}, Nil{}, 1n}
    case Con{Clock.InvalidSample{reason}, tail} Pub.Waiting{pending}: Failed{Pub.abandon(K, V, pending), Clock.Invalid{reason}, tail, 1n}
    case Con{Clock.ProviderException{reason}, tail} Pub.Waiting{pending}: Failed{Pub.abandon(K, V, pending), Clock.Thrown{reason}, tail, 1n}
    case Con{Clock.Sample{now}, tail} Pub.Waiting{pending}: bump(K, V, drive(K, V, zero_value, tail, Pub.resume(K, V, zero_value, pending, now)))

def execute(~K: Data, ~encode: K -> String, -V: Data, zero_key: K, +zero_value: V, c: C.Cache<K, V>, events: List<&2, Clock.Event>, request: Pub.Request<K, V>) -> Outcome<K, V>:
  drive(K, V, zero_value, events, Pub.start(K, V, encode, zero_key, zero_value, c, request))

def cache(-K: Data, -V: Data, outcome: Outcome<K, V>) -> C.Cache<K, V>:
  match outcome:
    case Returned{c, answer, events, requests}: c
    case Failed{c, error, events, requests}: c

def remaining(-K: Data, -V: Data, outcome: Outcome<K, V>) -> List<&2, Clock.Event>:
  match outcome:
    case Returned{c, answer, events, requests}: events
    case Failed{c, error, events, requests}: events

def requests(-K: Data, -V: Data, outcome: Outcome<K, V>) -> Nat:
  match outcome:
    case Returned{c, answer, events, count}: count
    case Failed{c, error, events, count}: count

# A caller may catch a failed command and continue from the retained state.
type Trace<-K: Data, -V: Data> is Data:
  Ran{cache: C.Cache<K, V>, remaining: List<&2, Clock.Event>, outcomes: List<&2, Outcome<K, V>>, requests: Nat}

def prepend(-K: Data, -V: Data, +outcome: Outcome<K, V>, rest: Trace<K, V>) -> Trace<K, V>:
  Ran{c, events, outcomes, count} = rest
  Ran{c, events, Con{outcome, outcomes}, Nat.add(requests(K, V, outcome), count)}

def run(~K: Data, ~encode: K -> String, -V: Data, requests: List<&2, Pub.Request<K, V>>, c: C.Cache<K, V>, +zero_key: K, +zero_value: V, events: List<&2, Clock.Event>) -> Trace<K, V>:
  match requests:
    case Nil{}: Ran{c, events, Nil{}, 0n}
    case Con{request, tail}:
      +outcome = execute(~K, ~encode, V, zero_key, zero_value, c, events, request)
      prepend(K, V, outcome, run(~K, ~encode, V, tail, cache(K, V, outcome), zero_key, zero_value, remaining(K, V, outcome)))
