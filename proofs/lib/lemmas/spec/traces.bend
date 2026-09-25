import Base
import ../types/model.bend as T
import ./cache.bend as S
import ./clock.bend as Clock
import ./public_commands.bend as P

# A caller may catch a failure and issue the next command. Each result retains
# the partial state and exact unused provider events. No failure becomes success.
type Trace<-K: Data, -V: Data> is Data:
  Finished{state: S.Model<K, V>, remaining: List<&2, Clock.ClockEvent>, observations: List<&2, P.CmdResult<K, V>>, requests: Nat}

def state(-K: Data, -V: Data, result: P.CmdResult<K, V>) -> S.Model<K, V>:
  match result:
    case P.Returned{s, reply, events, count}: s
    case P.Failed{s, error, events, count}: s

def remaining(-K: Data, -V: Data, result: P.CmdResult<K, V>) -> List<&2, Clock.ClockEvent>:
  match result:
    case P.Returned{s, reply, events, count}: events
    case P.Failed{s, error, events, count}: events

def requests(-K: Data, -V: Data, result: P.CmdResult<K, V>) -> Nat:
  match result:
    case P.Returned{s, reply, events, count}: count
    case P.Failed{s, error, events, count}: count

def prepend(-K: Data, -V: Data, +result: P.CmdResult<K, V>, rest: Trace<K, V>) -> Trace<K, V>:
  Finished{s, events, observations, count} = rest
  Finished{s, events, Con{result, observations}, Nat.add(requests(K, V, result), count)}

def run(~K: Data, ~same: K -> K -> Bool, -V: Data, commands: List<&2, S.Command<K, V>>, s: S.Model<K, V>, +zero_key: K, +zero_value: V, events: List<&2, Clock.ClockEvent>) -> Trace<K, V>:
  match commands:
    case Nil{}: Finished{s, events, Nil{}, 0n}
    case Con{command, tail}:
      +result = P.execute(~K, ~same, V, s, zero_key, zero_value, events, command)
      prepend(K, V, result, run(~K, ~same, V, tail, state(K, V, result), zero_key, zero_value, remaining(K, V, result)))
