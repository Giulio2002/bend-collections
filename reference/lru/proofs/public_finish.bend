import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/protocol.bend as P
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/operations.bend as O
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./ordered_entries.bend as Ordered
import ./public_relation.bend as R
import ./public_drive.bend as Drive
import ./map_routing.bend as Routing

def projection(-K: Data, shape: Pub.Shape<K>) -> PC.Projection<K>:
  match shape:
    case Pub.Flag{}: PC.Flag{}
    case Pub.ValueOnly{}: PC.ValueOnly{}
    case Pub.Captured{k}: PC.CapturedOldest{k}
    case Pub.Nothing{}: PC.Nothing{}
    case Pub.AllKeys{}: PC.Keys{}
    case Pub.AllValues{}: PC.Values{}

def value_projection(-K: Data, -V: Data, zero: V, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> {Pub.item_value(K, V, zero, item, present) == PC.value(K, V, zero, item, present) : V}:
  match item present:
    case Some{T.Item{k, v, d}} True{}: {==}
    case Some{T.Item{k, v, d}} False{}: {==}
    case None{} True{}: {==}
    case None{} False{}: {==}

def key_projection(-K: Data, -V: Data, zero: K, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> {Pub.item_key(K, V, zero, item, present) == PC.key(K, V, zero, item, present) : K}:
  match item present:
    case Some{T.Item{k, v, d}} True{}: {==}
    case Some{T.Item{k, v, d}} False{}: {==}
    case None{} True{}: {==}
    case None{} False{}: {==}

# Shapes whose reply is a projection of the returned item/flag. Enumerating
# shapes are handled with the aggregate proof, because a function-valued
# extensional premise is affine and cannot be queried once per listed key.
def returned(-V: Data, zero_value: V, step: C.Step<String, V>, shape: Pub.Shape<String>, events: List<&2, Clock.Event>, count: Nat) -> D.Outcome<String, V>:
  C.Out{+c, item, flag, evs} = step
  D.Returned{c, Pub.shaped(String, V, zero_value, c, item, flag, shape), events, count}

def simple(-K: Data, shape: Pub.Shape<K>) -> Bool:
  match shape:
    case Pub.AllKeys{}: False{}
    case Pub.AllValues{}: False{}
    case other: True{}

def simple_reply(~K: Data, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, c: C.Cache<K, V>, s: S.Model<K, V>, +item: Maybe<&2, T.Entry<K, V>>, +flag: Bool, shape: Pub.Shape<K>, plain: {simple(K, shape) == True{} : Bool}) -> {R.reply(K, V, Pub.shaped(K, V, zero_value, c, item, flag, shape)) == PC.project(~K, ~same, V, s, zero_key, zero_value, item, flag, projection(K, shape)) : PC.Reply<K, V>}:
  match shape:
    case Pub.Flag{}: {==}
    case Pub.ValueOnly{}: Equal.cong(V, PC.Reply<K, V>, v => PC.Value{v, flag}, Pub.item_value(K, V, zero_value, item, flag), PC.value(K, V, zero_value, item, flag), value_projection(K, V, zero_value, item, flag))
    case Pub.Captured{+k}: Equal.cong(V, PC.Reply<K, V>, v => PC.Oldest{k, v, flag}, Pub.item_value(K, V, zero_value, item, flag), PC.value(K, V, zero_value, item, flag), value_projection(K, V, zero_value, item, flag))
    case Pub.Nothing{}: {==}
    case Pub.AllKeys{}: Empty.absurd({R.reply(K, V, Pub.shaped(K, V, zero_value, c, item, flag, Pub.AllKeys{})) == PC.project(~K, ~same, V, s, zero_key, zero_value, item, flag, projection(K, Pub.AllKeys{})) : PC.Reply<K, V>}, Routing.false_true(plain))
    case Pub.AllValues{}: Empty.absurd({R.reply(K, V, Pub.shaped(K, V, zero_value, c, item, flag, Pub.AllValues{})) == PC.project(~K, ~same, V, s, zero_key, zero_value, item, flag, projection(K, Pub.AllValues{})) : PC.Reply<K, V>}, Routing.false_true(plain))

# A finished native step whose observation refines an independent observation
# yields a refining public result, for any event remainder and request count.
def finished(-V: Data, zero_key: String, +zero_value: V, step: C.Step<String, V>, shape: Pub.Shape<String>, expected: S.Observation<String, V>, +events: List<&2, Clock.Event>, +count: Nat, plain: {simple(String, shape) == True{} : Bool}, proof: E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, step), expected)) -> R.results(~String, ~Lookup.string_same, V, returned(V, zero_value, step, shape, events, count), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, projection(String, shape), expected, events, count)):
  C.Out{+c, +item, +flag, evs} = step
  S.Observed{+s, expected_item, expected_flag, expected_events} = expected
  (related, same_item, same_flag, same_events) = proof
  %same_item : R.results(~String, ~Lookup.string_same, V, D.Returned{c, Pub.shaped(String, V, zero_value, c, item, flag, shape), events, count}, PC.Returned{s, PC.project(~String, ~Lookup.string_same, V, s, zero_key, zero_value, _, expected_flag, projection(String, shape)), events, count})
  %same_flag : R.results(~String, ~Lookup.string_same, V, D.Returned{c, Pub.shaped(String, V, zero_value, c, item, flag, shape), events, count}, PC.Returned{s, PC.project(~String, ~Lookup.string_same, V, s, zero_key, zero_value, item, _, projection(String, shape)), events, count})
  (related, simple_reply(~String, ~Lookup.string_same, V, zero_key, zero_value, c, s, item, flag, shape, plain), {==}, {==})

def drive_step(-V: Data, +zero_value: V, step: C.Step<String, V>, shape: Pub.Shape<String>, events: List<&2, Clock.Event>) -> {D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, step, shape)) == returned(V, zero_value, step, shape, events, 0n) : D.Outcome<String, V>}:
  C.Out{+c, item, flag, evs} = step
  Drive.finished(String, V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, item, flag, shape))

def bump_step(-V: Data, +zero_value: V, step: C.Step<String, V>, shape: Pub.Shape<String>, events: List<&2, Clock.Event>) -> {D.bump(String, V, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, step, shape))) == returned(V, zero_value, step, shape, events, 1n) : D.Outcome<String, V>}:
  C.Out{+c, item, flag, evs} = step
  Equal.cong(D.Outcome<String, V>, D.Outcome<String, V>, outcome => D.bump(String, V, outcome), D.drive(String, V, zero_value, events, Pub.Finished{c, Pub.shaped(String, V, zero_value, c, item, flag, shape)}), D.Returned{c, Pub.shaped(String, V, zero_value, c, item, flag, shape), events, 0n}, Drive.finished(String, V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, item, flag, shape)))
