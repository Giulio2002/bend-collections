import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as Eff
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./read_refinement.bend as Read
import ./public_relation.bend as R
import ./public_finish.bend as Finish
import ./extensional_states.bend as Ext
import ./numeric.bend as Numeric
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ../src/time.bend as Time
import ../src/wide.bend as W
import ../spec/numeric.bend as N

# One accepted sample: the actual resumed read against the independent read.
def sampled(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +tracked: Bool, +shape: Pub.Shape<String>, +now: T.Int64, +tail: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, plain: {Finish.simple(String, shape) == True{} : Bool}, +present: {C.lookup(String, V, c, key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.finish_read(String, V, zero_value, c, key, now, tracked, shape))), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, Some{entry}), tail, 1n)):
  %Equal.sym(D.Outcome<String, V>, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.finish_step(String, V, zero_value, C.read_encoded(String, V, c, key, now, tracked), shape))), Finish.returned(V, zero_value, C.read_encoded(String, V, c, key, now, tracked), shape, tail, 1n), Finish.bump_step(V, zero_value, C.read_encoded(String, V, c, key, now, tracked), shape, tail)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, Some{entry}), tail, 1n))
  Finish.finished(V, zero_key, zero_value, C.read_encoded(String, V, c, key, now, tracked), shape, O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, Some{entry}), tail, 1n, plain, %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), Some{entry}, present) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, c, key, now, tracked, _)), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, Some{entry})) Read.found(V, c, key, now, tracked, Some{entry}, valid, disabled, present))

# The awaited request: every provider outcome, including failures, where the
# retained state is the unchanged cache and exactly one request is counted.
def waiting(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +tracked: Bool, +shape: Pub.Shape<String>, events: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, plain: {Finish.simple(String, shape) == True{} : Bool}, +present: {C.lookup(String, V, c, key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.Waiting{Pub.ReadWait{c, key, tracked, shape}}), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.sampled_read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, Clock.request(events)))):
  match events:
    case Nil{}: (Ext.string_reflexive(V, F.abstract(String, V, c)), {==}, {==}, {==})
    case Con{Clock.InvalidSample{reason}, tail}: (Ext.string_reflexive(V, F.abstract(String, V, c)), {==}, {==}, {==})
    case Con{Clock.ProviderException{reason}, tail}: (Ext.string_reflexive(V, F.abstract(String, V, c)), {==}, {==}, {==})
    case Con{Clock.Sample{+now}, +tail}: sampled(V, zero_key, zero_value, c, key, entry, tracked, shape, now, tail, valid, disabled, plain, present)

# A zero deadline is immortal: no request is made and the entry is live.
def lifetime(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +original: String, +value: V, +bits: Word(64n), +tracked: Bool, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, plain: {Finish.simple(String, shape) == True{} : Bool}, +present: {C.lookup(String, V, c, key) == Some{T.Item{original, value, T.I64{bits}}} : Maybe<&2, T.Entry<String, V>>}, immortal: Bool, zero_eq: {W.is_zero(64n, bits) == immortal : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read_lifetime(String, V, zero_value, c, key, tracked, shape, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.read_lifetime(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, events, immortal))):
  match immortal:
    case False{}: waiting(V, zero_key, zero_value, c, key, T.Item{original, value, T.I64{bits}}, tracked, shape, events, valid, disabled, plain, present)
    case True{}:
      %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape)), Finish.returned(V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, events, 0n), Finish.drive_step(V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, events)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, False{}), events, 0n))
      Finish.finished(V, zero_key, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, False{}), events, 0n, plain, %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), Some{T.Item{original, value, T.I64{bits}}}, present) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, c, key, Pub.zero_time(), tracked, _)), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, False{})) %Equal.sym(Bool, W.is_zero(64n, bits), True{}, zero_eq) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_expiry(String, V, c, key, T.Item{original, value, T.I64{bits}}, tracked, Time.expired_choose(T.I64{bits}, Pub.zero_time(), _))), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, False{})) Read.expiry(V, c, key, T.Item{original, value, T.I64{bits}}, tracked, False{}, valid, disabled, present))

def found(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +tracked: Bool, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, plain: {Finish.simple(String, shape) == True{} : Bool}, result: Maybe<&2, T.Entry<String, V>>, +decision: {C.lookup(String, V, c, key) == result : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read_found(String, V, zero_value, c, key, tracked, shape, result)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked, events, result))):
  match result:
    case None{}:
      %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape)), Finish.returned(V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, events, 0n), Finish.drive_step(V, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, events)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, Pub.zero_time(), tracked, None{}), events, 0n))
      Finish.finished(V, zero_key, zero_value, C.read_encoded(String, V, c, key, Pub.zero_time(), tracked), shape, O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, Pub.zero_time(), tracked, None{}), events, 0n, plain, %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), None{}, decision) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, c, key, Pub.zero_time(), tracked, _)), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, Pub.zero_time(), tracked, None{})) Read.found(V, c, key, Pub.zero_time(), tracked, None{}, valid, disabled, decision))
    case Some{T.Item{+original, +value, T.I64{+bits}}}:
      %Numeric.zero_comparison_correspondence(64n, bits) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read_lifetime(String, V, zero_value, c, key, tracked, shape, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.read_lifetime(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, T.I64{bits}}, tracked, events, N.zero(bits))))
      lifetime(V, zero_key, zero_value, c, key, original, value, bits, tracked, shape, events, valid, disabled, plain, decision, N.zero(bits), Equal.sym(Bool, N.zero(bits), W.is_zero(64n, bits), Numeric.zero_comparison_correspondence(64n, bits)))

# Whole Get/Peek/Contains (and the captured GetOldest read) of the actual
# driver over every provider-event list.
def read(-V: Data, zero_key: String, +zero_value: V, c: C.Cache<String, V>, +key: String, +tracked: Bool, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +plain: {Finish.simple(String, shape) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read(String, V, zero_value, c, key, tracked, shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked, events))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid)) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read_found(String, V, zero_value, C.State{cap, table, order, life, counts, cb}, key, tracked, shape, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), Eff.read(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, tracked, events)))
  found(V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, key, tracked, shape, events, valid, disabled, plain, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid))
