import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../src/entry_ops.bend as Entry
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as Eff
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_drive.bend as Drive
import ./public_config.bend as PublicConfig
import ./extensional_states.bend as Ext
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./cache_key_identity.bend as Key
import ./representation_access.bend as Access
import ./live_read_state.bend as Live
import ./refresh_state.bend as RefreshState
import ./duration_refinement.bend as Duration
import ./numeric.bend as Numeric

# Public GetAndRefresh through the actual machine: the hit and recency move are
# committed before the clock request and survive its failure; a sample then
# replaces the deadline (even of an expired entry) without a second hit.

def finished_related(~K: Data, ~same: K -> K -> Bool, -V: Data, +zero_value: V, +events: List<&2, Clock.ClockEvent>, +c: C.Cache<K, V>, +answer: Pub.Answer<K, V>, +expected: PC.Reply<K, V>, +s: S.Model<K, V>, state: E.states(~K, ~same, V, F.abstract(K, V, c), s), reply: {R.reply(K, V, answer) == expected : PC.Reply<K, V>}) -> R.results(~K, ~same, V, D.drive(K, V, zero_value, events, Pub.Finished{c, answer}), PC.Returned{s, expected, events, 0n}):
  %Equal.sym(D.Outcome<K, V>, D.drive(K, V, zero_value, events, Pub.Finished{c, answer}), D.Returned{c, answer, events, 0n}, Drive.finished(K, V, zero_value, events, c, answer)) : R.results(~K, ~same, V, _, PC.Returned{s, expected, events, 0n})
  (state, reply, {==}, {==})

def bumped_related(~K: Data, ~same: K -> K -> Bool, -V: Data, +zero_value: V, +events: List<&2, Clock.ClockEvent>, +c: C.Cache<K, V>, +answer: Pub.Answer<K, V>, +expected: PC.Reply<K, V>, +s: S.Model<K, V>, state: E.states(~K, ~same, V, F.abstract(K, V, c), s), reply: {R.reply(K, V, answer) == expected : PC.Reply<K, V>}) -> R.results(~K, ~same, V, D.bump(K, V, D.drive(K, V, zero_value, events, Pub.Finished{c, answer})), PC.Returned{s, expected, events, 1n}):
  %Equal.sym(D.Outcome<K, V>, D.bump(K, V, D.drive(K, V, zero_value, events, Pub.Finished{c, answer})), D.Returned{c, answer, events, 1n}, Equal.cong(D.Outcome<K, V>, D.Outcome<K, V>, outcome => D.bump(K, V, outcome), D.drive(K, V, zero_value, events, Pub.Finished{c, answer}), D.Returned{c, answer, events, 0n}, Drive.finished(K, V, zero_value, events, c, answer))) : R.results(~K, ~same, V, _, PC.Returned{s, expected, events, 1n})
  (state, reply, {==}, {==})

def lifetime(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +code: String, +k: String, +v: V, +d: T.Int64, +ns: T.Int64, +p: S.Model<String, V>, immortal: Bool, +events: List<&2, Clock.ClockEvent>, success: @+now: T.Int64 -> @+life: T.Int64 -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, Entry.refresh_at(String, V, c, code, T.Item{k, v, d}, life, now)), O.observed_state(String, V, Eff.refresh_deadline(~String, ~Lookup.string_same, V, p, T.Item{k, v, d}, Time.deadline(now, life)))), failure: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), p)) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_lifetime(String, V, c, code, T.Item{k, v, d}, ns, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_lifetime(~String, ~Lookup.string_same, V, p, T.Item{k, v, d}, ns, events, immortal))):
  S.Abstract{+pcap, +pbindings, +porder, +plife, +pcounts, +pcb} = p
  match immortal:
    case True{}: finished_related(~String, ~Lookup.string_same, V, zero_value, events, Entry.refresh_at(String, V, c, code, T.Item{k, v, d}, Pub.zero_time(), Pub.zero_time()), Pub.Value{v, True{}}, PC.Value{v, True{}}, O.observed_state(String, V, Eff.refresh_deadline(~String, ~Lookup.string_same, V, S.Abstract{pcap, pbindings, porder, plife, pcounts, pcb}, T.Item{k, v, d}, T.I64{Word.zero(64n)})), success(Pub.zero_time(), Pub.zero_time()), {==})
    case False{}:
      match events:
        case Nil{}: (failure, {==}, {==}, {==})
        case Con{Clock.InvalidSample{+reason}, +tail}: (failure, {==}, {==}, {==})
        case Con{Clock.ProviderException{+reason}, +tail}: (failure, {==}, {==}, {==})
        case Con{Clock.Sample{+now}, +tail}:
          %Duration.deadline(now, ns) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.Finished{Entry.refresh_at(String, V, c, code, T.Item{k, v, d}, ns, now), Pub.Value{v, True{}}})), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_deadline(~String, ~Lookup.string_same, V, S.Abstract{pcap, pbindings, porder, plife, pcounts, pcb}, T.Item{k, v, d}, _), tail, 1n))
          bumped_related(~String, ~Lookup.string_same, V, zero_value, tail, Entry.refresh_at(String, V, c, code, T.Item{k, v, d}, ns, now), Pub.Value{v, True{}}, PC.Value{v, True{}}, O.observed_state(String, V, Eff.refresh_deadline(~String, ~Lookup.string_same, V, S.Abstract{pcap, pbindings, porder, plife, pcounts, pcb}, T.Item{k, v, d}, Time.deadline(now, ns))), success(now, ns), {==})

def present(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +v: V, +d: T.Int64, +bits: Word(64n), +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +found: {C.lookup(String, V, c, key) == Some{T.Item{key, v, d}} : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_prepared(String, V, zero_value, key, T.I64{bits}, C.read_live(String, V, c, key, T.Item{key, v, d}, True{}))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_hit(~String, ~Lookup.string_same, V, F.abstract(String, V, c), T.I64{bits}, events, T.Item{key, v, d}))):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  %Numeric.zero_comparison_correspondence(64n, bits) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_lifetime(String, V, C.step_cache(String, V, C.read_live(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{key, v, d}, True{})), key, T.Item{key, v, d}, T.I64{bits}, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_lifetime(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, True{}), T.Item{key, v, d}, T.I64{bits}, events, N.zero(bits))))
  lifetime(V, zero_key, zero_value, C.step_cache(String, V, C.read_live(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{key, v, d}, True{})), key, key, v, d, T.I64{bits}, O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, True{}), N.zero(bits), events, now => lifetime_ns => RefreshState.correspondence(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, v, d, lifetime_ns, now, valid, found), %Equal.sym(S.Model<String, V>, F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{key, v, d}, True{}))), O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, True{}), Live.state(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{key, v, d}, True{}, valid, found)) : E.states(~String, ~Lookup.string_same, V, _, O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, True{})) Ext.reflexive(~String, ~Lookup.string_same, V, O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, True{})))

def found(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +bits: Word(64n), +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, result: Maybe<&2, T.Entry<String, V>>, +decision: {C.lookup(String, V, c, key) == result : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_prepared(String, V, zero_value, key, T.I64{bits}, Entry.refresh_prepare_found(String, V, c, key, result))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), T.I64{bits}, events, result))):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  match result:
    case None{}: PublicConfig.unchanged(~String, ~Lookup.string_same, V, zero_value, events, Entry.finish_miss(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, True{}), Pub.Value{zero_value, False{}}, PC.Value{zero_value, False{}}, F.abstract(String, V, Entry.finish_miss(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, True{})), {==}, {==})
    case Some{T.Item{+k, +v, +d}}:
      +same = Key.string_lookup_key(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, k, v, d, Access.get_identities(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, valid), decision)
      %same : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_prepared(String, V, zero_value, key, T.I64{bits}, C.read_live(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{_, v, d}, True{}))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_hit(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), T.I64{bits}, events, T.Item{_, v, d})))
      present(V, zero_key, zero_value, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, v, d, bits, events, valid, Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key), Some{T.Item{k, v, d}}, Some{T.Item{key, v, d}}, decision, Equal.cong(String, Maybe<&2, T.Entry<String, V>>, x => Some{T.Item{x, v, d}}, k, key, Equal.sym(String, key, k, same))))

# Whole public GetAndRefresh for every provider-event list.
def string_refresh(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, ns: T.Int64, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.GetAndRefresh{key, ns}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.GetAndRefresh{key, ns})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  T.I64{+bits} = ns
  %L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.refresh_prepared(String, V, zero_value, key, T.I64{bits}, Entry.refresh_prepare_found(String, V, C.State{cap, table, order, life, counts, cb}, key, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key)))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.ValueOnly{}, Eff.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), T.I64{bits}, events, _)))
  found(V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, key, bits, events, valid, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), {==})
