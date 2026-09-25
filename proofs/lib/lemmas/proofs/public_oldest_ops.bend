import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/operations.bend as O
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_drive.bend as Drive
import ./public_finish.bend as Finish
import ./public_read.bend as PublicRead
import ./extensional_states.bend as Ext
import ./oldest_refinement.bend as Oldest
import ./string_order.bend as Order
import ./abstraction_recency.bend as Recency
import ./abstraction_bindings.bend as B
import ./lookup_refinement.bend as L
import ./cache_key_identity.bend as Key
import ./representation_access.bend as Access
import ./public_config.bend as PublicConfig
import ../spec/effectful_operations.bend as Eff

# RemoveOldest: the removed entry's original key/value/flag are projected
# exactly as the independent RemovedOldest reply.
def oldest_removed_reply(~K: Data, ~same: K -> K -> Bool, -V: Data, +zero_key: K, +zero_value: V, step: C.Step<K, V>, expected: S.Observation<K, V>, +events: List<&2, Clock.ClockEvent>, proof: E.observations(~K, ~same, V, F.observe(K, V, step), expected)) -> R.results(~K, ~same, V, D.drive(K, V, zero_value, events, Pub.removed_oldest(K, V, zero_key, zero_value, step)), PC.observation(~K, ~same, V, zero_key, zero_value, PC.RemovedOldest{}, expected, events, 0n)):
  C.Out{+c, +item, +flag, evs} = step
  S.Observed{+s, expected_item, expected_flag, expected_events} = expected
  (related, same_item, same_flag, same_events) = proof
  %same_item : R.results(~K, ~same, V, D.drive(K, V, zero_value, events, Pub.removed_oldest(K, V, zero_key, zero_value, C.Out{c, item, flag, evs})), PC.Returned{s, PC.Oldest{PC.key(K, V, zero_key, _, expected_flag), PC.value(K, V, zero_value, _, expected_flag), expected_flag}, events, 0n})
  %same_flag : R.results(~K, ~same, V, D.drive(K, V, zero_value, events, Pub.removed_oldest(K, V, zero_key, zero_value, C.Out{c, item, flag, evs})), PC.Returned{s, PC.Oldest{PC.key(K, V, zero_key, item, _), PC.value(K, V, zero_value, item, _), _}, events, 0n})
  %Equal.sym(D.Outcome<K, V>, D.drive(K, V, zero_value, events, Pub.Finished{c, Pub.Oldest{Pub.item_key(K, V, zero_key, item, flag), Pub.item_value(K, V, zero_value, item, flag), flag}}), D.Returned{c, Pub.Oldest{Pub.item_key(K, V, zero_key, item, flag), Pub.item_value(K, V, zero_value, item, flag), flag}, events, 0n}, Drive.finished(K, V, zero_value, events, c, Pub.Oldest{Pub.item_key(K, V, zero_key, item, flag), Pub.item_value(K, V, zero_value, item, flag), flag})) : R.results(~K, ~same, V, _, PC.Returned{s, PC.Oldest{PC.key(K, V, zero_key, item, flag), PC.value(K, V, zero_value, item, flag), flag}, events, 0n})
  %Equal.sym(K, Pub.item_key(K, V, zero_key, item, flag), PC.key(K, V, zero_key, item, flag), Finish.key_projection(K, V, zero_key, item, flag)) : E.states(~K, ~same, V, F.abstract(K, V, c), s) & {PC.Oldest{_, Pub.item_value(K, V, zero_value, item, flag), flag} == PC.Oldest{PC.key(K, V, zero_key, item, flag), PC.value(K, V, zero_value, item, flag), flag} : PC.Reply<K, V>} & {events == events : List<&2, Clock.ClockEvent>} & {0n == 0n : Nat}
  %Equal.sym(V, Pub.item_value(K, V, zero_value, item, flag), PC.value(K, V, zero_value, item, flag), Finish.value_projection(K, V, zero_value, item, flag)) : E.states(~K, ~same, V, F.abstract(K, V, c), s) & {PC.Oldest{PC.key(K, V, zero_key, item, flag), _, flag} == PC.Oldest{PC.key(K, V, zero_key, item, flag), PC.value(K, V, zero_value, item, flag), flag} : PC.Reply<K, V>} & {events == events : List<&2, Clock.ClockEvent>} & {0n == 0n : Nat}
  (related, {==}, {==}, {==})

def string_remove_oldest(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.RemoveOldest{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.RemoveOldest{})):
  oldest_removed_reply(~String, ~Lookup.string_same, V, zero_key, zero_value, C.remove_oldest(String, V, c, False{}), O.remove_oldest(~String, ~Lookup.string_same, V, F.abstract(String, V, c)), events, Oldest.remove_oldest(V, c, valid, disabled))

# GetOldest after the oldest binding is known: the stored original key is
# captured, then the untracked public read decides liveness (clock effects,
# failures and expired removal included) through PublicRead.read.
def oldest_found_branch(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +code: String, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, result: Maybe<&2, T.Entry<String, V>>, +decision: {C.lookup(String, V, c, code) == result : Maybe<&2, T.Entry<String, V>>}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.oldest_found(String, V, zero_key, zero_value, c, code, result)), PC.oldest_binding(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, result)):
  match result:
    case None{}: PublicConfig.unchanged(~String, ~Lookup.string_same, V, zero_value, events, c, Pub.Oldest{zero_key, zero_value, False{}}, PC.Oldest{zero_key, zero_value, False{}}, F.abstract(String, V, c), {==}, {==})
    case Some{T.Item{+k, +v, +d}}:
      %Key.string_lookup_key(V, c, code, k, v, d, Access.get_identities(~String, ~Codec.string_encode, V, c, valid), decision) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.read(String, V, zero_value, c, code, False{}, Pub.Captured{k})), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.CapturedOldest{k}, Eff.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), _, False{}, events)))
      PublicRead.read(V, zero_key, zero_value, c, code, False{}, Pub.Captured{k}, events, valid, disabled, {==})

def oldest_order_branch(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, order: List<&2, String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.oldest_order(String, V, zero_key, zero_value, c, order)), PC.oldest_order(~String, ~Lookup.string_same, V, F.abstract(String, V, c), B.model_bindings(String, V, F.abstract(String, V, c)), order, zero_key, zero_value, events)):
  match order:
    case Nil{}: PublicConfig.unchanged(~String, ~Lookup.string_same, V, zero_value, events, c, Pub.Oldest{zero_key, zero_value, False{}}, PC.Oldest{zero_key, zero_value, False{}}, F.abstract(String, V, c), {==}, {==})
    case Con{+code, rest}:
      %L.string_lookup(V, c, code, valid) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.oldest_found(String, V, zero_key, zero_value, c, code, C.lookup(String, V, c, code))), PC.oldest_binding(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, _))
      oldest_found_branch(V, zero_key, zero_value, c, code, events, valid, disabled, C.lookup(String, V, c, code), {==})

def string_get_oldest(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.GetOldest{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.GetOldest{})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(List<&2, String>, Recency.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, Order.faithful(V, C.State{cap, table, order, life, counts, cb}, valid)) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.oldest_order(String, V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, order)), PC.oldest_order(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), _, zero_key, zero_value, events))
  oldest_order_branch(V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, order, events, valid, disabled)
