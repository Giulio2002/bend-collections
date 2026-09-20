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
import ./invariants.bend as Inv
import ./public_relation.bend as R
import ./public_drive.bend as Drive
import ./extensional_states.bend as Ext
import ./configuration_observations.bend as Config
import ./representation_access.bend as Access
import ./cache_storage_preservation.bend as Storage
import ./abstraction_size.bend as Size
import ./abstraction_bindings.bend as B

# Public requests that finish without a clock request. Every statement is about
# the actual start/drive machine for every event list and every key type/codec.

# A finished answer whose abstraction is identical to the specified state.
def unchanged(~K: Data, ~same: K -> K -> Bool, -V: Data, +zero_value: V, +events: List<&2, Clock.Event>, +c: C.Cache<K, V>, +answer: Pub.Answer<K, V>, +expected: PC.Reply<K, V>, +s: S.Model<K, V>, state: {F.abstract(K, V, c) == s : S.Model<K, V>}, reply: {R.reply(K, V, answer) == expected : PC.Reply<K, V>}) -> R.results(~K, ~same, V, D.drive(K, V, zero_value, events, Pub.Finished{c, answer}), PC.Returned{s, expected, events, 0n}):
  %Equal.sym(D.Outcome<K, V>, D.drive(K, V, zero_value, events, Pub.Finished{c, answer}), D.Returned{c, answer, events, 0n}, Drive.finished(K, V, zero_value, events, c, answer)) : R.results(~K, ~same, V, _, PC.Returned{s, expected, events, 0n})
  %state : E.states(~K, ~same, V, F.abstract(K, V, c), _) & {R.reply(K, V, answer) == expected : PC.Reply<K, V>} & {events == events : List<&2, Clock.Event>} & {0n == 0n : Nat}
  (Ext.reflexive(~K, ~same, V, F.abstract(K, V, c)), reply, {==}, {==})

def len(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +events: List<&2, Clock.Event>, valid: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}) -> R.results(~K, ~same, V, D.execute(~K, ~encode, V, zero_key, zero_value, c, events, Pub.Len{}), PC.execute(~K, ~same, V, F.abstract(K, V, c), zero_key, zero_value, events, S.Len{})):
  unchanged(~K, ~same, V, zero_value, events, c, Pub.Length{C.len(K, V, c)}, PC.Length{S.length(K, V, F.abstract(K, V, c))}, F.abstract(K, V, c), {==}, Equal.cong(Nat, PC.Reply<K, V>, n => PC.Length{n}, C.len(K, V, c), S.length(K, V, F.abstract(K, V, c)), Config.length(~K, ~encode, V, c, valid)))

def set_lifetime(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +ns: T.Int64, +events: List<&2, Clock.Event>) -> R.results(~K, ~same, V, D.execute(~K, ~encode, V, zero_key, zero_value, c, events, Pub.SetLifetime{ns}), PC.execute(~K, ~same, V, F.abstract(K, V, c), zero_key, zero_value, events, S.SetLifetime{ns})):
  unchanged(~K, ~same, V, zero_value, events, C.set_lifetime(K, V, c, ns), Pub.Empty{}, PC.Unit{}, S.set_lifetime(K, V, F.abstract(K, V, c), ns), F.set_lifetime_refines(K, V, c, ns), {==})

def metrics(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +events: List<&2, Clock.Event>) -> R.results(~K, ~same, V, D.execute(~K, ~encode, V, zero_key, zero_value, c, events, Pub.Metrics{}), PC.execute(~K, ~same, V, F.abstract(K, V, c), zero_key, zero_value, events, S.Metrics{})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  unchanged(~K, ~same, V, zero_value, events, C.State{cap, table, order, life, counts, cb}, Pub.Counters{counts}, PC.Counters{counts}, F.abstract(K, V, C.State{cap, table, order, life, counts, cb}), {==}, {==})

def reset_metrics(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +events: List<&2, Clock.Event>) -> R.results(~K, ~same, V, D.execute(~K, ~encode, V, zero_key, zero_value, c, events, Pub.ResetMetrics{}), PC.execute(~K, ~same, V, F.abstract(K, V, c), zero_key, zero_value, events, S.ResetMetrics{})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  unchanged(~K, ~same, V, zero_value, events, C.State{cap, table, order, life, T.zero_metrics(), cb}, Pub.Counters{counts}, PC.Counters{counts}, S.Abstract{cap, F.bindings(K, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), F.keys_of(K, V, C.entries(K, V, C.State{cap, table, order, life, counts, cb})), life, T.zero_metrics(), cb}, {==}, {==})

# Full Purge replaces the table with Map.new, clears recency and metrics.
def purge(~K: Data, ~encode: K -> String, ~same: K -> K -> Bool, -V: Data, zero_key: K, +zero_value: V, +c: C.Cache<K, V>, +events: List<&2, Clock.Event>) -> R.results(~K, ~same, V, D.execute(~K, ~encode, V, zero_key, zero_value, c, events, Pub.Purge{}), PC.execute(~K, ~same, V, F.abstract(K, V, c), zero_key, zero_value, events, S.Purge{})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  unchanged(~K, ~same, V, zero_value, events, Pub.purge(K, V, C.State{cap, table, order, life, counts, cb}), Pub.Empty{}, PC.Unit{}, S.purged(K, V, F.abstract(K, V, C.State{cap, table, order, life, counts, cb})), {==}, {==})
