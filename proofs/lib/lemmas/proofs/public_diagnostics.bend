import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/operations.bend as O
import ../spec/public_commands.bend as PC
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_config.bend as PublicConfig
import ./public_aggregate.bend as Aggregate
import ./ordered_entries.bend as Ordered
import ./configuration_observations.bend as Config
import ./size_length.bend as Size

# Diagnostics report the actual native Map leaf count and recency length; for
# represented caches both equal the number of bound abstract entries.
def string_diagnostics(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.Diagnostics{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.Diagnostics{})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  +leaves = Equal.trans(Nat, C.map_size(String, V, C.State{cap, table, order, life, counts, cb}), C.len(String, V, C.State{cap, table, order, life, counts, cb}), List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), Size.native_size(V, C.State{cap, table, order, life, counts, cb}, valid), Equal.trans(Nat, C.len(String, V, C.State{cap, table, order, life, counts, cb}), List.length(&2, T.Entry<String, V>, C.entries(String, V, C.State{cap, table, order, life, counts, cb})), List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), Aggregate.len_entries(V, C.State{cap, table, order, life, counts, cb}, valid), Equal.cong(List<&2, T.Entry<String, V>>, Nat, xs => List.length(&2, T.Entry<String, V>, xs), C.entries(String, V, C.State{cap, table, order, life, counts, cb}), O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), Ordered.all_entries(V, C.State{cap, table, order, life, counts, cb}, valid))))
  +recency = Config.length(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, valid)
  PublicConfig.unchanged(~String, ~Lookup.string_same, V, zero_value, events, C.State{cap, table, order, life, counts, cb}, Pub.Storage{C.map_size(String, V, C.State{cap, table, order, life, counts, cb}), C.len(String, V, C.State{cap, table, order, life, counts, cb}), cap, counts}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), cap, counts}, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), {==}, Equal.trans(PC.Reply<String, V>, PC.Storage{C.map_size(String, V, C.State{cap, table, order, life, counts, cb}), C.len(String, V, C.State{cap, table, order, life, counts, cb}), cap, counts}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), C.len(String, V, C.State{cap, table, order, life, counts, cb}), cap, counts}, PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), cap, counts}, Equal.cong(Nat, PC.Reply<String, V>, n => PC.Storage{n, C.len(String, V, C.State{cap, table, order, life, counts, cb}), cap, counts}, C.map_size(String, V, C.State{cap, table, order, life, counts, cb}), List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), leaves), Equal.cong(Nat, PC.Reply<String, V>, n => PC.Storage{List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))), n, cap, counts}, C.len(String, V, C.State{cap, table, order, life, counts, cb}), S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), recency)))
