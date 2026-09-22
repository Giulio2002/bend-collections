import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./string_order.bend as Order
import ./abstraction_recency.bend as Recency

def native(-V: Data, c: C.Cache<String, V>, order: List<&2, String>) -> List<&2, T.Entry<String, V>>:
  C.State{cap, table, recency, life, counts, cb} = c
  C.entries_go(String, V, order, table)

def collect(-V: Data, found: Maybe<&2, T.Entry<String, V>>, rest: List<&2, T.Entry<String, V>>) -> {C.collect_entry(String, V, found, rest) == O.collect(String, V, found, rest) : List<&2, T.Entry<String, V>>}:
  match found:
    case None{}: {==}
    case Some{entry}: {==}

def ordered(-V: Data, +c: C.Cache<String, V>, order: List<&2, String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {native(V, c, order) == O.ordered(~String, ~Lookup.string_same, V, order, B.model_bindings(String, V, F.abstract(String, V, c))) : List<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +recency, +life, +counts, +cb} = c
  match order:
    case Nil{}: {==}
    case Con{+key, +tail}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, recency, life, counts, cb}, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, recency, life, counts, cb}, key, valid)) : {C.collect_entry(String, V, _, C.entries_go(String, V, tail, table)) == O.collect(String, V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), O.ordered(~String, ~Lookup.string_same, V, tail, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})))) : List<&2, T.Entry<String, V>>}
      Equal.trans(List<&2, T.Entry<String, V>>, C.collect_entry(String, V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), C.entries_go(String, V, tail, table)), C.collect_entry(String, V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), O.ordered(~String, ~Lookup.string_same, V, tail, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})))), O.collect(String, V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), O.ordered(~String, ~Lookup.string_same, V, tail, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})))), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, T.Entry<String, V>>, xs => C.collect_entry(String, V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), xs), C.entries_go(String, V, tail, table), O.ordered(~String, ~Lookup.string_same, V, tail, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb}))), ordered(V, C.State{cap, table, recency, life, counts, cb}, tail, valid)), collect(V, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})), key), O.ordered(~String, ~Lookup.string_same, V, tail, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, recency, life, counts, cb})))))

# Exact ordered entries, retaining original keys, values and deadlines.
def all_entries(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.entries(String, V, c) == O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c)) : List<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(List<&2, String>, Recency.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, Order.faithful(V, C.State{cap, table, order, life, counts, cb}, valid)) : {C.entries_go(String, V, order, table) == O.ordered(~String, ~Lookup.string_same, V, _, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))) : List<&2, T.Entry<String, V>>}
  ordered(V, C.State{cap, table, order, life, counts, cb}, order, valid)

def keys_projection(-K: Data, -V: Data, entries: List<&2, T.Entry<K, V>>) -> {P.keys_of(K, V, entries) == O.entry_keys(K, V, entries) : List<&2, K>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{+key, value, deadline}, +tail}:
      Equal.cong(List<&2, K>, List<&2, K>, xs => Con{key, xs}, P.keys_of(K, V, tail), O.entry_keys(K, V, tail), keys_projection(K, V, tail))

def values_projection(-K: Data, -V: Data, entries: List<&2, T.Entry<K, V>>) -> {P.values_of(K, V, entries) == O.entry_values(K, V, entries) : List<&2, V>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{key, +value, deadline}, +tail}:
      Equal.cong(List<&2, V>, List<&2, V>, xs => Con{value, xs}, P.values_of(K, V, tail), O.entry_values(K, V, tail), values_projection(K, V, tail))

def keys(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {P.keys_of(String, V, C.entries(String, V, c)) == O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))) : List<&2, String>}:
  Equal.trans(List<&2, String>, P.keys_of(String, V, C.entries(String, V, c)), O.entry_keys(String, V, C.entries(String, V, c)), O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))), keys_projection(String, V, C.entries(String, V, c)), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, String>, xs => O.entry_keys(String, V, xs), C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c)), all_entries(V, c, valid)))

def values(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {P.values_of(String, V, C.entries(String, V, c)) == O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))) : List<&2, V>}:
  Equal.trans(List<&2, V>, P.values_of(String, V, C.entries(String, V, c)), O.entry_values(String, V, C.entries(String, V, c)), O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))), values_projection(String, V, C.entries(String, V, c)), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, V>, xs => O.entry_values(String, V, xs), C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c)), all_entries(V, c, valid)))

# Actual aggregate completion constructors, not the still-open expiry loop.
def complete_keys(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {P.complete(String, V, c, P.KeyList{}) == P.Complete{c, O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))), Nil{}} : P.Aggregate<String, V>}:
  Equal.cong(List<&2, String>, P.Aggregate<String, V>, xs => P.Complete{c, xs, Nil{}}, P.keys_of(String, V, C.entries(String, V, c)), O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))), keys(V, c, valid))

def complete_values(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {P.complete(String, V, c, P.ValueList{}) == P.Complete{c, Nil{}, O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))) } : P.Aggregate<String, V>}:
  Equal.cong(List<&2, V>, P.Aggregate<String, V>, xs => P.Complete{c, Nil{}, xs}, P.values_of(String, V, C.entries(String, V, c)), O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c))), values(V, c, valid))
