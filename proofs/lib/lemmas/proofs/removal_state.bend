import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./abstraction_bindings.bend as B
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup
import ./removal_lookup.bend as Delete
import ./removal_representation.bend as Rep
import ./string_order.bend as Order
import ./disabled.bend as Disabled
import ./canonical_native.bend as Native
import ./canonical_string.bend as CS

def normal_lookup(-V: Data, c: C.Cache<String, V>, query: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, c, query) == S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, c)), query) : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, query, valid)

def binding_lookup(-V: Data, +c: C.Cache<String, V>, +removed: String, +query: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)))), query) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, c)), removed), query) : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  Equal.trans(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry)))), query), C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry)), query), S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, C.State{cap, table, order, life, counts, cb})), removed), query), Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry)), query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry)))), query), normal_lookup(V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry)), query, Rep.remove_present(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, removed, False{}, entry, valid))), Delete.correspondence(V, C.State{cap, table, order, life, counts, cb}, removed, query, entry, valid))

# Lookups at any list of recency keys agree after the actual removal.
def lookups_removed(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, xs: List<&2, String>) -> {E.lookups(~String, ~Lookup.string_same, V, xs, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))))) == E.lookups(~String, ~Lookup.string_same, V, xs, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, c)), key)) : List<&2, Maybe<&2, T.Entry<String, V>>>}:
  match xs:
    case Nil{}: {==}
    case Con{+q, +rest}: CS.cons_equal(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry)))), q), S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, c)), key), q), E.lookups(~String, ~Lookup.string_same, V, rest, B.model_bindings(String, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))))), E.lookups(~String, ~Lookup.string_same, V, rest, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, Order.normal(V, c)), key)), binding_lookup(V, c, key, q, entry, valid), lookups_removed(V, c, key, entry, valid, rest))

def normalized(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))), O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, Order.normal(V, c), key, entry))):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  Native.by_fields(V, cap, C.without(order, key), S.unlist(~String, ~Lookup.string_same, order, key), life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, key))), S.erase(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), key), Order.filter(order, key), lookups_removed(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, entry, valid, S.unlist(~String, ~Lookup.string_same, order, key)), Native.stray_normal(V, cap, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, key), C.without(order, key), life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb, Rep.remove_present(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, False{}, entry, valid)), CS.removed_stray(V, order, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), key, Native.stray_normal(V, cap, table, order, life, T.Counts{i, e, r, h, m}, cb, valid)))

# Full abstract state correspondence for the actual removal phase. Native Map
# enumeration order is ignored only for bindings; recency and metrics are exact.
def correspondence(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))), O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry))):
  %Equal.sym(S.Model<String, V>, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))), Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))), Order.normalize(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry)), Rep.remove_present(~String, ~Codec.string_encode, V, c, key, False{}, entry, valid))) : E.states(~String, ~Lookup.string_same, V, _, O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry)))
  %Equal.sym(S.Model<String, V>, F.abstract(String, V, c), Order.normal(V, c), Order.normalize(V, c, valid)) : E.states(~String, ~Lookup.string_same, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry))), O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, _, key, entry)))
  normalized(V, c, key, entry, valid)

def no_events(-V: Data, +entry: T.Entry<String, V>, cb: Bool, disabled: {cb == False{} : Bool}) -> {C.events(String, V, cb, entry) == S.callbacks(String, V, Con{entry, Nil{}}, cb) : List<&2, T.LruEvent<String, V>>}:
  T.Item{+original, +value, +deadline} = entry
  %Equal.sym(Bool, cb, False{}, disabled) : {C.events(String, V, _, T.Item{original, value, deadline}) == S.callbacks(String, V, Con{T.Item{original, value, deadline}, Nil{}}, _) : List<&2, T.LruEvent<String, V>>}
  {==}

def observation(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.remove_present(String, V, c, key, False{}, entry)), S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry)):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  (correspondence(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, entry, valid), {==}, {==}, no_events(V, entry, cb, disabled))
