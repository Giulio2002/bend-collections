import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./string_order.bend as Order
import ./read_representation.bend as Rep

def normalized(-V: Data, c: C.Cache<String, V>, +key: String, entry: T.Entry<String, V>, tracked: Bool) -> {Order.normal(V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))) == O.hit_state(~String, ~Lookup.string_same, V, Order.normal(V, c), key, tracked) : S.Model<String, V>}:
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  match tracked:
    case False{}: {==}
    case True{}:
      Equal.cong(List<&2, String>, S.Model<String, V>, xs => S.Abstract{cap, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), List.append(&2, String, xs, Con{key, Nil{}}), life, T.Counts{i, e, r, Word.inc(64n, h), m}, cb}, C.without(order, key), S.unlist(~String, ~Lookup.string_same, order, key), Order.filter(order, key))

# Exact state correspondence for actual live reads, including tracked recency
# movement and Hits. The successful lookup premise supplies representation of
# the actual output through the previously checked preservation theorem.
def state(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +tracked: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, present: {C.lookup(String, V, c, key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> {F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))) == O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked) : S.Model<String, V>}:
  Equal.trans(S.Model<String, V>, F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), Order.normal(V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked), Order.normalize(V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked)), Rep.live(~String, ~Codec.string_encode, V, c, key, entry, tracked, present, valid)), Equal.trans(S.Model<String, V>, Order.normal(V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), O.hit_state(~String, ~Lookup.string_same, V, Order.normal(V, c), key, tracked), O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked), normalized(V, c, key, entry, tracked), Equal.cong(S.Model<String, V>, S.Model<String, V>, s => O.hit_state(~String, ~Lookup.string_same, V, s, key, tracked), Order.normal(V, c), F.abstract(String, V, c), Equal.sym(S.Model<String, V>, F.abstract(String, V, c), Order.normal(V, c), Order.normalize(V, c, valid)))))

def projection(-V: Data, c: C.Cache<String, V>, key: String, entry: T.Entry<String, V>, tracked: Bool) -> {F.observe(String, V, C.read_live(String, V, c, key, entry, tracked)) == S.Observed{F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), Some{entry}, True{}, Nil{}} : S.Observation<String, V>}:
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def observation(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +tracked: Bool, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, present: {C.lookup(String, V, c, key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> {F.observe(String, V, C.read_live(String, V, c, key, entry, tracked)) == O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, False{}) : S.Observation<String, V>}:
  Equal.trans(S.Observation<String, V>, F.observe(String, V, C.read_live(String, V, c, key, entry, tracked)), S.Observed{F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), Some{entry}, True{}, Nil{}}, O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, False{}), projection(V, c, key, entry, tracked), Equal.cong(S.Model<String, V>, S.Observation<String, V>, s => S.Observed{s, Some{entry}, True{}, Nil{}}, F.abstract(String, V, C.step_cache(String, V, C.read_live(String, V, c, key, entry, tracked))), O.hit_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, tracked), state(V, c, key, entry, tracked, valid, present)))
