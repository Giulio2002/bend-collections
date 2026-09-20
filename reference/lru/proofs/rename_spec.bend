import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as E
import ../spec/effectful_aggregate.bend as A
import ../spec/public_commands.bend as P
import ../spec/traces.bend as Traces
import ../spec/numeric.bend as N
import ../spec/clock.bend as Clock
import ../types/model.bend as T
import ./spec_lookup.bend as Lookup
import ./rename_map.bend as RM
import ./rename_machine.bend as RN

# The independent specification over key type K with key equality same
# commutes with renaming every key through enc into the String specification,
# provided String equality of codes agrees with same (agree). For an injective
# codec and a decidable equality this is exactly the statement that same
# decides equality; see proofs/key_equality.bend for the built-in key types.

def rn_model(~K: Data, ~enc: K -> String, -V: Data, s: S.Model<K, V>) -> S.Model<String, V>:
  S.Abstract{cap, bindings, recency, life, counts, cb} = s
  S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, recency), life, counts, cb}

def rn_obs(~K: Data, ~enc: K -> String, -V: Data, o: S.Observation<K, V>) -> S.Observation<String, V>:
  S.Observed{s, item, present, events} = o
  S.Observed{rn_model(~K, ~enc, V, s), RM.rn_item(~K, ~enc, V, item), present, RN.rn_events(~K, ~enc, V, events)}

def keys_append(~K: Data, ~enc: K -> String, xs: List<&2, K>, +key: K) -> {List.append(&2, String, RN.rn_keys(~K, ~enc, xs), Con{enc(key), Nil{}}) == RN.rn_keys(~K, ~enc, List.append(&2, K, xs, Con{key, Nil{}})) : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case Con{+x, rest}: Equal.cong(List<&2, String>, List<&2, String>, t => Con{enc(x), t}, List.append(&2, String, RN.rn_keys(~K, ~enc, rest), Con{enc(key), Nil{}}), RN.rn_keys(~K, ~enc, List.append(&2, K, rest, Con{key, Nil{}})), keys_append(~K, ~enc, rest, key))

def keys_length(~K: Data, ~enc: K -> String, xs: List<&2, K>) -> {List.length(&2, String, RN.rn_keys(~K, ~enc, xs)) == List.length(&2, K, xs) : Nat}:
  match xs:
    case Nil{}: {==}
    case Con{x, rest}: Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, RN.rn_keys(~K, ~enc, rest)), List.length(&2, K, rest), keys_length(~K, ~enc, rest))

def entries_length(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, T.Entry<K, V>>) -> {List.length(&2, T.Entry<String, V>, RN.rn_entries(~K, ~enc, V, xs)) == List.length(&2, T.Entry<K, V>, xs) : Nat}:
  match xs:
    case Nil{}: {==}
    case Con{x, rest}: Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, T.Entry<String, V>, RN.rn_entries(~K, ~enc, V, rest)), List.length(&2, T.Entry<K, V>, rest), entries_length(~K, ~enc, V, rest))

# ---------------------------------------------------------------------------
# spec/cache.bend
def choose(~K: Data, ~enc: K -> String, -V: Data, +e: T.Entry<K, V>, rest: Maybe<&2, T.Entry<K, V>>, b: Bool) -> {S.choose_entry(String, V, RM.rn_entry(~K, ~enc, V, e), RM.rn_item(~K, ~enc, V, rest), b) == RM.rn_item(~K, ~enc, V, S.choose_entry(K, V, e, rest, b)) : Maybe<&2, T.Entry<String, V>>}:
  match b:
    case True{}: {==}
    case False{}: {==}

def omit_entry(~K: Data, ~enc: K -> String, -V: Data, +e: T.Entry<K, V>, rest: List<&2, T.Entry<K, V>>, b: Bool) -> {S.omit_entry(String, V, RM.rn_entry(~K, ~enc, V, e), RN.rn_entries(~K, ~enc, V, rest), b) == RN.rn_entries(~K, ~enc, V, S.omit_entry(K, V, e, rest, b)) : List<&2, T.Entry<String, V>>}:
  match b:
    case True{}: {==}
    case False{}: {==}

def omit_key(~K: Data, ~enc: K -> String, +key: K, rest: List<&2, K>, b: Bool) -> {S.omit_key(String, enc(key), RN.rn_keys(~K, ~enc, rest), b) == RN.rn_keys(~K, ~enc, S.omit_key(K, key, rest, b)) : List<&2, String>}:
  match b:
    case True{}: {==}
    case False{}: {==}

def find(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, bindings: List<&2, T.Entry<K, V>>, +key: K) -> {S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)) == RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, key)) : Maybe<&2, T.Entry<String, V>>}:
  match bindings:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +tail}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, tail), enc(key)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, tail, key)), find(~K, ~enc, ~same, ~agree, V, tail, key)) : {S.choose_entry(String, V, T.Item{enc(k), v, d}, _, String.eq(enc(k), enc(key))) == RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, Con{T.Item{k, v, d}, tail}, key)) : Maybe<&2, T.Entry<String, V>>}
      %Equal.sym(Bool, String.eq(enc(k), enc(key)), same(k)(key), agree(k, key)) : {S.choose_entry(String, V, T.Item{enc(k), v, d}, RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, tail, key)), _) == RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, Con{T.Item{k, v, d}, tail}, key)) : Maybe<&2, T.Entry<String, V>>}
      choose(~K, ~enc, V, T.Item{k, v, d}, S.find(~K, ~same, V, tail, key), same(k)(key))

def erase(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, bindings: List<&2, T.Entry<K, V>>, +key: K) -> {S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)) == RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)) : List<&2, T.Entry<String, V>>}:
  match bindings:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +tail}:
      %Equal.sym(List<&2, T.Entry<String, V>>, S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, tail), enc(key)), RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, tail, key)), erase(~K, ~enc, ~same, ~agree, V, tail, key)) : {S.omit_entry(String, V, T.Item{enc(k), v, d}, _, String.eq(enc(k), enc(key))) == RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, Con{T.Item{k, v, d}, tail}, key)) : List<&2, T.Entry<String, V>>}
      %Equal.sym(Bool, String.eq(enc(k), enc(key)), same(k)(key), agree(k, key)) : {S.omit_entry(String, V, T.Item{enc(k), v, d}, RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, tail, key)), _) == RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, Con{T.Item{k, v, d}, tail}, key)) : List<&2, T.Entry<String, V>>}
      omit_entry(~K, ~enc, V, T.Item{k, v, d}, S.erase(~K, ~same, V, tail, key), same(k)(key))

def unlist(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, order: List<&2, K>, +key: K) -> {S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)) == RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, order, key)) : List<&2, String>}:
  match order:
    case Nil{}: {==}
    case Con{+h, +tail}:
      %Equal.sym(List<&2, String>, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, tail), enc(key)), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, tail, key)), unlist(~K, ~enc, ~same, ~agree, V, tail, key)) : {S.omit_key(String, enc(h), _, String.eq(enc(h), enc(key))) == RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, Con{h, tail}, key)) : List<&2, String>}
      %Equal.sym(Bool, String.eq(enc(h), enc(key)), same(h)(key), agree(h, key)) : {S.omit_key(String, enc(h), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, tail, key)), _) == RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, Con{h, tail}, key)) : List<&2, String>}
      omit_key(~K, ~enc, h, S.unlist(~K, ~same, tail, key), same(h)(key))

def callbacks(~K: Data, ~enc: K -> String, -V: Data, entries: List<&2, T.Entry<K, V>>, enabled: Bool) -> {S.callbacks(String, V, RN.rn_entries(~K, ~enc, V, entries), enabled) == RN.rn_events(~K, ~enc, V, S.callbacks(K, V, entries, enabled)) : List<&2, T.Event<String, V>>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, d}, tail}:
      match enabled:
        case False{}: {==}
        case True{}: Equal.cong(List<&2, T.Event<String, V>>, List<&2, T.Event<String, V>>, t => Con{T.Evicted{enc(k), v}, t}, S.callbacks(String, V, RN.rn_entries(~K, ~enc, V, tail), True{}), RN.rn_events(~K, ~enc, V, S.callbacks(K, V, tail, True{})), callbacks(~K, ~enc, V, tail, True{}))

def remove_existing(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, +entry: T.Entry<K, V>) -> {S.remove_existing(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, entry)) == rn_obs(~K, ~enc, V, S.remove_existing(~K, ~same, V, s, key, entry)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +recency, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = s
  %Equal.sym(List<&2, T.Entry<String, V>>, S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)), erase(~K, ~enc, ~same, ~agree, V, bindings, key)) : {S.Observed{S.Abstract{cap, _, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, recency), enc(key)), life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb}, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, S.callbacks(String, V, Con{RM.rn_entry(~K, ~enc, V, entry), Nil{}}, cb)} == rn_obs(~K, ~enc, V, S.remove_existing(~K, ~same, V, S.Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, m}, cb}, key, entry)) : S.Observation<String, V>}
  %Equal.sym(List<&2, String>, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, recency), enc(key)), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, recency, key)), unlist(~K, ~enc, ~same, ~agree, V, recency, key)) : {S.Observed{S.Abstract{cap, RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)), _, life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb}, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, S.callbacks(String, V, Con{RM.rn_entry(~K, ~enc, V, entry), Nil{}}, cb)} == rn_obs(~K, ~enc, V, S.remove_existing(~K, ~same, V, S.Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, m}, cb}, key, entry)) : S.Observation<String, V>}
  %Equal.sym(List<&2, T.Event<String, V>>, S.callbacks(String, V, Con{RM.rn_entry(~K, ~enc, V, entry), Nil{}}, cb), RN.rn_events(~K, ~enc, V, S.callbacks(K, V, Con{entry, Nil{}}, cb)), callbacks(~K, ~enc, V, Con{entry, Nil{}}, cb)) : {S.Observed{S.Abstract{cap, RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, recency, key)), life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb}, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, _} == rn_obs(~K, ~enc, V, S.remove_existing(~K, ~same, V, S.Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, m}, cb}, key, entry)) : S.Observation<String, V>}
  {==}

def remove_decision(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, found: Maybe<&2, T.Entry<K, V>>) -> {S.remove_decision(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_item(~K, ~enc, V, found)) == rn_obs(~K, ~enc, V, S.remove_decision(~K, ~same, V, s, key, found)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +recency, +life, +counts, +cb} = s
  match found:
    case None{}: {==}
    case Some{+entry}: remove_existing(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, recency, life, counts, cb}, key, entry)

def remove(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K) -> {S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)) == rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, key)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +recency, +life, +counts, +cb} = s
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, key)), find(~K, ~enc, ~same, ~agree, V, bindings, key)) : {S.remove_decision(~String, ~Lookup.string_same, V, S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, recency), life, counts, cb}, enc(key), _) == rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, S.Abstract{cap, bindings, recency, life, counts, cb}, key)) : S.Observation<String, V>}
  remove_decision(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, recency, life, counts, cb}, key, S.find(~K, ~same, V, bindings, key))

# ---------------------------------------------------------------------------
# spec/operations.bend
def moved(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +order: List<&2, K>, +key: K) -> {List.append(&2, String, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), Con{enc(key), Nil{}}) == RN.rn_keys(~K, ~enc, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}})) : List<&2, String>}:
  Equal.trans(List<&2, String>, List.append(&2, String, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), Con{enc(key), Nil{}}), List.append(&2, String, RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, order, key)), Con{enc(key), Nil{}}), RN.rn_keys(~K, ~enc, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}})), Equal.cong(List<&2, String>, List<&2, String>, xs => List.append(&2, String, xs, Con{enc(key), Nil{}}), S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, order, key)), unlist(~K, ~enc, ~same, ~agree, V, order, key)), keys_append(~K, ~enc, S.unlist(~K, ~same, order, key), key))

def write(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, +evicted: Bool, +events: List<&2, T.Event<K, V>>) -> {O.write(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), value, deadline, evicted, RN.rn_events(~K, ~enc, V, events)) == rn_obs(~K, ~enc, V, O.write(~K, ~same, V, s, key, value, deadline, evicted, events)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = s
  %Equal.sym(List<&2, T.Entry<String, V>>, S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)), erase(~K, ~enc, ~same, ~agree, V, bindings, key)) : {S.Observed{S.Abstract{cap, Con{T.Item{enc(key), value, deadline}, _}, List.append(&2, String, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), Con{enc(key), Nil{}}), life, T.Counts{Word.inc(64n, i), e, r, h, m}, cb}, None{}, evicted, RN.rn_events(~K, ~enc, V, events)} == rn_obs(~K, ~enc, V, O.write(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, key, value, deadline, evicted, events)) : S.Observation<String, V>}
  %Equal.sym(List<&2, String>, List.append(&2, String, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), Con{enc(key), Nil{}}), RN.rn_keys(~K, ~enc, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}})), moved(~K, ~enc, ~same, ~agree, V, order, key)) : {S.Observed{S.Abstract{cap, Con{T.Item{enc(key), value, deadline}, RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key))}, _, life, T.Counts{Word.inc(64n, i), e, r, h, m}, cb}, None{}, evicted, RN.rn_events(~K, ~enc, V, events)} == rn_obs(~K, ~enc, V, O.write(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, key, value, deadline, evicted, events)) : S.Observation<String, V>}
  {==}

def count_miss(~K: Data, ~enc: K -> String, -V: Data, s: S.Model<K, V>, tracked: Bool) -> {O.count_miss(String, V, rn_model(~K, ~enc, V, s), tracked) == rn_model(~K, ~enc, V, O.count_miss(K, V, s, tracked)) : S.Model<String, V>}:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  match tracked:
    case False{}: {==}
    case True{}: {==}

def hit_state(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, tracked: Bool) -> {O.hit_state(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), tracked) == rn_model(~K, ~enc, V, O.hit_state(~K, ~same, V, s, key, tracked)) : S.Model<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = s
  match tracked:
    case False{}: {==}
    case True{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(key)), Con{enc(key), Nil{}}), RN.rn_keys(~K, ~enc, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}})), moved(~K, ~enc, ~same, ~agree, V, order, key)) : {S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), _, life, T.Counts{i, e, r, Word.inc(64n, h), m}, cb} == rn_model(~K, ~enc, V, O.hit_state(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, key, True{})) : S.Model<String, V>}
      {==}

def expired_result(~K: Data, ~enc: K -> String, -V: Data, result: S.Observation<K, V>, +tracked: Bool) -> {O.expired_result(String, V, rn_obs(~K, ~enc, V, result), tracked) == rn_obs(~K, ~enc, V, O.expired_result(K, V, result, tracked)) : S.Observation<String, V>}:
  S.Observed{+s, +item, flag, +events} = result
  Equal.cong(S.Model<String, V>, S.Observation<String, V>, x => S.Observed{x, RM.rn_item(~K, ~enc, V, item), False{}, RN.rn_events(~K, ~enc, V, events)}, O.count_miss(String, V, rn_model(~K, ~enc, V, s), tracked), rn_model(~K, ~enc, V, O.count_miss(K, V, s, tracked)), count_miss(~K, ~enc, V, s, tracked))

def read_decide(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +entry: T.Entry<K, V>, +tracked: Bool, expired: Bool) -> {O.read_decide(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, entry), tracked, expired) == rn_obs(~K, ~enc, V, O.read_decide(~K, ~same, V, s, key, entry, tracked, expired)) : S.Observation<String, V>}:
  match expired:
    case True{}: Equal.trans(S.Observation<String, V>, O.expired_result(String, V, S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)), tracked), O.expired_result(String, V, rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, key)), tracked), rn_obs(~K, ~enc, V, O.expired_result(K, V, S.remove(~K, ~same, V, s, key), tracked)), Equal.cong(S.Observation<String, V>, S.Observation<String, V>, o => O.expired_result(String, V, o, tracked), S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)), rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, key)), remove(~K, ~enc, ~same, ~agree, V, s, key)), expired_result(~K, ~enc, V, S.remove(~K, ~same, V, s, key), tracked))
    case False{}: Equal.cong(S.Model<String, V>, S.Observation<String, V>, x => S.Observed{x, Some{RM.rn_entry(~K, ~enc, V, entry)}, True{}, Nil{}}, O.hit_state(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), tracked), rn_model(~K, ~enc, V, O.hit_state(~K, ~same, V, s, key, tracked)), hit_state(~K, ~enc, ~same, ~agree, V, s, key, tracked))

def read_found(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, now: T.Int64, +tracked: Bool, found: Maybe<&2, T.Entry<K, V>>) -> {O.read_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), now, tracked, RM.rn_item(~K, ~enc, V, found)) == rn_obs(~K, ~enc, V, O.read_found(~K, ~same, V, s, key, now, tracked, found)) : S.Observation<String, V>}:
  match found:
    case None{}: Equal.cong(S.Model<String, V>, S.Observation<String, V>, x => S.Observed{x, None{}, False{}, Nil{}}, O.count_miss(String, V, rn_model(~K, ~enc, V, s), tracked), rn_model(~K, ~enc, V, O.count_miss(K, V, s, tracked)), count_miss(~K, ~enc, V, s, tracked))
    case Some{T.Item{+k, +v, +d}}: read_decide(~K, ~enc, ~same, ~agree, V, s, key, T.Item{k, v, d}, tracked, N.expired(d, now))

def oldest_remove(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, order: List<&2, K>) -> {O.oldest_remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), RN.rn_keys(~K, ~enc, order)) == rn_obs(~K, ~enc, V, O.oldest_remove(~K, ~same, V, s, order)) : S.Observation<String, V>}:
  match order:
    case Nil{}: {==}
    case Con{+k, tail}: remove(~K, ~enc, ~same, ~agree, V, s, k)

def remove_oldest(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>) -> {O.remove_oldest(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)) == rn_obs(~K, ~enc, V, O.remove_oldest(~K, ~same, V, s)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  oldest_remove(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, order)

def collect(~K: Data, ~enc: K -> String, -V: Data, found: Maybe<&2, T.Entry<K, V>>, rest: List<&2, T.Entry<K, V>>) -> {O.collect(String, V, RM.rn_item(~K, ~enc, V, found), RN.rn_entries(~K, ~enc, V, rest)) == RN.rn_entries(~K, ~enc, V, O.collect(K, V, found, rest)) : List<&2, T.Entry<String, V>>}:
  match found:
    case None{}: {==}
    case Some{e}: {==}

def ordered(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, order: List<&2, K>, +bindings: List<&2, T.Entry<K, V>>) -> {O.ordered(~String, ~Lookup.string_same, V, RN.rn_keys(~K, ~enc, order), RN.rn_entries(~K, ~enc, V, bindings)) == RN.rn_entries(~K, ~enc, V, O.ordered(~K, ~same, V, order, bindings)) : List<&2, T.Entry<String, V>>}:
  match order:
    case Nil{}: {==}
    case Con{+k, +tail}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(k)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, k)), find(~K, ~enc, ~same, ~agree, V, bindings, k)) : {O.collect(String, V, _, O.ordered(~String, ~Lookup.string_same, V, RN.rn_keys(~K, ~enc, tail), RN.rn_entries(~K, ~enc, V, bindings))) == RN.rn_entries(~K, ~enc, V, O.ordered(~K, ~same, V, Con{k, tail}, bindings)) : List<&2, T.Entry<String, V>>}
      %Equal.sym(List<&2, T.Entry<String, V>>, O.ordered(~String, ~Lookup.string_same, V, RN.rn_keys(~K, ~enc, tail), RN.rn_entries(~K, ~enc, V, bindings)), RN.rn_entries(~K, ~enc, V, O.ordered(~K, ~same, V, tail, bindings)), ordered(~K, ~enc, ~same, ~agree, V, tail, bindings)) : {O.collect(String, V, RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, k)), _) == RN.rn_entries(~K, ~enc, V, O.ordered(~K, ~same, V, Con{k, tail}, bindings)) : List<&2, T.Entry<String, V>>}
      collect(~K, ~enc, V, S.find(~K, ~same, V, bindings, k), O.ordered(~K, ~same, V, tail, bindings))

def all_entries(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>) -> {O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)) == RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s)) : List<&2, T.Entry<String, V>>}:
  S.Abstract{cap, +bindings, order, life, counts, cb} = s
  ordered(~K, ~enc, ~same, ~agree, V, order, bindings)

def observed_state(~K: Data, ~enc: K -> String, -V: Data, result: S.Observation<K, V>) -> {O.observed_state(String, V, rn_obs(~K, ~enc, V, result)) == rn_model(~K, ~enc, V, O.observed_state(K, V, result)) : S.Model<String, V>}:
  S.Observed{s, item, present, events} = result
  {==}

def remove_entries(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, entries: List<&2, T.Entry<K, V>>, +s: S.Model<K, V>) -> {O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, entries), rn_model(~K, ~enc, V, s)) == rn_model(~K, ~enc, V, O.remove_entries(~K, ~same, V, entries, s)) : S.Model<String, V>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{+k, v, d}, +tail}: Equal.trans(S.Model<String, V>, O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, tail), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k)))), O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, tail), rn_model(~K, ~enc, V, O.observed_state(K, V, S.remove(~K, ~same, V, s, k)))), rn_model(~K, ~enc, V, O.remove_entries(~K, ~same, V, tail, O.observed_state(K, V, S.remove(~K, ~same, V, s, k)))), Equal.cong(S.Model<String, V>, S.Model<String, V>, x => O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, tail), x), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k))), rn_model(~K, ~enc, V, O.observed_state(K, V, S.remove(~K, ~same, V, s, k))), Equal.trans(S.Model<String, V>, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k))), O.observed_state(String, V, rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, k))), rn_model(~K, ~enc, V, O.observed_state(K, V, S.remove(~K, ~same, V, s, k))), Equal.cong(S.Observation<String, V>, S.Model<String, V>, o => O.observed_state(String, V, o), S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k)), rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, k)), remove(~K, ~enc, ~same, ~agree, V, s, k)), observed_state(~K, ~enc, V, S.remove(~K, ~same, V, s, k)))), remove_entries(~K, ~enc, ~same, ~agree, V, tail, O.observed_state(K, V, S.remove(~K, ~same, V, s, k))))

def entry_keys(~K: Data, ~enc: K -> String, -V: Data, entries: List<&2, T.Entry<K, V>>) -> {O.entry_keys(String, V, RN.rn_entries(~K, ~enc, V, entries)) == RN.rn_keys(~K, ~enc, O.entry_keys(K, V, entries)) : List<&2, String>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{+k, v, d}, tail}: Equal.cong(List<&2, String>, List<&2, String>, t => Con{enc(k), t}, O.entry_keys(String, V, RN.rn_entries(~K, ~enc, V, tail)), RN.rn_keys(~K, ~enc, O.entry_keys(K, V, tail)), entry_keys(~K, ~enc, V, tail))

def entry_values(~K: Data, ~enc: K -> String, -V: Data, entries: List<&2, T.Entry<K, V>>) -> {O.entry_values(String, V, RN.rn_entries(~K, ~enc, V, entries)) == O.entry_values(K, V, entries) : List<&2, V>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{k, +v, d}, tail}: Equal.cong(List<&2, V>, List<&2, V>, t => Con{v, t}, O.entry_values(String, V, RN.rn_entries(~K, ~enc, V, tail)), O.entry_values(K, V, tail), entry_values(~K, ~enc, V, tail))

# ---------------------------------------------------------------------------
# spec/effectful_operations.bend
def rn_eout(~K: Data, ~enc: K -> String, -V: Data, o: E.Outcome<K, V>) -> E.Outcome<String, V>:
  match o:
    case E.Returned{observed, remaining, requests}: E.Returned{rn_obs(~K, ~enc, V, observed), remaining, requests}
    case E.Failed{s, error, remaining, requests}: E.Failed{rn_model(~K, ~enc, V, s), error, remaining, requests}

def rn_prepared(~K: Data, ~enc: K -> String, -V: Data, p: E.PreparedAdd<K, V>) -> E.PreparedAdd<String, V>:
  E.Prepared{s, key, evicted} = p
  E.Prepared{rn_model(~K, ~enc, V, s), enc(key), evicted}

def e_evicted(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, old: T.Entry<K, V>) -> {E.evicted(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, old)) == rn_prepared(~K, ~enc, V, E.evicted(~K, ~same, V, s, key, old)) : E.PreparedAdd<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = s
  T.Item{+oldkey, +ov, +od} = old
  %Equal.sym(List<&2, T.Entry<String, V>>, S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(oldkey)), RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, oldkey)), erase(~K, ~enc, ~same, ~agree, V, bindings, oldkey)) : {E.Prepared{S.Abstract{cap, _, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(oldkey)), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb}, enc(key), True{}} == rn_prepared(~K, ~enc, V, E.evicted(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{oldkey, ov, od})) : E.PreparedAdd<String, V>}
  %Equal.sym(List<&2, String>, S.unlist(~String, ~Lookup.string_same, RN.rn_keys(~K, ~enc, order), enc(oldkey)), RN.rn_keys(~K, ~enc, S.unlist(~K, ~same, order, oldkey)), unlist(~K, ~enc, ~same, ~agree, V, order, oldkey)) : {E.Prepared{S.Abstract{cap, RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, oldkey)), _, life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb}, enc(key), True{}} == rn_prepared(~K, ~enc, V, E.evicted(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, key, T.Item{oldkey, ov, od})) : E.PreparedAdd<String, V>}
  {==}

def e_evict_found(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, old: Maybe<&2, T.Entry<K, V>>) -> {E.evict_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_item(~K, ~enc, V, old)) == rn_prepared(~K, ~enc, V, E.evict_found(~K, ~same, V, s, key, old)) : E.PreparedAdd<String, V>}:
  match old:
    case None{}: {==}
    case Some{+entry}: e_evicted(~K, ~enc, ~same, ~agree, V, s, key, entry)

def e_evict_first(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>) -> {E.evict_first(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order)) == rn_prepared(~K, ~enc, V, E.evict_first(~K, ~same, V, s, key, bindings, order)) : E.PreparedAdd<String, V>}:
  match order:
    case Nil{}: {==}
    case Con{+old, tail}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(old)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, old)), find(~K, ~enc, ~same, ~agree, V, bindings, old)) : {E.evict_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), _) == rn_prepared(~K, ~enc, V, E.evict_first(~K, ~same, V, s, key, bindings, Con{old, tail})) : E.PreparedAdd<String, V>}
      e_evict_found(~K, ~enc, ~same, ~agree, V, s, key, S.find(~K, ~same, V, bindings, old))

def e_room(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +bindings: List<&2, T.Entry<K, V>>, +order: List<&2, K>, full: Bool) -> {E.room(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), full) == rn_prepared(~K, ~enc, V, E.room(~K, ~same, V, s, key, bindings, order, full)) : E.PreparedAdd<String, V>}:
  match full:
    case False{}: {==}
    case True{}: e_evict_first(~K, ~enc, ~same, ~agree, V, s, key, bindings, order)

def e_absent_add(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K) -> {E.absent_add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)) == rn_prepared(~K, ~enc, V, E.absent_add(~K, ~same, V, s, key)) : E.PreparedAdd<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  %Equal.sym(Nat, List.length(&2, String, RN.rn_keys(~K, ~enc, order)), List.length(&2, K, order), keys_length(~K, ~enc, order)) : {E.room(~String, ~Lookup.string_same, V, S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), life, counts, cb}, enc(key), RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), Nat.is_ge(_, cap)) == rn_prepared(~K, ~enc, V, E.absent_add(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key)) : E.PreparedAdd<String, V>}
  e_room(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, bindings, order, Nat.is_ge(List.length(&2, K, order), cap))

def e_prepare_found(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, found: Maybe<&2, T.Entry<K, V>>) -> {E.prepare_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_item(~K, ~enc, V, found)) == rn_prepared(~K, ~enc, V, E.prepare_found(~K, ~same, V, s, key, found)) : E.PreparedAdd<String, V>}:
  match found:
    case Some{T.Item{o, v, d}}: {==}
    case None{}: e_absent_add(~K, ~enc, ~same, ~agree, V, s, key)

def e_prepare_add(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K) -> {E.prepare_add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)) == rn_prepared(~K, ~enc, V, E.prepare_add(~K, ~same, V, s, key)) : E.PreparedAdd<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, key)), find(~K, ~enc, ~same, ~agree, V, bindings, key)) : {E.prepare_found(~String, ~Lookup.string_same, V, S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), life, counts, cb}, enc(key), _) == rn_prepared(~K, ~enc, V, E.prepare_add(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key)) : E.PreparedAdd<String, V>}
  e_prepare_found(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, S.find(~K, ~same, V, bindings, key))

def e_sampled_add(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, prepared: E.PreparedAdd<K, V>, +value: V, +ns: T.Int64, reply: Clock.Reply) -> {E.sampled_add(~String, ~Lookup.string_same, V, rn_prepared(~K, ~enc, V, prepared), value, ns, reply) == rn_eout(~K, ~enc, V, E.sampled_add(~K, ~same, V, prepared, value, ns, reply)) : E.Outcome<String, V>}:
  E.Prepared{+s, +key, +evicted} = prepared
  match reply:
    case Clock.Rejected{error, remaining}: {==}
    case Clock.Accepted{+now, +remaining}: Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, remaining, 1n}, O.write(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), value, N.deadline(now, ns), evicted, Nil{}), rn_obs(~K, ~enc, V, O.write(~K, ~same, V, s, key, value, N.deadline(now, ns), evicted, Nil{})), write(~K, ~enc, ~same, ~agree, V, s, key, value, N.deadline(now, ns), evicted, Nil{}))

def e_immortal_add(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, prepared: E.PreparedAdd<K, V>, +value: V, +events: List<&2, Clock.Event>) -> {E.immortal_add(~String, ~Lookup.string_same, V, rn_prepared(~K, ~enc, V, prepared), value, events) == rn_eout(~K, ~enc, V, E.immortal_add(~K, ~same, V, prepared, value, events)) : E.Outcome<String, V>}:
  E.Prepared{+s, +key, +evicted} = prepared
  Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, events, 0n}, O.write(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), value, T.I64{Word.zero(64n)}, evicted, Nil{}), rn_obs(~K, ~enc, V, O.write(~K, ~same, V, s, key, value, T.I64{Word.zero(64n)}, evicted, Nil{})), write(~K, ~enc, ~same, ~agree, V, s, key, value, T.I64{Word.zero(64n)}, evicted, Nil{}))

def e_add_lifetime(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +prepared: E.PreparedAdd<K, V>, +value: V, +ns: T.Int64, +events: List<&2, Clock.Event>, immortal: Bool) -> {E.add_lifetime(~String, ~Lookup.string_same, V, rn_prepared(~K, ~enc, V, prepared), value, ns, events, immortal) == rn_eout(~K, ~enc, V, E.add_lifetime(~K, ~same, V, prepared, value, ns, events, immortal)) : E.Outcome<String, V>}:
  match immortal:
    case True{}: e_immortal_add(~K, ~enc, ~same, ~agree, V, prepared, value, events)
    case False{}: e_sampled_add(~K, ~enc, ~same, ~agree, V, prepared, value, ns, Clock.request(events))

def e_add_with_lifetime(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, ns: T.Int64, +events: List<&2, Clock.Event>) -> {E.add_with_lifetime(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), value, ns, events) == rn_eout(~K, ~enc, V, E.add_with_lifetime(~K, ~same, V, s, key, value, ns, events)) : E.Outcome<String, V>}:
  T.I64{+bits} = ns
  %Equal.sym(E.PreparedAdd<String, V>, E.prepare_add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key)), rn_prepared(~K, ~enc, V, E.prepare_add(~K, ~same, V, s, key)), e_prepare_add(~K, ~enc, ~same, ~agree, V, s, key)) : {E.add_lifetime(~String, ~Lookup.string_same, V, _, value, T.I64{bits}, events, N.zero(bits)) == rn_eout(~K, ~enc, V, E.add_with_lifetime(~K, ~same, V, s, key, value, T.I64{bits}, events)) : E.Outcome<String, V>}
  e_add_lifetime(~K, ~enc, ~same, ~agree, V, E.prepare_add(~K, ~same, V, s, key), value, T.I64{bits}, events, N.zero(bits))

def e_add(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, +value: V, +events: List<&2, Clock.Event>) -> {E.add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), value, events) == rn_eout(~K, ~enc, V, E.add(~K, ~same, V, s, key, value, events)) : E.Outcome<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  e_add_with_lifetime(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, value, life, events)

def e_refresh_deadline(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, entry: T.Entry<K, V>, +deadline: T.Int64) -> {E.refresh_deadline(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), RM.rn_entry(~K, ~enc, V, entry), deadline) == rn_obs(~K, ~enc, V, E.refresh_deadline(~K, ~same, V, s, entry, deadline)) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  T.Item{+key, +value, old} = entry
  %Equal.sym(List<&2, T.Entry<String, V>>, S.erase(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RN.rn_entries(~K, ~enc, V, S.erase(~K, ~same, V, bindings, key)), erase(~K, ~enc, ~same, ~agree, V, bindings, key)) : {S.Observed{S.Abstract{cap, Con{T.Item{enc(key), value, deadline}, _}, RN.rn_keys(~K, ~enc, order), life, counts, cb}, Some{T.Item{enc(key), value, deadline}}, True{}, Nil{}} == rn_obs(~K, ~enc, V, E.refresh_deadline(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, T.Item{key, value, old}, deadline)) : S.Observation<String, V>}
  {==}

def e_sampled_refresh(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +prepared: S.Model<K, V>, +entry: T.Entry<K, V>, +ns: T.Int64, reply: Clock.Reply) -> {E.sampled_refresh(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, prepared), RM.rn_entry(~K, ~enc, V, entry), ns, reply) == rn_eout(~K, ~enc, V, E.sampled_refresh(~K, ~same, V, prepared, entry, ns, reply)) : E.Outcome<String, V>}:
  match reply:
    case Clock.Rejected{error, remaining}: {==}
    case Clock.Accepted{+now, +remaining}: Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, remaining, 1n}, E.refresh_deadline(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, prepared), RM.rn_entry(~K, ~enc, V, entry), N.deadline(now, ns)), rn_obs(~K, ~enc, V, E.refresh_deadline(~K, ~same, V, prepared, entry, N.deadline(now, ns))), e_refresh_deadline(~K, ~enc, ~same, ~agree, V, prepared, entry, N.deadline(now, ns)))

def e_refresh_lifetime(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +prepared: S.Model<K, V>, +entry: T.Entry<K, V>, +ns: T.Int64, +events: List<&2, Clock.Event>, immortal: Bool) -> {E.refresh_lifetime(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, prepared), RM.rn_entry(~K, ~enc, V, entry), ns, events, immortal) == rn_eout(~K, ~enc, V, E.refresh_lifetime(~K, ~same, V, prepared, entry, ns, events, immortal)) : E.Outcome<String, V>}:
  match immortal:
    case True{}: Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, events, 0n}, E.refresh_deadline(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, prepared), RM.rn_entry(~K, ~enc, V, entry), T.I64{Word.zero(64n)}), rn_obs(~K, ~enc, V, E.refresh_deadline(~K, ~same, V, prepared, entry, T.I64{Word.zero(64n)})), e_refresh_deadline(~K, ~enc, ~same, ~agree, V, prepared, entry, T.I64{Word.zero(64n)}))
    case False{}: e_sampled_refresh(~K, ~enc, ~same, ~agree, V, prepared, entry, ns, Clock.request(events))

def e_refresh_hit(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, ns: T.Int64, +events: List<&2, Clock.Event>, entry: T.Entry<K, V>) -> {E.refresh_hit(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), ns, events, RM.rn_entry(~K, ~enc, V, entry)) == rn_eout(~K, ~enc, V, E.refresh_hit(~K, ~same, V, s, ns, events, entry)) : E.Outcome<String, V>}:
  T.I64{+bits} = ns
  T.Item{+key, +value, +deadline} = entry
  %Equal.sym(S.Model<String, V>, O.hit_state(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), True{}), rn_model(~K, ~enc, V, O.hit_state(~K, ~same, V, s, key, True{})), hit_state(~K, ~enc, ~same, ~agree, V, s, key, True{})) : {E.refresh_lifetime(~String, ~Lookup.string_same, V, _, T.Item{enc(key), value, deadline}, T.I64{bits}, events, N.zero(bits)) == rn_eout(~K, ~enc, V, E.refresh_hit(~K, ~same, V, s, T.I64{bits}, events, T.Item{key, value, deadline})) : E.Outcome<String, V>}
  e_refresh_lifetime(~K, ~enc, ~same, ~agree, V, O.hit_state(~K, ~same, V, s, key, True{}), T.Item{key, value, deadline}, T.I64{bits}, events, N.zero(bits))

def e_refresh_found(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +ns: T.Int64, +events: List<&2, Clock.Event>, found: Maybe<&2, T.Entry<K, V>>) -> {E.refresh_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), ns, events, RM.rn_item(~K, ~enc, V, found)) == rn_eout(~K, ~enc, V, E.refresh_found(~K, ~same, V, s, ns, events, found)) : E.Outcome<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = s
  match found:
    case None{}: {==}
    case Some{+entry}: e_refresh_hit(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}, ns, events, entry)

def e_refresh(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, +ns: T.Int64, +events: List<&2, Clock.Event>) -> {E.refresh(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), ns, events) == rn_eout(~K, ~enc, V, E.refresh(~K, ~same, V, s, key, ns, events)) : E.Outcome<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, key)), find(~K, ~enc, ~same, ~agree, V, bindings, key)) : {E.refresh_found(~String, ~Lookup.string_same, V, S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), life, counts, cb}, ns, events, _) == rn_eout(~K, ~enc, V, E.refresh(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, ns, events)) : E.Outcome<String, V>}
  e_refresh_found(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, ns, events, S.find(~K, ~same, V, bindings, key))

def e_sampled_read(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +entry: T.Entry<K, V>, +tracked: Bool, reply: Clock.Reply) -> {E.sampled_read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, entry), tracked, reply) == rn_eout(~K, ~enc, V, E.sampled_read(~K, ~same, V, s, key, entry, tracked, reply)) : E.Outcome<String, V>}:
  match reply:
    case Clock.Rejected{error, remaining}: {==}
    case Clock.Accepted{+now, +remaining}: Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, remaining, 1n}, O.read_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), now, tracked, Some{RM.rn_entry(~K, ~enc, V, entry)}), rn_obs(~K, ~enc, V, O.read_found(~K, ~same, V, s, key, now, tracked, Some{entry})), read_found(~K, ~enc, ~same, ~agree, V, s, key, now, tracked, Some{entry}))

def e_read_lifetime(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +entry: T.Entry<K, V>, +tracked: Bool, +events: List<&2, Clock.Event>, immortal: Bool) -> {E.read_lifetime(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, entry), tracked, events, immortal) == rn_eout(~K, ~enc, V, E.read_lifetime(~K, ~same, V, s, key, entry, tracked, events, immortal)) : E.Outcome<String, V>}:
  match immortal:
    case True{}: Equal.cong(S.Observation<String, V>, E.Outcome<String, V>, o => E.Returned{o, events, 0n}, O.read_decide(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), RM.rn_entry(~K, ~enc, V, entry), tracked, False{}), rn_obs(~K, ~enc, V, O.read_decide(~K, ~same, V, s, key, entry, tracked, False{})), read_decide(~K, ~enc, ~same, ~agree, V, s, key, entry, tracked, False{}))
    case False{}: e_sampled_read(~K, ~enc, ~same, ~agree, V, s, key, entry, tracked, Clock.request(events))

def e_read_found(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +key: K, +tracked: Bool, +events: List<&2, Clock.Event>, found: Maybe<&2, T.Entry<K, V>>) -> {E.read_found(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), tracked, events, RM.rn_item(~K, ~enc, V, found)) == rn_eout(~K, ~enc, V, E.read_found(~K, ~same, V, s, key, tracked, events, found)) : E.Outcome<String, V>}:
  match found:
    case None{}: Equal.cong(S.Model<String, V>, E.Outcome<String, V>, x => E.Returned{S.Observed{x, None{}, False{}, Nil{}}, events, 0n}, O.count_miss(String, V, rn_model(~K, ~enc, V, s), tracked), rn_model(~K, ~enc, V, O.count_miss(K, V, s, tracked)), count_miss(~K, ~enc, V, s, tracked))
    case Some{T.Item{+original, +value, T.I64{+bits}}}: e_read_lifetime(~K, ~enc, ~same, ~agree, V, s, key, T.Item{original, value, T.I64{bits}}, tracked, events, N.zero(bits))

def e_read(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +key: K, +tracked: Bool, +events: List<&2, Clock.Event>) -> {E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(key), tracked, events) == rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, key, tracked, events)) : E.Outcome<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(key)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, key)), find(~K, ~enc, ~same, ~agree, V, bindings, key)) : {E.read_found(~String, ~Lookup.string_same, V, S.Abstract{cap, RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), life, counts, cb}, enc(key), tracked, events, _) == rn_eout(~K, ~enc, V, E.read(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, tracked, events)) : E.Outcome<String, V>}
  e_read_found(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, tracked, events, S.find(~K, ~same, V, bindings, key))

# ---------------------------------------------------------------------------
# spec/effectful_aggregate.bend
def rn_prefix(~K: Data, ~enc: K -> String, -V: Data, p: A.Prefix<K, V>) -> A.Prefix<String, V>:
  match p:
    case A.Finished{removed, retained, remaining, requests}: A.Finished{RN.rn_entries(~K, ~enc, V, removed), RN.rn_entries(~K, ~enc, V, retained), remaining, requests}
    case A.Failed{error, removed, retained, remaining, requests}: A.Failed{error, RN.rn_entries(~K, ~enc, V, removed), RN.rn_entries(~K, ~enc, V, retained), remaining, requests}

def a_prepend(~K: Data, ~enc: K -> String, -V: Data, entry: T.Entry<K, V>, result: A.Prefix<K, V>) -> {A.prepend(String, V, RM.rn_entry(~K, ~enc, V, entry), rn_prefix(~K, ~enc, V, result)) == rn_prefix(~K, ~enc, V, A.prepend(K, V, entry, result)) : A.Prefix<String, V>}:
  match result:
    case A.Finished{removed, retained, remaining, requests}: {==}
    case A.Failed{error, removed, retained, remaining, requests}: {==}

def a_decide(~K: Data, ~enc: K -> String, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>, rest: A.Prefix<K, V>, expired: Bool) -> {A.decide(String, V, RM.rn_entry(~K, ~enc, V, entry), RN.rn_entries(~K, ~enc, V, tail), events, rn_prefix(~K, ~enc, V, rest), expired) == rn_prefix(~K, ~enc, V, A.decide(K, V, entry, tail, events, rest, expired)) : A.Prefix<String, V>}:
  match expired:
    case False{}: {==}
    case True{}: a_prepend(~K, ~enc, V, entry, rest)

def a_sentinel(~K: Data, ~enc: K -> String, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>, result: A.Prefix<K, V>, immortal: Bool) -> {A.sentinel(String, V, RM.rn_entry(~K, ~enc, V, entry), RN.rn_entries(~K, ~enc, V, tail), events, rn_prefix(~K, ~enc, V, result), immortal) == rn_prefix(~K, ~enc, V, A.sentinel(K, V, entry, tail, events, result, immortal)) : A.Prefix<String, V>}:
  match immortal:
    case True{}: {==}
    case False{}: {==}

def a_prefix(~K: Data, ~enc: K -> String, -V: Data, ordered: List<&2, T.Entry<K, V>>, events: List<&2, Clock.Event>) -> {A.prefix(String, V, RN.rn_entries(~K, ~enc, V, ordered), events) == rn_prefix(~K, ~enc, V, A.prefix(K, V, ordered, events)) : A.Prefix<String, V>}:
  match ordered:
    case Nil{}: {==}
    case Con{T.Item{+key, +value, T.I64{+bits}}, +tail}:
      match events:
        case Nil{}: a_sentinel(~K, ~enc, V, T.Item{key, value, T.I64{bits}}, tail, Nil{}, A.Failed{Clock.Exhausted{}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, Nil{}, 1n}, N.zero(bits))
        case Con{Clock.InvalidSample{+reason}, +remaining}: a_sentinel(~K, ~enc, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.InvalidSample{reason}, remaining}, A.Failed{Clock.Invalid{reason}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, remaining, 1n}, N.zero(bits))
        case Con{Clock.ProviderException{+reason}, +remaining}: a_sentinel(~K, ~enc, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.ProviderException{reason}, remaining}, A.Failed{Clock.Thrown{reason}, Nil{}, Con{T.Item{key, value, T.I64{bits}}, tail}, remaining, 1n}, N.zero(bits))
        case Con{Clock.Sample{+now}, +remaining}: Equal.trans(A.Prefix<String, V>, A.sentinel(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), Con{Clock.Sample{now}, remaining}, A.decide(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), remaining, A.prefix(String, V, RN.rn_entries(~K, ~enc, V, tail), remaining), N.expired(T.I64{bits}, now)), N.zero(bits)), A.sentinel(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), Con{Clock.Sample{now}, remaining}, rn_prefix(~K, ~enc, V, A.decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now))), N.zero(bits)), rn_prefix(~K, ~enc, V, A.sentinel(K, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.Sample{now}, remaining}, A.decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now)), N.zero(bits))), Equal.cong(A.Prefix<String, V>, A.Prefix<String, V>, x => A.sentinel(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), Con{Clock.Sample{now}, remaining}, x, N.zero(bits)), A.decide(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), remaining, A.prefix(String, V, RN.rn_entries(~K, ~enc, V, tail), remaining), N.expired(T.I64{bits}, now)), rn_prefix(~K, ~enc, V, A.decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now))), Equal.trans(A.Prefix<String, V>, A.decide(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), remaining, A.prefix(String, V, RN.rn_entries(~K, ~enc, V, tail), remaining), N.expired(T.I64{bits}, now)), A.decide(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), remaining, rn_prefix(~K, ~enc, V, A.prefix(K, V, tail, remaining)), N.expired(T.I64{bits}, now)), rn_prefix(~K, ~enc, V, A.decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now))), Equal.cong(A.Prefix<String, V>, A.Prefix<String, V>, x => A.decide(String, V, T.Item{enc(key), value, T.I64{bits}}, RN.rn_entries(~K, ~enc, V, tail), remaining, x, N.expired(T.I64{bits}, now)), A.prefix(String, V, RN.rn_entries(~K, ~enc, V, tail), remaining), rn_prefix(~K, ~enc, V, A.prefix(K, V, tail, remaining)), a_prefix(~K, ~enc, V, tail, remaining)), a_decide(~K, ~enc, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now)))), a_sentinel(~K, ~enc, V, T.Item{key, value, T.I64{bits}}, tail, Con{Clock.Sample{now}, remaining}, A.decide(K, V, T.Item{key, value, T.I64{bits}}, tail, remaining, A.prefix(K, V, tail, remaining), N.expired(T.I64{bits}, now)), N.zero(bits)))

def a_apply_prefix(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, result: A.Prefix<K, V>) -> {A.apply_prefix(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), rn_prefix(~K, ~enc, V, result)) == rn_eout(~K, ~enc, V, A.apply_prefix(~K, ~same, V, s, result)) : E.Outcome<String, V>}:
  match result:
    case A.Finished{removed, retained, +remaining, +requests}: Equal.cong(S.Model<String, V>, E.Outcome<String, V>, x => E.Returned{S.Observed{x, None{}, False{}, Nil{}}, remaining, requests}, O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, removed), rn_model(~K, ~enc, V, s)), rn_model(~K, ~enc, V, O.remove_entries(~K, ~same, V, removed, s)), remove_entries(~K, ~enc, ~same, ~agree, V, removed, s))
    case A.Failed{+error, removed, retained, +remaining, +requests}: Equal.cong(S.Model<String, V>, E.Outcome<String, V>, x => E.Failed{x, error, remaining, requests}, O.remove_entries(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, removed), rn_model(~K, ~enc, V, s)), rn_model(~K, ~enc, V, O.remove_entries(~K, ~same, V, removed, s)), remove_entries(~K, ~enc, ~same, ~agree, V, removed, s))

def a_purge_expired(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +events: List<&2, Clock.Event>) -> {A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events) == rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events)) : E.Outcome<String, V>}:
  Equal.trans(E.Outcome<String, V>, A.apply_prefix(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), A.prefix(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), events)), A.apply_prefix(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), rn_prefix(~K, ~enc, V, A.prefix(K, V, O.all_entries(~K, ~same, V, s), events))), rn_eout(~K, ~enc, V, A.apply_prefix(~K, ~same, V, s, A.prefix(K, V, O.all_entries(~K, ~same, V, s), events))), Equal.cong(A.Prefix<String, V>, E.Outcome<String, V>, p => A.apply_prefix(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), p), A.prefix(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), events), rn_prefix(~K, ~enc, V, A.prefix(K, V, O.all_entries(~K, ~same, V, s), events)), Equal.trans(A.Prefix<String, V>, A.prefix(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), events), A.prefix(String, V, RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s)), events), rn_prefix(~K, ~enc, V, A.prefix(K, V, O.all_entries(~K, ~same, V, s), events)), Equal.cong(List<&2, T.Entry<String, V>>, A.Prefix<String, V>, xs => A.prefix(String, V, xs, events), O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s)), all_entries(~K, ~enc, ~same, ~agree, V, s)), a_prefix(~K, ~enc, V, O.all_entries(~K, ~same, V, s), events))), a_apply_prefix(~K, ~enc, ~same, ~agree, V, s, A.prefix(K, V, O.all_entries(~K, ~same, V, s), events)))

# ---------------------------------------------------------------------------
# spec/public_commands.bend and spec/traces.bend
def rn_projection(~K: Data, ~enc: K -> String, p: P.Projection<K>) -> P.Projection<String>:
  match p:
    case P.Flag{}: P.Flag{}
    case P.ValueOnly{}: P.ValueOnly{}
    case P.RemovedOldest{}: P.RemovedOldest{}
    case P.CapturedOldest{k}: P.CapturedOldest{enc(k)}
    case P.Nothing{}: P.Nothing{}
    case P.Keys{}: P.Keys{}
    case P.Values{}: P.Values{}

def rn_reply(~K: Data, ~enc: K -> String, -V: Data, r: P.Reply<K, V>) -> P.Reply<String, V>:
  match r:
    case P.Unit{}: P.Unit{}
    case P.Boolean{b}: P.Boolean{b}
    case P.Value{v, f}: P.Value{v, f}
    case P.Oldest{k, v, f}: P.Oldest{enc(k), v, f}
    case P.KeyList{ks}: P.KeyList{RN.rn_keys(~K, ~enc, ks)}
    case P.ValueList{vs}: P.ValueList{vs}
    case P.Length{n}: P.Length{n}
    case P.Counters{m}: P.Counters{m}
    case P.Storage{leaves, recency, cap, m}: P.Storage{leaves, recency, cap, m}

def rn_result(~K: Data, ~enc: K -> String, -V: Data, r: P.Result<K, V>) -> P.Result<String, V>:
  match r:
    case P.Returned{s, reply, remaining, requests}: P.Returned{rn_model(~K, ~enc, V, s), rn_reply(~K, ~enc, V, reply), remaining, requests}
    case P.Failed{s, error, remaining, requests}: P.Failed{rn_model(~K, ~enc, V, s), error, remaining, requests}

def rn_results(~K: Data, ~enc: K -> String, -V: Data, rs: List<&2, P.Result<K, V>>) -> List<&2, P.Result<String, V>>:
  match rs:
    case Nil{}: Nil{}
    case Con{r, rest}: Con{rn_result(~K, ~enc, V, r), rn_results(~K, ~enc, V, rest)}

def rn_command(~K: Data, ~enc: K -> String, -V: Data, c: S.Command<K, V>) -> S.Command<String, V>:
  match c:
    case S.Add{k, v}: S.Add{enc(k), v}
    case S.AddWithLifetime{k, v, ns}: S.AddWithLifetime{enc(k), v, ns}
    case S.Get{k}: S.Get{enc(k)}
    case S.GetAndRefresh{k, ns}: S.GetAndRefresh{enc(k), ns}
    case S.Peek{k}: S.Peek{enc(k)}
    case S.Contains{k}: S.Contains{enc(k)}
    case S.Remove{k}: S.Remove{enc(k)}
    case S.RemoveOldest{}: S.RemoveOldest{}
    case S.GetOldest{}: S.GetOldest{}
    case S.Keys{}: S.Keys{}
    case S.Values{}: S.Values{}
    case S.Purge{}: S.Purge{}
    case S.PurgeExpired{}: S.PurgeExpired{}
    case S.Len{}: S.Len{}
    case S.SetLifetime{ns}: S.SetLifetime{ns}
    case S.Metrics{}: S.Metrics{}
    case S.ResetMetrics{}: S.ResetMetrics{}
    case S.Diagnostics{}: S.Diagnostics{}

def rn_commands(~K: Data, ~enc: K -> String, -V: Data, cs: List<&2, S.Command<K, V>>) -> List<&2, S.Command<String, V>>:
  match cs:
    case Nil{}: Nil{}
    case Con{c, rest}: Con{rn_command(~K, ~enc, V, c), rn_commands(~K, ~enc, V, rest)}

def rn_strace(~K: Data, ~enc: K -> String, -V: Data, t: Traces.Trace<K, V>) -> Traces.Trace<String, V>:
  Traces.Finished{s, events, observations, requests} = t
  Traces.Finished{rn_model(~K, ~enc, V, s), events, rn_results(~K, ~enc, V, observations), requests}

def p_value(~K: Data, ~enc: K -> String, -V: Data, +zero_value: V, item: Maybe<&2, T.Entry<K, V>>, +present: Bool) -> {P.value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present) == P.value(K, V, zero_value, item, present) : V}:
  match item:
    case None{}: {==}
    case Some{T.Item{k, v, d}}:
      match present:
        case True{}: {==}
        case False{}: {==}

def p_key(~K: Data, ~enc: K -> String, -V: Data, +zero_key: K, item: Maybe<&2, T.Entry<K, V>>, +present: Bool) -> {P.key(String, V, enc(zero_key), RM.rn_item(~K, ~enc, V, item), present) == enc(P.key(K, V, zero_key, item, present)) : String}:
  match item:
    case None{}: {==}
    case Some{T.Item{k, v, d}}:
      match present:
        case True{}: {==}
        case False{}: {==}

def p_project(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +zero_key: K, +zero_value: V, +item: Maybe<&2, T.Entry<K, V>>, +present: Bool, kind: P.Projection<K>) -> {P.project(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, RM.rn_item(~K, ~enc, V, item), present, rn_projection(~K, ~enc, kind)) == rn_reply(~K, ~enc, V, P.project(~K, ~same, V, s, zero_key, zero_value, item, present, kind)) : P.Reply<String, V>}:
  match kind:
    case P.Flag{}: {==}
    case P.ValueOnly{}: Equal.cong(V, P.Reply<String, V>, x => P.Value{x, present}, P.value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), P.value(K, V, zero_value, item, present), p_value(~K, ~enc, V, zero_value, item, present))
    case P.RemovedOldest{}:
      %Equal.sym(String, P.key(String, V, enc(zero_key), RM.rn_item(~K, ~enc, V, item), present), enc(P.key(K, V, zero_key, item, present)), p_key(~K, ~enc, V, zero_key, item, present)) : {P.Oldest{_, P.value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), present} == rn_reply(~K, ~enc, V, P.project(~K, ~same, V, s, zero_key, zero_value, item, present, P.RemovedOldest{})) : P.Reply<String, V>}
      %Equal.sym(V, P.value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), P.value(K, V, zero_value, item, present), p_value(~K, ~enc, V, zero_value, item, present)) : {P.Oldest{enc(P.key(K, V, zero_key, item, present)), _, present} == rn_reply(~K, ~enc, V, P.project(~K, ~same, V, s, zero_key, zero_value, item, present, P.RemovedOldest{})) : P.Reply<String, V>}
      {==}
    case P.CapturedOldest{+captured}: Equal.cong(V, P.Reply<String, V>, x => P.Oldest{enc(captured), x, present}, P.value(String, V, zero_value, RM.rn_item(~K, ~enc, V, item), present), P.value(K, V, zero_value, item, present), p_value(~K, ~enc, V, zero_value, item, present))
    case P.Nothing{}: {==}
    case P.Keys{}: Equal.cong(List<&2, String>, P.Reply<String, V>, x => P.KeyList{x}, O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s))), RN.rn_keys(~K, ~enc, O.entry_keys(K, V, O.all_entries(~K, ~same, V, s))), Equal.trans(List<&2, String>, O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s))), O.entry_keys(String, V, RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s))), RN.rn_keys(~K, ~enc, O.entry_keys(K, V, O.all_entries(~K, ~same, V, s))), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, String>, xs => O.entry_keys(String, V, xs), O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s)), all_entries(~K, ~enc, ~same, ~agree, V, s)), entry_keys(~K, ~enc, V, O.all_entries(~K, ~same, V, s))))
    case P.Values{}: Equal.cong(List<&2, V>, P.Reply<String, V>, x => P.ValueList{x}, O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s))), O.entry_values(K, V, O.all_entries(~K, ~same, V, s)), Equal.trans(List<&2, V>, O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s))), O.entry_values(String, V, RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s))), O.entry_values(K, V, O.all_entries(~K, ~same, V, s)), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, V>, xs => O.entry_values(String, V, xs), O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, s)), all_entries(~K, ~enc, ~same, ~agree, V, s)), entry_values(~K, ~enc, V, O.all_entries(~K, ~same, V, s))))

def p_observation(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +zero_key: K, +zero_value: V, +kind: P.Projection<K>, observed: S.Observation<K, V>, +events: List<&2, Clock.Event>, +requests: Nat) -> {P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, kind), rn_obs(~K, ~enc, V, observed), events, requests) == rn_result(~K, ~enc, V, P.observation(~K, ~same, V, zero_key, zero_value, kind, observed, events, requests)) : P.Result<String, V>}:
  S.Observed{+s, +item, +present, ignored} = observed
  Equal.cong(P.Reply<String, V>, P.Result<String, V>, r => P.Returned{rn_model(~K, ~enc, V, s), r, events, requests}, P.project(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, RM.rn_item(~K, ~enc, V, item), present, rn_projection(~K, ~enc, kind)), rn_reply(~K, ~enc, V, P.project(~K, ~same, V, s, zero_key, zero_value, item, present, kind)), p_project(~K, ~enc, ~same, ~agree, V, s, zero_key, zero_value, item, present, kind))

def p_effect(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +zero_key: K, +zero_value: V, +kind: P.Projection<K>, outcome: E.Outcome<K, V>) -> {P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, kind), rn_eout(~K, ~enc, V, outcome)) == rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, kind, outcome)) : P.Result<String, V>}:
  match outcome:
    case E.Failed{s, error, remaining, requests}: {==}
    case E.Returned{observed, remaining, requests}: p_observation(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, kind, observed, remaining, requests)

def p_oldest_binding(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>, found: Maybe<&2, T.Entry<K, V>>) -> {P.oldest_binding(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, RM.rn_item(~K, ~enc, V, found)) == rn_result(~K, ~enc, V, P.oldest_binding(~K, ~same, V, s, zero_key, zero_value, events, found)) : P.Result<String, V>}:
  match found:
    case None{}: {==}
    case Some{T.Item{+original, v, d}}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.CapturedOldest{original}), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(original), False{}, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.CapturedOldest{original}), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, original, False{}, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.CapturedOldest{original}, E.read(~K, ~same, V, s, original, False{}, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.CapturedOldest{original}), o), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(original), False{}, events), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, original, False{}, events)), e_read(~K, ~enc, ~same, ~agree, V, s, original, False{}, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.CapturedOldest{original}, E.read(~K, ~same, V, s, original, False{}, events)))

def p_oldest_order(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +s: S.Model<K, V>, +bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>) -> {P.oldest_order(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), RN.rn_entries(~K, ~enc, V, bindings), RN.rn_keys(~K, ~enc, order), enc(zero_key), zero_value, events) == rn_result(~K, ~enc, V, P.oldest_order(~K, ~same, V, s, bindings, order, zero_key, zero_value, events)) : P.Result<String, V>}:
  match order:
    case Nil{}: {==}
    case Con{+first, tail}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, RN.rn_entries(~K, ~enc, V, bindings), enc(first)), RM.rn_item(~K, ~enc, V, S.find(~K, ~same, V, bindings, first)), find(~K, ~enc, ~same, ~agree, V, bindings, first)) : {P.oldest_binding(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, _) == rn_result(~K, ~enc, V, P.oldest_order(~K, ~same, V, s, bindings, Con{first, tail}, zero_key, zero_value, events)) : P.Result<String, V>}
      p_oldest_binding(~K, ~enc, ~same, ~agree, V, s, zero_key, zero_value, events, S.find(~K, ~same, V, bindings, first))

def p_oldest(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>) -> {P.oldest(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events) == rn_result(~K, ~enc, V, P.oldest(~K, ~same, V, s, zero_key, zero_value, events)) : P.Result<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  p_oldest_order(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb}, bindings, order, zero_key, zero_value, events)

def p_diagnostics(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, s: S.Model<K, V>, +events: List<&2, Clock.Event>) -> {P.diagnostics(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events) == rn_result(~K, ~enc, V, P.diagnostics(~K, ~same, V, s, events)) : P.Result<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  %Equal.sym(Nat, List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb}))), List.length(&2, T.Entry<K, V>, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb})), Equal.trans(Nat, List.length(&2, T.Entry<String, V>, O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb}))), List.length(&2, T.Entry<String, V>, RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}))), List.length(&2, T.Entry<K, V>, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb})), Equal.cong(List<&2, T.Entry<String, V>>, Nat, xs => List.length(&2, T.Entry<String, V>, xs), O.all_entries(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb})), RN.rn_entries(~K, ~enc, V, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb})), all_entries(~K, ~enc, ~same, ~agree, V, S.Abstract{cap, bindings, order, life, counts, cb})), entries_length(~K, ~enc, V, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb})))) : {P.Returned{rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb}), P.Storage{_, List.length(&2, String, RN.rn_keys(~K, ~enc, order)), cap, counts}, events, 0n} == rn_result(~K, ~enc, V, P.diagnostics(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, events)) : P.Result<String, V>}
  %Equal.sym(Nat, List.length(&2, String, RN.rn_keys(~K, ~enc, order)), List.length(&2, K, order), keys_length(~K, ~enc, order)) : {P.Returned{rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb}), P.Storage{List.length(&2, T.Entry<K, V>, O.all_entries(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb})), _, cap, counts}, events, 0n} == rn_result(~K, ~enc, V, P.diagnostics(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, events)) : P.Result<String, V>}
  {==}

def p_execute(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>, command: S.Command<K, V>, +s: S.Model<K, V>) -> {P.execute(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, rn_command(~K, ~enc, V, command)) == rn_result(~K, ~enc, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command)) : P.Result<String, V>}:
  match command:
    case S.Add{+k, +v}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), E.add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), v, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), rn_eout(~K, ~enc, V, E.add(~K, ~same, V, s, k, v, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Flag{}, E.add(~K, ~same, V, s, k, v, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), o), E.add(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), v, events), rn_eout(~K, ~enc, V, E.add(~K, ~same, V, s, k, v, events)), e_add(~K, ~enc, ~same, ~agree, V, s, k, v, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Flag{}, E.add(~K, ~same, V, s, k, v, events)))
    case S.AddWithLifetime{+k, +v, +ns}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), E.add_with_lifetime(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), v, ns, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), rn_eout(~K, ~enc, V, E.add_with_lifetime(~K, ~same, V, s, k, v, ns, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Flag{}, E.add_with_lifetime(~K, ~same, V, s, k, v, ns, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), o), E.add_with_lifetime(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), v, ns, events), rn_eout(~K, ~enc, V, E.add_with_lifetime(~K, ~same, V, s, k, v, ns, events)), e_add_with_lifetime(~K, ~enc, ~same, ~agree, V, s, k, v, ns, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Flag{}, E.add_with_lifetime(~K, ~same, V, s, k, v, ns, events)))
    case S.Get{+k}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), True{}, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, True{}, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.ValueOnly{}, E.read(~K, ~same, V, s, k, True{}, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), o), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), True{}, events), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, True{}, events)), e_read(~K, ~enc, ~same, ~agree, V, s, k, True{}, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.ValueOnly{}, E.read(~K, ~same, V, s, k, True{}, events)))
    case S.GetAndRefresh{+k, +ns}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), E.refresh(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), ns, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), rn_eout(~K, ~enc, V, E.refresh(~K, ~same, V, s, k, ns, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.ValueOnly{}, E.refresh(~K, ~same, V, s, k, ns, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), o), E.refresh(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), ns, events), rn_eout(~K, ~enc, V, E.refresh(~K, ~same, V, s, k, ns, events)), e_refresh(~K, ~enc, ~same, ~agree, V, s, k, ns, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.ValueOnly{}, E.refresh(~K, ~same, V, s, k, ns, events)))
    case S.Peek{+k}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), False{}, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, False{}, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.ValueOnly{}, E.read(~K, ~same, V, s, k, False{}, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.ValueOnly{}), o), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), False{}, events), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, False{}, events)), e_read(~K, ~enc, ~same, ~agree, V, s, k, False{}, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.ValueOnly{}, E.read(~K, ~same, V, s, k, False{}, events)))
    case S.Contains{+k}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), False{}, events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, False{}, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Flag{}, E.read(~K, ~same, V, s, k, False{}, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), o), E.read(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k), False{}, events), rn_eout(~K, ~enc, V, E.read(~K, ~same, V, s, k, False{}, events)), e_read(~K, ~enc, ~same, ~agree, V, s, k, False{}, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Flag{}, E.read(~K, ~same, V, s, k, False{}, events)))
    case S.Remove{+k}: Equal.trans(P.Result<String, V>, P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k)), events, 0n), P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, k)), events, 0n), rn_result(~K, ~enc, V, P.observation(~K, ~same, V, zero_key, zero_value, P.Flag{}, S.remove(~K, ~same, V, s, k), events, 0n)), Equal.cong(S.Observation<String, V>, P.Result<String, V>, o => P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Flag{}), o, events, 0n), S.remove(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(k)), rn_obs(~K, ~enc, V, S.remove(~K, ~same, V, s, k)), remove(~K, ~enc, ~same, ~agree, V, s, k)), p_observation(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Flag{}, S.remove(~K, ~same, V, s, k), events, 0n))
    case S.RemoveOldest{}: Equal.trans(P.Result<String, V>, P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.RemovedOldest{}), O.remove_oldest(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), events, 0n), P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.RemovedOldest{}), rn_obs(~K, ~enc, V, O.remove_oldest(~K, ~same, V, s)), events, 0n), rn_result(~K, ~enc, V, P.observation(~K, ~same, V, zero_key, zero_value, P.RemovedOldest{}, O.remove_oldest(~K, ~same, V, s), events, 0n)), Equal.cong(S.Observation<String, V>, P.Result<String, V>, o => P.observation(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.RemovedOldest{}), o, events, 0n), O.remove_oldest(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s)), rn_obs(~K, ~enc, V, O.remove_oldest(~K, ~same, V, s)), remove_oldest(~K, ~enc, ~same, ~agree, V, s)), p_observation(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.RemovedOldest{}, O.remove_oldest(~K, ~same, V, s), events, 0n))
    case S.GetOldest{}: p_oldest(~K, ~enc, ~same, ~agree, V, s, zero_key, zero_value, events)
    case S.Keys{}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Keys{}), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Keys{}), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Keys{}, A.purge_expired(~K, ~same, V, s, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Keys{}), o), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events)), a_purge_expired(~K, ~enc, ~same, ~agree, V, s, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Keys{}, A.purge_expired(~K, ~same, V, s, events)))
    case S.Values{}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Values{}), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Values{}), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Values{}, A.purge_expired(~K, ~same, V, s, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Values{}), o), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events)), a_purge_expired(~K, ~enc, ~same, ~agree, V, s, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Values{}, A.purge_expired(~K, ~same, V, s, events)))
    case S.PurgeExpired{}: Equal.trans(P.Result<String, V>, P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Nothing{}), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events)), P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Nothing{}), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events))), rn_result(~K, ~enc, V, P.effect(~K, ~same, V, zero_key, zero_value, P.Nothing{}, A.purge_expired(~K, ~same, V, s, events))), Equal.cong(E.Outcome<String, V>, P.Result<String, V>, o => P.effect(~String, ~Lookup.string_same, V, enc(zero_key), zero_value, rn_projection(~K, ~enc, P.Nothing{}), o), A.purge_expired(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), events), rn_eout(~K, ~enc, V, A.purge_expired(~K, ~same, V, s, events)), a_purge_expired(~K, ~enc, ~same, ~agree, V, s, events)), p_effect(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, P.Nothing{}, A.purge_expired(~K, ~same, V, s, events)))
    case S.Purge{}:
      S.Abstract{cap, bindings, order, life, counts, cb} = s
      {==}
    case S.Len{}:
      S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
      Equal.cong(Nat, P.Result<String, V>, n => P.Returned{rn_model(~K, ~enc, V, S.Abstract{cap, bindings, order, life, counts, cb}), P.Length{n}, events, 0n}, List.length(&2, String, RN.rn_keys(~K, ~enc, order)), List.length(&2, K, order), keys_length(~K, ~enc, order))
    case S.SetLifetime{ns}:
      S.Abstract{cap, bindings, order, life, counts, cb} = s
      {==}
    case S.Metrics{}:
      S.Abstract{cap, bindings, order, life, counts, cb} = s
      {==}
    case S.ResetMetrics{}:
      S.Abstract{cap, bindings, order, life, counts, cb} = s
      {==}
    case S.Diagnostics{}: p_diagnostics(~K, ~enc, ~same, ~agree, V, s, events)

def t_prepend(~K: Data, ~enc: K -> String, -V: Data, r: P.Result<K, V>, t: Traces.Trace<K, V>) -> {Traces.prepend(String, V, rn_result(~K, ~enc, V, r), rn_strace(~K, ~enc, V, t)) == rn_strace(~K, ~enc, V, Traces.prepend(K, V, r, t)) : Traces.Trace<String, V>}:
  match r:
    case P.Returned{s, reply, remaining, requests}:
      Traces.Finished{s2, events, observations, count} = t
      {==}
    case P.Failed{s, error, remaining, requests}:
      Traces.Finished{s2, events, observations, count} = t
      {==}

def t_run_cons(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, -V: Data, +zero_key: K, +zero_value: V, +tail: List<&2, S.Command<K, V>>, o: P.Result<K, V>, ih: @+s2: S.Model<K, V> -> @+ev2: List<&2, Clock.Event> -> {Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), rn_model(~K, ~enc, V, s2), enc(zero_key), zero_value, ev2) == rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, ev2)) : Traces.Trace<String, V>}) -> {Traces.prepend(String, V, rn_result(~K, ~enc, V, o), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), Traces.state(String, V, rn_result(~K, ~enc, V, o)), enc(zero_key), zero_value, Traces.remaining(String, V, rn_result(~K, ~enc, V, o)))) == rn_strace(~K, ~enc, V, Traces.prepend(K, V, o, Traces.run(~K, ~same, V, tail, Traces.state(K, V, o), zero_key, zero_value, Traces.remaining(K, V, o)))) : Traces.Trace<String, V>}:
  match o:
    case P.Returned{+s2, +reply, +remaining, +requests}: Equal.trans(Traces.Trace<String, V>, Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Returned{s2, reply, remaining, requests}), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), rn_model(~K, ~enc, V, s2), enc(zero_key), zero_value, remaining)), Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Returned{s2, reply, remaining, requests}), rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining))), rn_strace(~K, ~enc, V, Traces.prepend(K, V, P.Returned{s2, reply, remaining, requests}, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining))), Equal.cong(Traces.Trace<String, V>, Traces.Trace<String, V>, t => Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Returned{s2, reply, remaining, requests}), t), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), rn_model(~K, ~enc, V, s2), enc(zero_key), zero_value, remaining), rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining)), ih(s2)(remaining)), t_prepend(~K, ~enc, V, P.Returned{s2, reply, remaining, requests}, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining)))
    case P.Failed{+s2, +error, +remaining, +requests}: Equal.trans(Traces.Trace<String, V>, Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Failed{s2, error, remaining, requests}), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), rn_model(~K, ~enc, V, s2), enc(zero_key), zero_value, remaining)), Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Failed{s2, error, remaining, requests}), rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining))), rn_strace(~K, ~enc, V, Traces.prepend(K, V, P.Failed{s2, error, remaining, requests}, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining))), Equal.cong(Traces.Trace<String, V>, Traces.Trace<String, V>, t => Traces.prepend(String, V, rn_result(~K, ~enc, V, P.Failed{s2, error, remaining, requests}), t), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), rn_model(~K, ~enc, V, s2), enc(zero_key), zero_value, remaining), rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining)), ih(s2)(remaining)), t_prepend(~K, ~enc, V, P.Failed{s2, error, remaining, requests}, Traces.run(~K, ~same, V, tail, s2, zero_key, zero_value, remaining)))

def t_run(~K: Data, ~enc: K -> String, ~same: K -> K -> Bool, ~agree: @+a: K -> @+b: K -> {String.eq(enc(a), enc(b)) == same(a)(b) : Bool}, -V: Data, commands: List<&2, S.Command<K, V>>, +s: S.Model<K, V>, +zero_key: K, +zero_value: V, +events: List<&2, Clock.Event>) -> {Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, commands), rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events) == rn_strace(~K, ~enc, V, Traces.run(~K, ~same, V, commands, s, zero_key, zero_value, events)) : Traces.Trace<String, V>}:
  match commands:
    case Nil{}: {==}
    case Con{+command, +tail}:
      Equal.trans(Traces.Trace<String, V>, Traces.prepend(String, V, P.execute(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, rn_command(~K, ~enc, V, command)), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), Traces.state(String, V, P.execute(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, rn_command(~K, ~enc, V, command))), enc(zero_key), zero_value, Traces.remaining(String, V, P.execute(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, rn_command(~K, ~enc, V, command))))), Traces.prepend(String, V, rn_result(~K, ~enc, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command)), Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), Traces.state(String, V, rn_result(~K, ~enc, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command))), enc(zero_key), zero_value, Traces.remaining(String, V, rn_result(~K, ~enc, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command))))), rn_strace(~K, ~enc, V, Traces.prepend(K, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command), Traces.run(~K, ~same, V, tail, Traces.state(K, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command)), zero_key, zero_value, Traces.remaining(K, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command))))), Equal.cong(P.Result<String, V>, Traces.Trace<String, V>, x => Traces.prepend(String, V, x, Traces.run(~String, ~Lookup.string_same, V, rn_commands(~K, ~enc, V, tail), Traces.state(String, V, x), enc(zero_key), zero_value, Traces.remaining(String, V, x))), P.execute(~String, ~Lookup.string_same, V, rn_model(~K, ~enc, V, s), enc(zero_key), zero_value, events, rn_command(~K, ~enc, V, command)), rn_result(~K, ~enc, V, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command)), p_execute(~K, ~enc, ~same, ~agree, V, zero_key, zero_value, events, command, s)), t_run_cons(~K, ~enc, ~same, V, zero_key, zero_value, tail, P.execute(~K, ~same, V, s, zero_key, zero_value, events, command), s2 => ev2 => t_run(~K, ~enc, ~same, ~agree, V, tail, s2, zero_key, zero_value, ev2)))
