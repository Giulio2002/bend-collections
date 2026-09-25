import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../src/public.bend as Pub
import ../src/entry_ops.bend as Entry
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as Eff
import ../spec/effectful_aggregate.bend as A
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
import ./extensional_states.bend as Ext
import ./lookup_refinement.bend as L
import ./cache_key_identity.bend as Key
import ./representation_access.bend as Access
import ./configuration_observations.bend as Config
import ./numeric.bend as Numeric
import ./map_routing.bend as Routing
import ./cache_oldest_available.bend as Oldest
import ./cache_storage_preservation.bend as Storage
import ./cache_order.bend as CacheOrder
import ./recency_head_removal.bend as RecencyHead
import ./removal_lookup.bend as RemovalLookup
import ./removal_state.bend as RemovalState
import ./removal_representation.bend as RemovalRep
import ./ordered_entries.bend as Ordered
import ./canonical_string.bend as CS
import ./canonical_remove.bend as CR

# Keys, Values and PurgeExpired through the actual machine: the oldest expired
# prefix is removed one entry per accepted sample; completed removals survive a
# later provider failure; an immortal or live oldest entry stops the walk.

def first_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> Maybe<&2, T.Entry<K, V>>:
  match xs:
    case Nil{}: None{}
    case Con{x, rest}: Some{x}

def tail_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match xs:
    case Nil{}: Nil{}
    case Con{x, rest}: rest

def unwrap(-K: Data, -V: Data, m: Maybe<&2, T.Entry<K, V>>, fallback: T.Entry<K, V>) -> T.Entry<K, V>:
  match m:
    case None{}: fallback
    case Some{x}: x

def or_left(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, Routing.false_true(Equal.sym(Bool, True{}, False{}, e)))

def or_right(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}: e
    case True{}: Empty.absurd({b == False{} : Bool}, Routing.false_true(Equal.sym(Bool, True{}, False{}, e)))

def not_true(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, Routing.false_true(e))

# The native head of the recency order is present under the representation.
def head_available(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == True{} : Bool}) -> Oldest.available(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h):
  Oldest.ordered_lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h, Storage.valid(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, valid)), Storage.populated(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, valid)), Routing.and_left(Oldest.order_in_keys(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}), CacheOrder.keys_in_order(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}), Storage.membership(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, valid))), Oldest.head_member(h, rest))

def oldest_head_found(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, w: Oldest.available(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h)) -> {C.oldest_entry(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == first_of(String, V, C.entries(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb})) : Maybe<&2, T.Entry<String, V>>}:
  (+entry, found) = w
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h), Some{entry}, found) : {_ == first_of(String, V, C.collect_entry(String, V, _, C.entries_go(String, V, rest, table))) : Maybe<&2, T.Entry<String, V>>}
  {==}

def oldest_head(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.oldest_entry(String, V, c) == first_of(String, V, C.entries(String, V, c)) : Maybe<&2, T.Entry<String, V>>}:
  match c:
    case C.State{+cap, +table, Nil{}, +life, +counts, +cb}: {==}
    case C.State{+cap, +table, Con{+h, +rest}, +life, +counts, +cb}: oldest_head_found(V, cap, table, h, rest, life, counts, cb, head_available(V, cap, table, h, rest, life, counts, cb, valid))

# Removing the head code does not change the native lookups of the other codes.
def entries_go_skip(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +h: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}, xs: List<&2, String>, +missing: {Inv.member(xs, h) == False{} : Bool}) -> {C.entries_go(String, V, xs, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, h)) == C.entries_go(String, V, xs, table) : List<&2, T.Entry<String, V>>}:
  match xs:
    case Nil{}: {==}
    case Con{+q, +rest}:
      +different = CS.symmetric_false(q, h, or_left(String.eq(q, h), Inv.member(rest, h), missing))
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, h, False{}, entry)), q), C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, q), RemovalLookup.other(V, C.State{cap, table, order, life, counts, cb}, h, q, entry, valid, different)) : {C.collect_entry(String, V, _, C.entries_go(String, V, rest, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, h))) == C.collect_entry(String, V, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, q), C.entries_go(String, V, rest, table)) : List<&2, T.Entry<String, V>>}
      Equal.cong(List<&2, T.Entry<String, V>>, List<&2, T.Entry<String, V>>, tail => C.collect_entry(String, V, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, q), tail), C.entries_go(String, V, rest, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, h)), C.entries_go(String, V, rest, table), entries_go_skip(V, cap, table, order, life, counts, cb, h, entry, valid, rest, or_right(String.eq(q, h), Inv.member(rest, h), missing)))

def entries_tail_found(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == True{} : Bool}, w: Oldest.available(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h)) -> {C.entries(String, V, C.step_cache(String, V, C.remove_oldest(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, False{}))) == tail_of(String, V, C.entries(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb})) : List<&2, T.Entry<String, V>>}:
  (+entry, found) = w
  +unique = Access.get_unique(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, valid)
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h), Some{entry}, found) : {C.entries(String, V, C.step_cache(String, V, C.remove_found(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h, False{}, _))) == tail_of(String, V, C.collect_entry(String, V, _, C.entries_go(String, V, rest, table))) : List<&2, T.Entry<String, V>>}
  %Equal.sym(List<&2, String>, C.without(Con{h, rest}, h), rest, RecencyHead.head(h, rest, unique)) : {C.entries_go(String, V, _, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, h)) == C.entries_go(String, V, rest, table) : List<&2, T.Entry<String, V>>}
  entries_go_skip(V, cap, table, Con{h, rest}, life, counts, cb, h, entry, valid, rest, not_true(Inv.member(rest, h), Routing.and_left(Bool.not(Inv.member(rest, h)), Inv.unique(rest), unique)))

# Removing the oldest entry drops exactly the head of the ordered entries.
def entries_tail(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.entries(String, V, C.step_cache(String, V, C.remove_oldest(String, V, c, False{}))) == tail_of(String, V, C.entries(String, V, c)) : List<&2, T.Entry<String, V>>}:
  match c:
    case C.State{+cap, +table, Nil{}, +life, +counts, +cb}: {==}
    case C.State{+cap, +table, Con{+h, +rest}, +life, +counts, +cb}: entries_tail_found(V, cap, table, h, rest, life, counts, cb, valid, head_available(V, cap, table, h, rest, life, counts, cb, valid))

def is_con(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> Bool:
  match xs:
    case Nil{}: False{}
    case Con{x, rest}: True{}

def head_facts(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +k: String, +v: V, +d: T.Int64, +xs: List<&2, T.Entry<String, V>>, listed: {Con{T.Item{k, v, d}, xs} == C.entries(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) : List<&2, T.Entry<String, V>>}, w: Oldest.available(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h)) -> {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}:
  (+entry, +found) = w
  eq1 = Equal.cong(List<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, ys => first_of(String, V, ys), Con{T.Item{k, v, d}, xs}, C.entries(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}), listed)
  eq2 = Equal.cong(Maybe<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, m => first_of(String, V, C.collect_entry(String, V, m, C.entries_go(String, V, rest, table))), C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h), Some{entry}, found)
  eq3 = Equal.trans(Maybe<&2, T.Entry<String, V>>, Some{T.Item{k, v, d}}, first_of(String, V, C.entries(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb})), Some{entry}, eq1, eq2)
  eq4 = Equal.cong(Maybe<&2, T.Entry<String, V>>, T.Entry<String, V>, m => unwrap(String, V, m, T.Item{k, v, d}), Some{T.Item{k, v, d}}, Some{entry}, eq3)
  Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h), Some{entry}, Some{T.Item{k, v, d}}, found, Equal.cong(T.Entry<String, V>, Maybe<&2, T.Entry<String, V>>, x => Some{x}, entry, T.Item{k, v, d}, Equal.sym(T.Entry<String, V>, T.Item{k, v, d}, entry, eq4)))

def head_code(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +k: String, +v: V, +d: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == True{} : Bool}, found: {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}) -> {h == k : String}:
  Key.string_lookup_key(V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h, k, v, d, Access.get_identities(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, valid), found)

def head_lookup_found(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +k: String, +v: V, +d: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == True{} : Bool}, +found: {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}) -> {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, k) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}:
  %head_code(V, cap, table, h, rest, life, counts, cb, k, v, d, valid, found) : {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, _) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}
  found

def remove_head_found(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +h: String, +rest: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +k: String, +v: V, +d: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, Con{h, rest}, life, counts, cb}) == True{} : Bool}, +found: {C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}) -> {C.remove_oldest(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, False{}) == C.remove_present(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, k, False{}, T.Item{k, v, d}) : C.Step<String, V>}:
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h), Some{T.Item{k, v, d}}, found) : {C.remove_found(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, h, False{}, _) == C.remove_present(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, k, False{}, T.Item{k, v, d}) : C.Step<String, V>}
  Equal.cong(String, C.Step<String, V>, x => C.remove_present(String, V, C.State{cap, table, Con{h, rest}, life, counts, cb}, x, False{}, T.Item{k, v, d}), h, k, head_code(V, cap, table, h, rest, life, counts, cb, k, v, d, valid, found))

# Both facts about the oldest entry named by the ordered entries.
def head_lookup(-V: Data, c: C.Cache<String, V>, +k: String, +v: V, +d: T.Int64, +xs: List<&2, T.Entry<String, V>>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +listed: {Con{T.Item{k, v, d}, xs} == C.entries(String, V, c) : List<&2, T.Entry<String, V>>}) -> {C.lookup(String, V, c, k) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}:
  match c:
    case C.State{+cap, +table, Nil{}, +life, +counts, +cb}: Empty.absurd({C.lookup(String, V, C.State{cap, table, Nil{}, life, counts, cb}, k) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<String, V>>}, Routing.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, T.Entry<String, V>>, Bool, ys => is_con(String, V, ys), Con{T.Item{k, v, d}, xs}, Nil{}, listed))))
    case C.State{+cap, +table, Con{+h, +rest}, +life, +counts, +cb}: head_lookup_found(V, cap, table, h, rest, life, counts, cb, k, v, d, valid, head_facts(V, cap, table, h, rest, life, counts, cb, k, v, d, xs, listed, head_available(V, cap, table, h, rest, life, counts, cb, valid)))

def remove_head(-V: Data, c: C.Cache<String, V>, +k: String, +v: V, +d: T.Int64, +xs: List<&2, T.Entry<String, V>>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +listed: {Con{T.Item{k, v, d}, xs} == C.entries(String, V, c) : List<&2, T.Entry<String, V>>}) -> {C.remove_oldest(String, V, c, False{}) == C.remove_present(String, V, c, k, False{}, T.Item{k, v, d}) : C.Step<String, V>}:
  match c:
    case C.State{+cap, +table, Nil{}, +life, +counts, +cb}: Empty.absurd({C.remove_oldest(String, V, C.State{cap, table, Nil{}, life, counts, cb}, False{}) == C.remove_present(String, V, C.State{cap, table, Nil{}, life, counts, cb}, k, False{}, T.Item{k, v, d}) : C.Step<String, V>}, Routing.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, T.Entry<String, V>>, Bool, ys => is_con(String, V, ys), Con{T.Item{k, v, d}, xs}, Nil{}, listed))))
    case C.State{+cap, +table, Con{+h, +rest}, +life, +counts, +cb}: remove_head_found(V, cap, table, h, rest, life, counts, cb, k, v, d, valid, head_facts(V, cap, table, h, rest, life, counts, cb, k, v, d, xs, listed, head_available(V, cap, table, h, rest, life, counts, cb, valid)))

def keys_length(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> {List.length(&2, K, F.keys_of(K, V, xs)) == List.length(&2, T.Entry<K, V>, xs) : Nat}:
  match xs:
    case Nil{}: {==}
    case Con{T.Item{k, v, d}, +rest}: Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, K, F.keys_of(K, V, rest)), List.length(&2, T.Entry<K, V>, rest), keys_length(K, V, rest))

# The walk's fuel (Len) is the number of ordered entries.
def len_entries(-V: Data, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.len(String, V, c) == List.length(&2, T.Entry<String, V>, C.entries(String, V, c)) : Nat}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  Equal.trans(Nat, C.len(String, V, C.State{cap, table, order, life, counts, cb}), S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), List.length(&2, T.Entry<String, V>, C.entries(String, V, C.State{cap, table, order, life, counts, cb})), Config.length(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, valid), keys_length(String, V, C.entries(String, V, C.State{cap, table, order, life, counts, cb})))

# Final reply of a completed walk, for any count and remaining events.
def completion(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +events: List<&2, Clock.ClockEvent>, +count: Nat, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), shape: Pub.Shape<String>) -> R.results(~String, ~Lookup.string_same, V, D.Returned{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), events, count}, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), S.Observed{s, None{}, False{}, Nil{}}, events, count)):
  match shape:
    case Pub.Flag{}: (related, {==}, {==}, {==})
    case Pub.ValueOnly{}: (related, {==}, {==}, {==})
    case Pub.Captured{k}: (related, {==}, {==}, {==})
    case Pub.Nothing{}: (related, {==}, {==}, {==})
    case Pub.AllKeys{}:
      +entries = Equal.trans(List<&2, T.Entry<String, V>>, C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c)), O.all_entries(~String, ~Lookup.string_same, V, s), Ordered.all_entries(V, c, valid), CS.entries_agreement(V, F.abstract(String, V, c), s, related))
      %Equal.sym(List<&2, String>, Entry.keys_of(String, V, C.entries(String, V, c)), O.entry_keys(String, V, C.entries(String, V, c)), Ordered.keys_projection(String, V, C.entries(String, V, c))) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s) & {PC.KeyList{_} == PC.KeyList{O.entry_keys(String, V, O.all_entries(~String, ~Lookup.string_same, V, s))} : PC.Reply<String, V>} & {events == events : List<&2, Clock.ClockEvent>} & {count == count : Nat}
      (related, Equal.cong(List<&2, T.Entry<String, V>>, PC.Reply<String, V>, ys => PC.KeyList{O.entry_keys(String, V, ys)}, C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, s), entries), {==}, {==})
    case Pub.AllValues{}:
      +entries = Equal.trans(List<&2, T.Entry<String, V>>, C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, F.abstract(String, V, c)), O.all_entries(~String, ~Lookup.string_same, V, s), Ordered.all_entries(V, c, valid), CS.entries_agreement(V, F.abstract(String, V, c), s, related))
      %Equal.sym(List<&2, V>, Entry.values_of(String, V, C.entries(String, V, c)), O.entry_values(String, V, C.entries(String, V, c)), Ordered.values_projection(String, V, C.entries(String, V, c))) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s) & {PC.ValueList{_} == PC.ValueList{O.entry_values(String, V, O.all_entries(~String, ~Lookup.string_same, V, s))} : PC.Reply<String, V>} & {events == events : List<&2, Clock.ClockEvent>} & {count == count : Nat}
      (related, Equal.cong(List<&2, T.Entry<String, V>>, PC.Reply<String, V>, ys => PC.ValueList{O.entry_values(String, V, ys)}, C.entries(String, V, c), O.all_entries(~String, ~Lookup.string_same, V, s), entries), {==}, {==})

# One more accepted request on both sides.
def pbump(-K: Data, -V: Data, r: PC.CmdResult<K, V>) -> PC.CmdResult<K, V>:
  match r:
    case PC.Returned{s, reply, events, count}: PC.Returned{s, reply, events, 1n+count}
    case PC.Failed{s, error, events, count}: PC.Failed{s, error, events, 1n+count}

def ebump(-K: Data, -V: Data, r: Eff.Outcome<K, V>) -> Eff.Outcome<K, V>:
  match r:
    case Eff.Returned{observed, events, count}: Eff.Returned{observed, events, 1n+count}
    case Eff.Failed{s, error, events, count}: Eff.Failed{s, error, events, 1n+count}

def prefix_bump(-V: Data, +s: S.Model<String, V>, +k: String, v: V, d: T.Int64, result: A.Prefix<String, V>) -> {A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prepend(String, V, T.Item{k, v, d}, result)) == ebump(String, V, A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), result)) : Eff.Outcome<String, V>}:
  match result:
    case A.Finished{removed, retained, events, requests}: {==}
    case A.Failed{error, removed, retained, events, requests}: {==}

def effect_bump(-V: Data, zero_key: String, zero_value: V, kind: PC.Projection<String>, outcome: Eff.Outcome<String, V>) -> {PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, ebump(String, V, outcome)) == pbump(String, V, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, kind, outcome)) : PC.CmdResult<String, V>}:
  match outcome:
    case Eff.Returned{S.Observed{s, item, present, ignored}, events, count}: {==}
    case Eff.Failed{s, error, events, count}: {==}

def results_bump(-V: Data, actual: D.Outcome<String, V>, expected: PC.CmdResult<String, V>, related: R.results(~String, ~Lookup.string_same, V, actual, expected)) -> R.results(~String, ~Lookup.string_same, V, D.bump(String, V, actual), pbump(String, V, expected)):
  match actual expected:
    case D.Returned{c, answer, events, count} PC.Returned{s, reply, evs, n}:
      (st, rp, ev, ct) = related
      (st, rp, ev, Equal.cong(Nat, Nat, x => 1n+x, count, n, ct))
    case D.Failed{c, error, events, count} PC.Failed{s, err, evs, n}:
      (st, er, ev, ct) = related
      (st, er, ev, Equal.cong(Nat, Nat, x => 1n+x, count, n, ct))
    case D.Returned{c, answer, events, count} PC.Failed{s, err, evs, n}: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Returned{c, answer, events, 1n+count}, PC.Failed{s, err, evs, 1n+n}), related)
    case D.Failed{c, error, events, count} PC.Returned{s, reply, evs, n}: Empty.absurd(R.results(~String, ~Lookup.string_same, V, D.Failed{c, error, events, 1n+count}, PC.Returned{s, reply, evs, 1n+n}), related)

def states_from_equal(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, eq: {a == b : S.Model<String, V>}) -> E.states(~String, ~Lookup.string_same, V, a, b):
  Equal.cong(S.Model<String, V>, E.Canonical<String, V>, m => E.canonical(~String, ~Lookup.string_same, V, m), a, b, eq)

# The state after removing the oldest (expired) entry corresponds to the
# independent removal of that entry's original key from the related model.
def step_related(-V: Data, c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +d: T.Int64, +xs: List<&2, T.Entry<String, V>>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), +listed: {Con{T.Item{k, v, d}, xs} == C.entries(String, V, c) : List<&2, T.Entry<String, V>>}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_oldest(String, V, c, False{}))), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  +hl = head_lookup(V, C.State{cap, table, order, life, counts, cb}, k, v, d, xs, valid, listed)
  +found = Equal.trans(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), k), C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, k), Some{T.Item{k, v, d}}, Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, k), S.find(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), k), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, k, valid)), hl)
  +same_removal = states_from_equal(V, O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k, T.Item{k, v, d})), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k)), Equal.cong(Maybe<&2, T.Entry<String, V>>, S.Model<String, V>, m => O.observed_state(String, V, S.remove_decision(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k, m)), Some{T.Item{k, v, d}}, S.find(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), k), Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), k), Some{T.Item{k, v, d}}, found)))
  %Equal.sym(C.Step<String, V>, C.remove_oldest(String, V, C.State{cap, table, order, life, counts, cb}, False{}), C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, k, False{}, T.Item{k, v, d}), remove_head(V, C.State{cap, table, order, life, counts, cb}, k, v, d, xs, valid, listed)) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, _)), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)))
  Ext.string_transitive(V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, counts, cb}, k, False{}, T.Item{k, v, d}))), O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k, T.Item{k, v, d})), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), RemovalState.correspondence(V, C.State{cap, table, order, life, counts, cb}, k, T.Item{k, v, d}, valid), Ext.string_transitive(V, O.observed_state(String, V, S.remove_existing(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k, T.Item{k, v, d})), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), k)), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), same_removal, CR.remove_congruence(V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), s, k, related)))

def flag_step(-K: Data, -V: Data, step: C.Step<K, V>) -> {Disabled.flag(K, V, C.step_cache(K, V, step)) == Disabled.step_flag(K, V, step) : Bool}:
  C.Out{c, item, flag, events} = step
  {==}

def finished_now(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s)) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.complete(String, V, zero_value, c, shape)), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), S.Observed{s, None{}, False{}, Nil{}}, events, 0n)):
  %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.Finished{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape)}), D.Returned{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), events, 0n}, Drive.finished(String, V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape))) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), S.Observed{s, None{}, False{}, Nil{}}, events, 0n))
  completion(V, zero_key, zero_value, c, s, events, 0n, valid, related, shape)

def finished_after_sample(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s)) -> R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, events, Pub.complete(String, V, zero_value, c, shape))), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), S.Observed{s, None{}, False{}, Nil{}}, events, 1n)):
  %Equal.sym(D.Outcome<String, V>, D.bump(String, V, D.drive(String, V, zero_value, events, Pub.Finished{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape)})), D.Returned{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), events, 1n}, Equal.cong(D.Outcome<String, V>, D.Outcome<String, V>, outcome => D.bump(String, V, outcome), D.drive(String, V, zero_value, events, Pub.Finished{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape)}), D.Returned{c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), events, 0n}, Drive.finished(String, V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape)))) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), S.Observed{s, None{}, False{}, Nil{}}, events, 1n))
  completion(V, zero_key, zero_value, c, s, events, 1n, valid, related, shape)

# After an accepted sample: expired removes the oldest and continues; live stops.
def walk_decide(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, +tail: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), ih: @ev: List<&2, Clock.ClockEvent> -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, ev, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, ev)))), expired: Bool) -> R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_decide(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, expired))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.decide(String, V, T.Item{k, v, T.I64{bits}}, rest, tail, A.prefix(String, V, rest, tail), expired)))):
  match expired:
    case False{}: finished_after_sample(V, zero_key, zero_value, c, s, shape, tail, valid, related)
    case True{}:
      %Equal.sym(Eff.Outcome<String, V>, A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prepend(String, V, T.Item{k, v, T.I64{bits}}, A.prefix(String, V, rest, tail))), ebump(String, V, A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, tail))), prefix_bump(V, s, k, v, T.I64{bits}, A.prefix(String, V, rest, tail))) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), _))
      %Equal.sym(PC.CmdResult<String, V>, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), ebump(String, V, A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, tail)))), pbump(String, V, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, tail)))), effect_bump(V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, tail)))) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape))), _)
      results_bump(V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, tail))), ih(tail))

def walk_sample(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, +now: T.Int64, +tail: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), +oe: {C.oldest_entry(String, V, c) == Some{T.Item{k, v, T.I64{bits}}} : Maybe<&2, T.Entry<String, V>>}, ih: @ev: List<&2, Clock.ClockEvent> -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, ev, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, ev)))), immortal: Bool) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, Con{Clock.Sample{now}, tail}, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.sentinel(String, V, T.Item{k, v, T.I64{bits}}, rest, Con{Clock.Sample{now}, tail}, A.decide(String, V, T.Item{k, v, T.I64{bits}}, rest, tail, A.prefix(String, V, rest, tail), N.expired(T.I64{bits}, now)), immortal)))):
  match immortal:
    case True{}: finished_now(V, zero_key, zero_value, c, s, shape, Con{Clock.Sample{now}, tail}, valid, related)
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.oldest_entry(String, V, c), Some{T.Item{k, v, T.I64{bits}}}, oe) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_sampled(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, now, _))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.decide(String, V, T.Item{k, v, T.I64{bits}}, rest, tail, A.prefix(String, V, rest, tail), N.expired(T.I64{bits}, now)))))
      %Equal.sym(Bool, Time.expired(T.I64{bits}, now), N.expired(T.I64{bits}, now), Numeric.expiration_refines(T.I64{bits}, now)) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_decide(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, _))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.decide(String, V, T.Item{k, v, T.I64{bits}}, rest, tail, A.prefix(String, V, rest, tail), N.expired(T.I64{bits}, now)))))
      walk_decide(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, tail, valid, related, ih, N.expired(T.I64{bits}, now))

def walk_nil(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), immortal: Bool) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, Nil{}, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.sentinel(String, V, T.Item{k, v, T.I64{bits}}, rest, Nil{}, A.Failed{Clock.Exhausted{}, Nil{}, Con{T.Item{k, v, T.I64{bits}}, rest}, Nil{}, 1n}, immortal)))):
  match immortal:
    case True{}: finished_now(V, zero_key, zero_value, c, s, shape, Nil{}, valid, related)
    case False{}: (related, {==}, {==}, {==})

def walk_invalid(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, +reason: String, +tail: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), immortal: Bool) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, Con{Clock.InvalidSample{reason}, tail}, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.sentinel(String, V, T.Item{k, v, T.I64{bits}}, rest, Con{Clock.InvalidSample{reason}, tail}, A.Failed{Clock.Invalid{reason}, Nil{}, Con{T.Item{k, v, T.I64{bits}}, rest}, tail, 1n}, immortal)))):
  match immortal:
    case True{}: finished_now(V, zero_key, zero_value, c, s, shape, Con{Clock.InvalidSample{reason}, tail}, valid, related)
    case False{}: (related, {==}, {==}, {==})

def walk_thrown(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, +reason: String, +tail: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), immortal: Bool) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, Con{Clock.ProviderException{reason}, tail}, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.sentinel(String, V, T.Item{k, v, T.I64{bits}}, rest, Con{Clock.ProviderException{reason}, tail}, A.Failed{Clock.Thrown{reason}, Nil{}, Con{T.Item{k, v, T.I64{bits}}, rest}, tail, 1n}, immortal)))):
  match immortal:
    case True{}: finished_now(V, zero_key, zero_value, c, s, shape, Con{Clock.ProviderException{reason}, tail}, valid, related)
    case False{}: (related, {==}, {==}, {==})

def walk_events(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +s: S.Model<String, V>, +k: String, +v: V, +bits: Word(64n), +rest: List<&2, T.Entry<String, V>>, +shape: Pub.Shape<String>, events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), +oe: {C.oldest_entry(String, V, c) == Some{T.Item{k, v, T.I64{bits}}} : Maybe<&2, T.Entry<String, V>>}, ih: @ev: List<&2, Clock.ClockEvent> -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, ev, Pub.expire_next(String, V, zero_value, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), A.prefix(String, V, rest, ev))))) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, N.zero(bits))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, Con{T.Item{k, v, T.I64{bits}}, rest}, events)))):
  match events:
    case Nil{}: walk_nil(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, valid, related, N.zero(bits))
    case Con{Clock.InvalidSample{+reason}, +tail}: walk_invalid(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, reason, tail, valid, related, N.zero(bits))
    case Con{Clock.ProviderException{+reason}, +tail}: walk_thrown(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, reason, tail, valid, related, N.zero(bits))
    case Con{Clock.Sample{+now}, +tail}: walk_sample(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, now, tail, valid, related, oe, ih, N.zero(bits))

# Induction over the ordered entries still to inspect (oldest first).
def walk(-V: Data, +zero_key: String, +zero_value: V, xs: List<&2, T.Entry<String, V>>, +c: C.Cache<String, V>, +n: Nat, +s: S.Model<String, V>, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +related: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), s), +listed: {xs == C.entries(String, V, c) : List<&2, T.Entry<String, V>>}, +count: {n == List.length(&2, T.Entry<String, V>, xs) : Nat}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_next(String, V, zero_value, c, n, shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, xs, events)))):
  match xs:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, count) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_next(String, V, zero_value, c, _, shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, Nil{}, events))))
      finished_now(V, zero_key, zero_value, c, s, shape, events, valid, related)
    case Con{T.Item{+k, +v, T.I64{+bits}}, +rest}:
      +oe = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.oldest_entry(String, V, c), first_of(String, V, C.entries(String, V, c)), Some{T.Item{k, v, T.I64{bits}}}, oldest_head(V, c, valid), Equal.cong(List<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, ys => first_of(String, V, ys), C.entries(String, V, c), Con{T.Item{k, v, T.I64{bits}}, rest}, Equal.sym(List<&2, T.Entry<String, V>>, Con{T.Item{k, v, T.I64{bits}}, rest}, C.entries(String, V, c), listed)))
      +next_listed = Equal.sym(List<&2, T.Entry<String, V>>, C.entries(String, V, C.step_cache(String, V, C.remove_oldest(String, V, c, False{}))), rest, Equal.trans(List<&2, T.Entry<String, V>>, C.entries(String, V, C.step_cache(String, V, C.remove_oldest(String, V, c, False{}))), tail_of(String, V, C.entries(String, V, c)), rest, entries_tail(V, c, valid), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, T.Entry<String, V>>, ys => tail_of(String, V, ys), C.entries(String, V, c), Con{T.Item{k, v, T.I64{bits}}, rest}, Equal.sym(List<&2, T.Entry<String, V>>, Con{T.Item{k, v, T.I64{bits}}, rest}, C.entries(String, V, c), listed))))
      %Equal.sym(Nat, n, 1n+List.length(&2, T.Entry<String, V>, rest), count) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_next(String, V, zero_value, c, _, shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, Con{T.Item{k, v, T.I64{bits}}, rest}, events))))
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.oldest_entry(String, V, c), Some{T.Item{k, v, T.I64{bits}}}, oe) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_entry(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, Con{T.Item{k, v, T.I64{bits}}, rest}, events))))
      %Numeric.zero_comparison_correspondence(64n, bits) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_lifetime(String, V, zero_value, c, List.length(&2, T.Entry<String, V>, rest), shape, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, s, A.prefix(String, V, Con{T.Item{k, v, T.I64{bits}}, rest}, events))))
      walk_events(V, zero_key, zero_value, c, s, k, v, bits, rest, shape, events, valid, related, oe, ev => walk(V, zero_key, zero_value, rest, C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), List.length(&2, T.Entry<String, V>, rest), O.observed_state(String, V, S.remove(~String, ~Lookup.string_same, V, s, k)), shape, ev, RemovalRep.string_remove_oldest(V, c, False{}, valid), step_related(V, c, s, k, v, T.I64{bits}, rest, valid, related, listed), next_listed, {==}))

# Whole public aggregate walk over every provider-event list.
def aggregate(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire(String, V, zero_value, c, shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.purge_expired(~String, ~Lookup.string_same, V, F.abstract(String, V, c), events))):
  %Ordered.all_entries(V, c, valid) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.expire_next(String, V, zero_value, c, C.len(String, V, c), shape)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, Finish.projection(String, shape), A.apply_prefix(~String, ~Lookup.string_same, V, F.abstract(String, V, c), A.prefix(String, V, _, events))))
  walk(V, zero_key, zero_value, C.entries(String, V, c), c, C.len(String, V, c), F.abstract(String, V, c), shape, events, valid, Ext.string_reflexive(V, F.abstract(String, V, c)), {==}, len_entries(V, c, valid))

def string_keys(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.Keys{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.Keys{})):
  aggregate(V, zero_key, zero_value, c, Pub.AllKeys{}, events, valid)

def string_values(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.Values{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.Values{})):
  aggregate(V, zero_key, zero_value, c, Pub.AllValues{}, events, valid)

def string_purge_expired(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.PurgeExpired{}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.PurgeExpired{})):
  aggregate(V, zero_key, zero_value, c, Pub.Nothing{}, events, valid)
