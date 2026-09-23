import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./recency_unique.bend as Unique
import ./recency_head_removal.bend as Head
import ./map_key_membership.bend as Keys
import ./map_delete_common.bend as Common
import ./native_map.bend as Native
import ./canonical_native.bend as CN
import ./representation_parts.bend as Parts

# Two duplicate-free code lists that include each other have equal length.
# Used to relate the native Map leaf count to the recency length.

def without_present(+h: String, +t: List<&2, String>, +key: String, eq: Bool, +decision: {String.eq(h, key) == eq : Bool}, present: {Bool.or(eq, Inv.member(t, key)) == True{} : Bool}, +unique: {Inv.unique(Con{h, t}) == True{} : Bool}, ih: @p: {Inv.member(t, key) == True{} : Bool} -> {Nat.add(1n, List.length(&2, String, C.without(t, key))) == List.length(&2, String, t) : Nat}) -> {Nat.add(1n, List.length(&2, String, C.without_keep(h, C.without(t, key), eq))) == 1n+List.length(&2, String, t) : Nat}:
  match eq:
    case True{}:
      +same = Unique.equal_boolean(h, key, decision)
      missing = Unique.not_true(Inv.member(t, h), R.and_left(Bool.not(Inv.member(t, h)), Inv.unique(t), unique))
      %same : {Nat.add(1n, List.length(&2, String, C.without(t, _))) == 1n+List.length(&2, String, t) : Nat}
      Equal.cong(List<&2, String>, Nat, xs => Nat.add(1n, List.length(&2, String, xs)), C.without(t, h), t, Head.absent(t, h, missing))
    case False{}: Equal.cong(Nat, Nat, n => 1n+n, Nat.add(1n, List.length(&2, String, C.without(t, key))), List.length(&2, String, t), ih(present))

# Removing a code present exactly once shortens the list by exactly one.
def without_length(xs: List<&2, String>, +key: String, present: {Inv.member(xs, key) == True{} : Bool}, +unique: {Inv.unique(xs) == True{} : Bool}) -> {Nat.add(1n, List.length(&2, String, C.without(xs, key))) == List.length(&2, String, xs) : Nat}:
  match xs:
    case Nil{}: Empty.absurd({Nat.add(1n, 0n) == 0n : Nat}, R.false_true(present))
    case Con{+h, +t}: without_present(h, t, key, String.eq(h, key), {==}, present, unique, p => without_length(t, key, p, R.and_right(Bool.not(Inv.member(t, h)), Inv.unique(t), unique)))

def member_without_step(+h: String, +t: List<&2, String>, +key: String, +x: String, drop: Bool, +decision: {String.eq(h, key) == drop : Bool}, hx: Bool, +ehx: {String.eq(h, x) == hx : Bool}, present: {Bool.or(hx, Inv.member(t, x)) == True{} : Bool}, +diff: {String.eq(key, x) == False{} : Bool}, ih: @p: {Inv.member(t, x) == True{} : Bool} -> {Inv.member(C.without(t, key), x) == True{} : Bool}) -> {Inv.member(C.without_keep(h, C.without(t, key), drop), x) == True{} : Bool}:
  match drop:
    case True{}:
      match hx:
        case False{}: ih(present)
        case True{}:
          hk = Unique.equal_boolean(h, key, decision)
          hxe = Unique.equal_boolean(h, x, ehx)
          bad = Equal.trans(Bool, String.eq(key, x), String.eq(h, x), True{}, Equal.cong(String, Bool, z => String.eq(z, x), key, h, Equal.sym(String, h, key, hk)), ehx)
          Empty.absurd({Inv.member(C.without(t, key), x) == True{} : Bool}, R.false_true(Equal.trans(Bool, False{}, String.eq(key, x), True{}, Equal.sym(Bool, String.eq(key, x), False{}, diff), bad)))
    case False{}:
      match hx:
        case True{}:
          %Equal.sym(Bool, String.eq(h, x), True{}, ehx) : {Bool.or(_, Inv.member(C.without(t, key), x)) == True{} : Bool}
          {==}
        case False{}:
          %Equal.sym(Bool, String.eq(h, x), False{}, ehx) : {Bool.or(_, Inv.member(C.without(t, key), x)) == True{} : Bool}
          ih(present)

# A code different from the removed one survives the filter.
def member_without(xs: List<&2, String>, +key: String, +x: String, present: {Inv.member(xs, x) == True{} : Bool}, +diff: {String.eq(key, x) == False{} : Bool}) -> {Inv.member(C.without(xs, key), x) == True{} : Bool}:
  match xs:
    case Nil{}: present
    case Con{+h, +t}: member_without_step(h, t, key, x, String.eq(h, key), {==}, String.eq(h, x), {==}, present, diff, p => member_without(t, key, x, p, diff))

# Inclusion into a list survives removing a code absent from the included list.
def included_without(xs: List<&2, String>, +ys: List<&2, String>, +key: String, +incl: {Inv.included(xs, ys) == True{} : Bool}, +absent: {Inv.member(xs, key) == False{} : Bool}) -> {Inv.included(xs, C.without(ys, key)) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+x, +r}:
      +diff = Unique.unequal_reverse(x, key, Unique.or_false_left(String.eq(x, key), Inv.member(r, key), absent))
      Common.conjunction(Inv.member(C.without(ys, key), x), Inv.included(r, C.without(ys, key)), member_without(ys, key, x, R.and_left(Inv.member(ys, x), Inv.included(r, ys), incl), diff), included_without(r, ys, key, R.and_right(Inv.member(ys, x), Inv.included(r, ys), incl), Unique.or_false_right(String.eq(x, key), Inv.member(r, key), absent)))

def or_right_true(a: Bool, b: Bool, e: {Bool.or(a, b) == True{} : Bool}, no: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}: e
    case True{}: Empty.absurd({b == True{} : Bool}, R.false_true(Equal.sym(Bool, True{}, False{}, no)))

def without_included_step(+y: String, +r: List<&2, String>, +h: String, +t: List<&2, String>, drop: Bool, +decision: {String.eq(y, h) == drop : Bool}, present: {Bool.or(String.eq(h, y), Inv.member(t, y)) == True{} : Bool}, ih: {Inv.included(C.without(r, h), t) == True{} : Bool}) -> {Inv.included(C.without_keep(y, C.without(r, h), drop), t) == True{} : Bool}:
  match drop:
    case True{}: ih
    case False{}: Common.conjunction(Inv.member(t, y), Inv.included(C.without(r, h), t), or_right_true(String.eq(h, y), Inv.member(t, y), present, Unique.unequal_reverse(y, h, decision)), ih)

# Codes of a list included in h::t, other than h, are included in t.
def without_included(ys: List<&2, String>, +h: String, +t: List<&2, String>, +incl: {Inv.included(ys, Con{h, t}) == True{} : Bool}) -> {Inv.included(C.without(ys, h), t) == True{} : Bool}:
  match ys:
    case Nil{}: {==}
    case Con{+y, +r}: without_included_step(y, r, h, t, String.eq(y, h), {==}, R.and_left(Inv.member(Con{h, t}, y), Inv.included(r, Con{h, t}), incl), without_included(r, h, t, R.and_right(Inv.member(Con{h, t}, y), Inv.included(r, Con{h, t}), incl)))

# Duplicate-free, mutually included code lists have equal length.
def same_length(xs: List<&2, String>, +ys: List<&2, String>, +uxs: {Inv.unique(xs) == True{} : Bool}, +uys: {Inv.unique(ys) == True{} : Bool}, +i1: {Inv.included(xs, ys) == True{} : Bool}, +i2: {Inv.included(ys, xs) == True{} : Bool}) -> {List.length(&2, String, xs) == List.length(&2, String, ys) : Nat}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}: {==}
        case Con{+y, +r}: Empty.absurd({0n == 1n+List.length(&2, String, r) : Nat}, R.false_true(i2))
    case Con{+h, +t}:
      +hy = R.and_left(Inv.member(ys, h), Inv.included(t, ys), i1)
      +ut = R.and_right(Bool.not(Inv.member(t, h)), Inv.unique(t), uxs)
      +missing = Unique.not_true(Inv.member(t, h), R.and_left(Bool.not(Inv.member(t, h)), Inv.unique(t), uxs))
      +ih = same_length(t, C.without(ys, h), ut, Unique.filtering_preserves_unique(ys, h, uys), included_without(t, ys, h, R.and_right(Inv.member(ys, h), Inv.included(t, ys), i1), missing), without_included(ys, h, t, i2))
      Equal.trans(Nat, 1n+List.length(&2, String, t), Nat.add(1n, List.length(&2, String, C.without(ys, h))), List.length(&2, String, ys), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, t), List.length(&2, String, C.without(ys, h)), ih), without_length(ys, h, hy, uys))

def list_keys_length(-V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>) -> {List.length(&2, String, CN.list_keys(V, xs)) == List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, xs) : Nat}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{code, item}, +rest}: Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, CN.list_keys(V, rest)), List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, rest), list_keys_length(V, rest))

def size_parts(-V: Data, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, facts: {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), order) == True{} : Bool}) -> {Map.size(&2, Maybe<&2, T.Entry<String, V>>, table) == List.length(&2, String, order) : Nat}:
  (uo, uk, io, ik) = facts
  Equal.trans(Nat, Map.size(&2, Maybe<&2, T.Entry<String, V>>, table), List.length(&2, String, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)), List.length(&2, String, order), Equal.trans(Nat, Map.size(&2, Maybe<&2, T.Entry<String, V>>, table), List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), List.length(&2, String, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)), Equal.sym(Nat, List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), Map.size(&2, Maybe<&2, T.Entry<String, V>>, table), Native.entries_size(Maybe<&2, T.Entry<String, V>>, table)), Equal.trans(Nat, List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), List.length(&2, String, CN.list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table))), List.length(&2, String, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)), Equal.sym(Nat, List.length(&2, String, CN.list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table))), List.length(&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), list_keys_length(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table))), Equal.cong(List<&2, String>, Nat, ks => List.length(&2, String, ks), CN.list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), Equal.sym(List<&2, String>, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), CN.list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), CN.keys_to_list(V, table))))), same_length(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), order, uk, uo, ik, io))

def size_components(-V: Data, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +cap: Nat, facts: {Nat.is_gt(cap, 0n) == True{} : Bool} & {Nat.is_le(List.length(&2, String, order), cap) == True{} : Bool} & {Inv.unique(order) == True{} : Bool} & {Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)) == True{} : Bool} & {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table)) == True{} : Bool} & {Inv.included(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), order) == True{} : Bool} & {Inv.critbit(Maybe<&2, T.Entry<String, V>>, table) == True{} : Bool} & {Inv.identities(~String, ~Codec.string_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)) == True{} : Bool}) -> {Map.size(&2, Maybe<&2, T.Entry<String, V>>, table) == List.length(&2, String, order) : Nat}:
  (positive, bound, uo, uk, io, ik, crit, ident) = facts
  size_parts(V, table, order, (uo, uk, io, ik))

# The native leaf count equals the recency length for represented caches.
def native_size(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.map_size(String, V, c) == C.len(String, V, c) : Nat}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  size_components(V, table, order, cap, Parts.components(~String, ~Codec.string_encode, V, cap, table, order, life, counts, cb, valid))
