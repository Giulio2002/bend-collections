import Base
import ./native_map.bend as N
import ./map_set_critbit.bend as Set
import ./map_insert_critbit.bend as Distinct
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as Logic
import ../src/cache.bend as C
import ../types/model.bend as T

law or_false_left:
  for a: Bool
  for b: Bool
  for e: {a || b == False{} : Bool}
  {a == False{} : Bool}
def or_false_left(a, b, e):
  match a:
    case False{}: {==}
    case True{}: e

law or_false_right:
  for a: Bool
  for b: Bool
  for e: {a || b == False{} : Bool}
  {b == False{} : Bool}
def or_false_right(a, b, e):
  match a:
    case False{}: e
    case True{}: Empty.absurd({b == False{} : Bool}, R.false_true(Equal.sym(Bool, True{}, False{}, e)))

law not_true:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}
def not_true(b, e):
  match b:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, R.false_true(e))

law keep_absent:
  for +head: String
  for +tail: List<&2, String>
  for +query: String
  for drop: Bool
  for head_absent: {String.eq(head, query) == False{} : Bool}
  for tail_absent: {Inv.member(tail, query) == False{} : Bool}
  {Inv.member(C.without_keep(head, tail, drop), query) == False{} : Bool}
def keep_absent(head, tail, query, drop, head_absent, tail_absent):
  match drop:
    case True{}: tail_absent
    case False{}:
      %Equal.sym(Bool, String.eq(head, query), False{}, head_absent) : {_ || Inv.member(tail, query) == False{} : Bool}
      tail_absent

law filtering_preserves_absence:
  for xs: List<&2, String>
  for +removed: String
  for +query: String
  for +absent: {Inv.member(xs, query) == False{} : Bool}
  {Inv.member(C.without(xs, removed), query) == False{} : Bool}
def filtering_preserves_absence(xs, removed, query, absent):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      keep_absent(head, C.without(tail, removed), query, String.eq(head, removed), or_false_left(String.eq(head, query), Inv.member(tail, query), absent), filtering_preserves_absence(tail, removed, query, or_false_right(String.eq(head, query), Inv.member(tail, query), absent)))

law target_branch:
  for +head: String
  for +tail: List<&2, String>
  for +key: String
  for drop: Bool
  for decision: {String.eq(head, key) == drop : Bool}
  for rest: {Inv.member(tail, key) == False{} : Bool}
  {Inv.member(C.without_keep(head, tail, drop), key) == False{} : Bool}
def target_branch(head, tail, key, drop, decision, rest):
  match drop:
    case True{}: rest
    case False{}: keep_absent(head, tail, key, False{}, decision, rest)

law filtering_removes_target:
  for xs: List<&2, String>
  for +key: String
  {Inv.member(C.without(xs, key), key) == False{} : Bool}
def filtering_removes_target(xs, key):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      target_branch(head, C.without(tail, key), key, String.eq(head, key), {==}, filtering_removes_target(tail, key))

law keep_unique:
  for +head: String
  for +tail: List<&2, String>
  for drop: Bool
  for absent: {Inv.member(tail, head) == False{} : Bool}
  for unique: {Inv.unique(tail) == True{} : Bool}
  {Inv.unique(C.without_keep(head, tail, drop)) == True{} : Bool}
def keep_unique(head, tail, drop, absent, unique):
  match drop:
    case True{}: unique
    case False{}:
      Logic.conjunction(Bool.not(Inv.member(tail, head)), Inv.unique(tail), Equal.cong(Bool, Bool, Bool.not, Inv.member(tail, head), False{}, absent), unique)

law filtering_preserves_unique:
  for xs: List<&2, String>
  for +key: String
  for +unique: {Inv.unique(xs) == True{} : Bool}
  {Inv.unique(C.without(xs, key)) == True{} : Bool}
def filtering_preserves_unique(xs, key, unique):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      keep_unique(head, C.without(tail, key), String.eq(head, key), filtering_preserves_absence(tail, key, head, not_true(Inv.member(tail, head), R.and_left(Bool.not(Inv.member(tail, head)), Inv.unique(tail), unique))), filtering_preserves_unique(tail, key, R.and_right(Bool.not(Inv.member(tail, head)), Inv.unique(tail), unique)))

def unique_recency(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, lifetime, counts, cb} = c
  Inv.unique(order)

law removal_preserves_unique_recency:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for unique: {unique_recency(K, V, c) == True{} : Bool}
  {unique_recency(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == True{} : Bool}
def removal_preserves_unique_recency(K, V, c, code, evict, entry, unique):
  C.State{cap, table, order, life, counts, cb} = c
  filtering_preserves_unique(order, code, unique)

law equal_comparison:
  for +a: String
  for +b: String
  for cmp: Cmp
  for tag: {N.comparison_tag(String, String.cmp(a, b)) == cmp : Cmp}
  for eq: {Cmp.is_eq(cmp) == True{} : Bool}
  {a == b : String}
def equal_comparison(a, b, cmp, tag, eq):
  match cmp:
    case EQ{}: N.string_equal_from_comparison(a, b, tag)
    case LT{}: Empty.absurd({a == b : String}, R.false_true(eq))
    case GT{}: Empty.absurd({a == b : String}, R.false_true(eq))

law equal_boolean:
  for +a: String
  for +b: String
  for eq: {String.eq(a, b) == True{} : Bool}
  {a == b : String}
def equal_boolean(a, b, eq):
  equal_comparison(a, b, N.comparison_tag(String, String.cmp(a, b)), {==}, Equal.trans(Bool, Cmp.is_eq(N.comparison_tag(String, String.cmp(a, b))), String.eq(a, b), True{}, Equal.sym(Bool, String.eq(a, b), Cmp.is_eq(N.comparison_tag(String, String.cmp(a, b))), Set.comparison_boolean(a, b, N.comparison_tag(String, String.cmp(a, b)), {==})), eq))

law unequal_reverse_case:
  for +a: String
  for +b: String
  for unequal: {String.eq(a, b) == False{} : Bool}
  for result: Bool
  for observed: {String.eq(b, a) == result : Bool}
  {String.eq(b, a) == False{} : Bool}
def unequal_reverse_case(a, b, unequal, result, observed):
  match result:
    case False{}: observed
    case True{}:
      Empty.absurd({String.eq(b, a) == False{} : Bool}, Distinct.unequal_distinct(a, b, unequal, Equal.sym(String, b, a, equal_boolean(b, a, observed))))

law unequal_reverse:
  for +a: String
  for +b: String
  for unequal: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}
def unequal_reverse(a, b, unequal):
  unequal_reverse_case(a, b, unequal, String.eq(b, a), {==})

law append_absent:
  for xs: List<&2, String>
  for +key: String
  for +query: String
  for +absent: {Inv.member(xs, query) == False{} : Bool}
  for +different: {String.eq(key, query) == False{} : Bool}
  {Inv.member(List.append(&2, String, xs, Con{key, Nil{}}), query) == False{} : Bool}
def append_absent(xs, key, query, absent, different):
  match xs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(key, query), False{}, different) : {_ || False{} == False{} : Bool}
      {==}
    case Con{+head, +tail}:
      keep_absent(head, List.append(&2, String, tail, Con{key, Nil{}}), query, False{}, or_false_left(String.eq(head, query), Inv.member(tail, query), absent), append_absent(tail, key, query, or_false_right(String.eq(head, query), Inv.member(tail, query), absent), different))

law append_fresh_unique:
  for xs: List<&2, String>
  for +key: String
  for +unique: {Inv.unique(xs) == True{} : Bool}
  for +absent: {Inv.member(xs, key) == False{} : Bool}
  {Inv.unique(List.append(&2, String, xs, Con{key, Nil{}})) == True{} : Bool}
def append_fresh_unique(xs, key, unique, absent):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      keep_unique(head, List.append(&2, String, tail, Con{key, Nil{}}), False{}, append_absent(tail, key, head, not_true(Inv.member(tail, head), R.and_left(Bool.not(Inv.member(tail, head)), Inv.unique(tail), unique)), unequal_reverse(head, key, or_false_left(String.eq(head, key), Inv.member(tail, key), absent))), append_fresh_unique(tail, key, R.and_right(Bool.not(Inv.member(tail, head)), Inv.unique(tail), unique), or_false_right(String.eq(head, key), Inv.member(tail, key), absent)))

law move_preserves_unique:
  for +xs: List<&2, String>
  for +key: String
  for unique: {Inv.unique(xs) == True{} : Bool}
  {Inv.unique(List.append(&2, String, C.without(xs, key), Con{key, Nil{}})) == True{} : Bool}
def move_preserves_unique(xs, key, unique):
  append_fresh_unique(C.without(xs, key), key, filtering_preserves_unique(xs, key, unique), filtering_removes_target(xs, key))

law touch_preserves_unique:
  for +xs: List<&2, String>
  for +key: String
  for touch: Bool
  for unique: {Inv.unique(xs) == True{} : Bool}
  {Inv.unique(C.touch_order(xs, key, touch)) == True{} : Bool}
def touch_preserves_unique(xs, key, touch, unique):
  match touch:
    case False{}: unique
    case True{}: move_preserves_unique(xs, key, unique)

law store_preserves_unique_recency:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.LruEvent<K, V>>
  for unique: {unique_recency(K, V, c) == True{} : Bool}
  {unique_recency(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}
def store_preserves_unique_recency(K, V, c, code, key, value, deadline, flag, events, unique):
  C.State{cap, table, order, life, counts, cb} = c
  T.Counts{i, e, r, h, misses} = counts
  move_preserves_unique(order, code, unique)
