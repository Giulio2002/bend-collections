import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_populated.bend as Pop
import ./map_delete_membership.bend as D
import ./map_key_membership.bend as Keys
import ./recency_membership.bend as Recency
import ./cache_oldest_available.bend as Oldest
import ./cache_order.bend as Order
import ./cache_populated.bend as Packed
import ./refinement.bend as F
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And

law included_cons:
  for xs: List<&2, String>
  for +head: String
  for +ys: List<&2, String>
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  {Inv.included(xs, Con{head, ys}) == True{} : Bool}
def included_cons(xs, head, ys, included):
  match xs:
    case Nil{}: {==}
    case Con{+key, +rest}:
      And.conjunction(Inv.member(Con{head, ys}, key), Inv.included(rest, Con{head, ys}), Keys.member_cons(head, ys, key, R.and_left(Inv.member(ys, key), Inv.included(rest, ys), included)), included_cons(rest, head, ys, R.and_right(Inv.member(ys, key), Inv.included(rest, ys), included)))

law included_self:
  for +xs: List<&2, String>
  {Inv.included(xs, xs) == True{} : Bool}
def included_self(xs):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(Con{head, tail}, head), Inv.included(tail, Con{head, tail}), Oldest.head_member(head, tail), included_cons(tail, head, tail, included_self(tail)))

law into_deleted:
  for -V: Data
  for xs: List<&2, String>
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for +populated: {Pop.populated(V, tree) == True{} : Bool}
  for +included: {Inv.included(xs, C.without(Map.keys(&2, Maybe<&2, V>, tree), removed)) == True{} : Bool}
  {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed))) == True{} : Bool}
def into_deleted(V, xs, tree, removed, valid, populated, included):
  match xs:
    case Nil{}: {==}
    case Con{+key, +rest}:
      And.conjunction(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), Inv.included(rest, Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed))), Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), key), True{}, D.filter_keys(V, tree, removed, key, valid, populated), R.and_left(Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), key), Inv.included(rest, C.without(Map.keys(&2, Maybe<&2, V>, tree), removed)), included)), into_deleted(V, rest, tree, removed, valid, populated, R.and_right(Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), key), Inv.included(rest, C.without(Map.keys(&2, Maybe<&2, V>, tree), removed)), included)))

law from_deleted:
  for -V: Data
  for xs: List<&2, String>
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +target: List<&2, String>
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for +populated: {Pop.populated(V, tree) == True{} : Bool}
  for +included: {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed))) == True{} : Bool}
  for +filtered: {Inv.included(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), target) == True{} : Bool}
  {Inv.included(xs, target) == True{} : Bool}
def from_deleted(V, xs, tree, removed, target, valid, populated, included, filtered):
  match xs:
    case Nil{}: {==}
    case Con{+key, +rest}:
      And.conjunction(Inv.member(target, key), Inv.included(rest, target), Keys.included_member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), target, key, filtered, Equal.trans(Bool, Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), key), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), True{}, Equal.sym(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), key), D.filter_keys(V, tree, removed, key, valid, populated)), R.and_left(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), Inv.included(rest, Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed))), included))), from_deleted(V, rest, tree, removed, target, valid, populated, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), key), Inv.included(rest, Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed))), included), filtered))

law detach_order_in_keys:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +removed: String
  for entry: T.Entry<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {Oldest.order_in_keys(K, V, c) == True{} : Bool}
  {Oldest.order_in_keys(K, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))) == True{} : Bool}
def detach_order_in_keys(K, V, c, removed, entry, valid, populated, included):
  C.State{cap, +tree, +order, life, counts, cb} = c
  into_deleted(T.Entry<K, V>, C.without(order, removed), tree, removed, valid, populated, Recency.filter_included_both(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, tree), removed, included))

law detach_keys_in_order:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +removed: String
  for entry: T.Entry<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {Order.keys_in_order(K, V, c) == True{} : Bool}
  {Order.keys_in_order(K, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))) == True{} : Bool}
def detach_keys_in_order(K, V, c, removed, entry, valid, populated, included):
  C.State{cap, +tree, +order, life, counts, cb} = c
  from_deleted(T.Entry<K, V>, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed)), tree, removed, C.without(order, removed), valid, populated, included_self(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.del(&2, Maybe<&2, T.Entry<K, V>>, tree, removed))), Recency.filter_included_both(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, tree), order, removed, included))

def membership(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Bool:
  Oldest.order_in_keys(K, V, c) && Order.keys_in_order(K, V, c)

law detach_present:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +removed: String
  for +entry: T.Entry<K, V>
  for +valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for +populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for +included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))) == True{} : Bool}
def detach_present(K, V, c, removed, entry, valid, populated, included):
  And.conjunction(Oldest.order_in_keys(K, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))), Order.keys_in_order(K, V, C.step_cache(K, V, P.detach_present(K, V, c, removed, entry))), detach_order_in_keys(K, V, c, removed, entry, valid, populated, R.and_left(Oldest.order_in_keys(K, V, c), Order.keys_in_order(K, V, c), included)), detach_keys_in_order(K, V, c, removed, entry, valid, populated, R.and_right(Oldest.order_in_keys(K, V, c), Order.keys_in_order(K, V, c), included)))

law detach_found:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for removed: String
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.detach_found(K, V, c, removed, found))) == True{} : Bool}
def detach_found(K, V, c, removed, found, valid, populated, included):
  match found:
    case None{}: included
    case Some{entry}: detach_present(K, V, c, removed, entry, valid, populated, included)

law detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +removed: String
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.detach(K, V, c, removed))) == True{} : Bool}
def detach(K, V, c, removed, valid, populated, included):
  detach_found(K, V, c, removed, C.lookup(K, V, c, removed), valid, populated, included)

law detach_first:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for order: List<&2, String>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.detach_first(K, V, c, order))) == True{} : Bool}
def detach_first(K, V, c, order, valid, populated, included):
  match order:
    case Nil{}: included
    case Con{code, rest}: detach(K, V, c, code, valid, populated, included)

law detach_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c))) == True{} : Bool}
def detach_oldest(K, V, c, valid, populated, included):
  C.State{cap, table, +order, life, counts, cb} = c
  detach_first(K, V, C.State{cap, table, order, life, counts, cb}, order, valid, populated, included)

law prepare_room:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for full: Bool
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))) == True{} : Bool}
def prepare_room(K, V, c, full, valid, populated, included):
  match full:
    case False{}: included
    case True{}: detach_oldest(K, V, c, valid, populated, included)

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, found))) == True{} : Bool}
def prepare_found(K, V, c, found, valid, populated, included):
  match found:
    case Some{entry}: included
    case None{}: prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), valid, populated, included)

law prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))) == True{} : Bool}
def prepare_add(K, V, c, code, valid, populated, included):
  prepare_found(K, V, c, C.lookup(K, V, c, code), valid, populated, included)

law core_remove_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for removed: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, C.remove_present(K, V, c, removed, evict, entry))) == True{} : Bool}
def core_remove_present(K, V, c, removed, evict, entry, valid, populated, included):
  C.State{cap, table, order, life, counts, cb} = c
  detach_present(K, V, C.State{cap, table, order, life, counts, cb}, removed, entry, valid, populated, included)

law core_remove_found:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for removed: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, C.remove_found(K, V, c, removed, evict, found))) == True{} : Bool}
def core_remove_found(K, V, c, removed, evict, found, valid, populated, included):
  match found:
    case None{}: included
    case Some{entry}: core_remove_present(K, V, c, removed, evict, entry, valid, populated, included)

law core_remove_encoded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +removed: String
  for evict: Bool
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, C.remove_encoded(K, V, c, removed, evict))) == True{} : Bool}
def core_remove_encoded(K, V, c, removed, evict, valid, populated, included):
  core_remove_found(K, V, c, removed, evict, C.lookup(K, V, c, removed), valid, populated, included)

law core_oldest_remove:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for order: List<&2, String>
  for evict: Bool
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, C.oldest_remove(K, V, c, order, evict))) == True{} : Bool}
def core_oldest_remove(K, V, c, order, evict, valid, populated, included):
  match order:
    case Nil{}: included
    case Con{code, rest}: core_remove_encoded(K, V, c, code, evict, valid, populated, included)

law core_remove_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for included: {membership(K, V, c) == True{} : Bool}
  {membership(K, V, C.step_cache(K, V, C.remove_oldest(K, V, c, evict))) == True{} : Bool}
def core_remove_oldest(K, V, c, evict, valid, populated, included):
  C.State{cap, table, +order, life, counts, cb} = c
  core_oldest_remove(K, V, C.State{cap, table, order, life, counts, cb}, order, evict, valid, populated, included)
