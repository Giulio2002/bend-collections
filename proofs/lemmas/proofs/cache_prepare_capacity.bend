import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./cache_oldest_available.bend as O
import ./cache_populated.bend as Pop
import ./refinement.bend as F
import ./recency_bounds.bend as B
import ./map_routing.bend as R

law zero_le:
  for n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}
def zero_le(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

law unequal_has_room:
  for a: Nat
  for b: Nat
  for bound: {Nat.is_le(a, b) == True{} : Bool}
  for unequal: {Nat.is_eq(a, b) == False{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}
def unequal_has_room(a, b, bound, unequal):
  match a b:
    case 0n 0n: Empty.absurd({False{} == True{} : Bool}, R.false_true(Equal.sym(Bool, True{}, False{}, unequal)))
    case 0n 1n+q: zero_le(q)
    case 1n+p 0n: Empty.absurd({False{} == True{} : Bool}, R.false_true(bound))
    case 1n+p 1n+q: unequal_has_room(p, q, bound, unequal)

# A full cache of positive capacity cannot have empty order. Availability of
# its oldest lookup is derived, so detach cannot silently take its miss branch.
law full_detach_room:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for full: {Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c))), C.capacity(K, V, c)) == True{} : Bool}
def full_detach_room(K, V, c, positive, bound, full, valid, populated, included):
  match c:
    case C.State{cap, +table, order, +life, +counts, +cb}:
      match cap order:
        case 0n xs:
          Empty.absurd({Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.detach_oldest(K, V, C.State{0n, table, xs, life, counts, cb}))), 0n) == True{} : Bool}, R.false_true(positive))
        case 1n++n Nil{}:
          Empty.absurd({Nat.is_le(1n, 1n+n) == True{} : Bool}, R.false_true(full))
        case 1n++n Con{+code, +rest}:
          B.le_transitive(1n+C.len(K, V, C.step_cache(K, V, P.detach_oldest(K, V, C.State{1n+n, table, Con{code, rest}, life, counts, cb}))), 1n+List.length(&2, String, rest), 1n+n, O.oldest_frees_slot(K, V, 1n+n, table, code, rest, life, counts, cb, valid, populated, included), bound)

law prepare_branch:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for full: Bool
  for decision: {Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)) == full : Bool}
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))), C.capacity(K, V, c)) == True{} : Bool}
def prepare_branch(K, V, c, full, decision, positive, bound, valid, populated, included):
  match full:
    case False{}: unequal_has_room(C.len(K, V, c), C.capacity(K, V, c), bound, decision)
    case True{}: full_detach_room(K, V, c, positive, bound, decision, valid, populated, included)

law absent_preparation_has_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for absent: {C.lookup(K, V, c, code) == None{} : Maybe<&2, T.Entry<K, V>>}
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))), C.capacity(K, V, c)) == True{} : Bool}
def absent_preparation_has_room(K, V, c, code, absent, positive, bound, valid, populated, included):
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, c, code), None{}, absent) : {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, _))), C.capacity(K, V, c)) == True{} : Bool}
  prepare_branch(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), {==}, positive, bound, valid, populated, included)

law not_full_has_room:
  for a: Nat
  for b: Nat
  for not_full: {Nat.is_ge(a, b) == False{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}
def not_full_has_room(a, b, not_full):
  match a b:
    case 0n 0n: Empty.absurd({False{} == True{} : Bool}, R.false_true(Equal.sym(Bool, True{}, False{}, not_full)))
    case 0n 1n+q: zero_le(q)
    case 1n+p 0n: Empty.absurd({False{} == True{} : Bool}, R.false_true(Equal.sym(Bool, True{}, False{}, not_full)))
    case 1n+p 1n+q: not_full_has_room(p, q, not_full)
