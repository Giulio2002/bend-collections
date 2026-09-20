import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_key_lookup.bend as M
import ./map_key_membership.bend as Keys
import ./map_insert.bend as I
import ./refinement.bend as F
import ./cache_populated.bend as Pop
import ./cache_order.bend as O
import ./recency_capacity.bend as B
import ./recency_bounds.bend as Bounds

def order_in_keys(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))

def available(-K: Data, -V: Data, c: C.Cache<K, V>, code: String) -> Type:
  Sigma<&2, &1, T.Entry<K, V>, entry => {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}>

law bridge:
  for -K: Data
  for -V: Data
  for +cap: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +order: List<&2, String>
  for +life: T.Int64
  for +counts: T.Metrics
  for +cb: Bool
  for +code: String
  for w: Sigma<&2, &1, T.Entry<K, V>, entry => {I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}>
  available(K, V, C.State{cap, table, order, life, counts, cb}, code)
def bridge(K, V, cap, table, order, life, counts, cb, code, w):
  (+entry, found) = w
  (entry, Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), Some{entry}, F.lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), found))

law ordered_lookup:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {order_in_keys(K, V, c) == True{} : Bool}
  for member: {O.ordered(K, V, c, code) == True{} : Bool}
  available(K, V, c, code)
def ordered_lookup(K, V, c, code, valid, populated, included, member):
  match c:
    case C.State{cap, +table, +order, life, counts, cb}:
      bridge(K, V, cap, table, order, life, counts, cb, code, M.key_lookup(T.Entry<K, V>, table, code, valid, populated, Keys.included_member(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code, included, member)))

law head_member:
  for +code: String
  for rest: List<&2, String>
  {Inv.member(Con{code, rest}, code) == True{} : Bool}
def head_member(code, rest):
  %Equal.sym(Bool, String.eq(code, code), True{}, Keys.eq_true(code, code, {==})) : {_ || Inv.member(rest, code) == True{} : Bool}
  {==}

law detach_frees_slot:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for member: {O.ordered(K, V, c, code) == True{} : Bool}
  for w: available(K, V, c, code)
  {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.detach(K, V, c, code))), C.len(K, V, c)) == True{} : Bool}
def detach_frees_slot(K, V, c, code, member, w):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  (+entry, found) = w
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.State{cap, table, order, life, counts, cb}, code), Some{entry}, found) : {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.detach_found(K, V, C.State{cap, table, order, life, counts, cb}, code, _))), List.length(&2, String, order)) == True{} : Bool}
  B.present_frees_slot(order, code, member)

# No successful lookup is assumed: it follows from the three input storage
# components. The conclusion concerns the actual facade-used protocol phase.
law oldest_frees_slot:
  for -K: Data
  for -V: Data
  for +cap: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +code: String
  for +rest: List<&2, String>
  for +life: T.Int64
  for +counts: T.Metrics
  for +cb: Bool
  for valid: {F.storage_critbit(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}) == True{} : Bool}
  for included: {order_in_keys(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}) == True{} : Bool}
  {Nat.is_le(1n+C.len(K, V, C.step_cache(K, V, P.detach_oldest(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}))), 1n+List.length(&2, String, rest)) == True{} : Bool}
def oldest_frees_slot(K, V, cap, table, code, rest, life, counts, cb, valid, populated, included):
  detach_frees_slot(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}, code, head_member(code, rest), ordered_lookup(K, V, C.State{cap, table, Con{code, rest}, life, counts, cb}, code, valid, populated, included, head_member(code, rest)))
