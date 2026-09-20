import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./cache_storage_preservation.bend as S
import ./cache_delete_membership.bend as D
import ./cache_order.bend as Order
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./map_key_membership.bend as Keys
import ./recency_move_inclusion.bend as Move
import ./refresh_lookup.bend as Lookup
import ./abstraction_recency.bend as Identity

# Preparation is committed before the host requests a clock sample. Its state
# therefore needs its own preservation theorem, including on clock failure.
law live_membership:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for +membership: {D.membership(K, V, c) == True{} : Bool}
  for ordered: {Order.ordered(K, V, c, code) == True{} : Bool}
  {D.membership(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, True{}))) == True{} : Bool}
def live_membership(K, V, c, code, entry, membership, ordered):
  C.State{cap, +table, +order, life, counts, cb} = c
  And.conjunction(Inv.included(Move.moved(order, code), Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), Move.moved(order, code)),
    Move.forward(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code,
      R.and_left(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), membership),
      Keys.included_member(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code, R.and_left(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), membership), ordered)),
    Move.backward(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order, code, R.and_right(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), membership)))

law live:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for +invariant: {S.storage(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {S.storage(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, True{}))) == True{} : Bool}
def live(K, V, c, code, entry, invariant, found):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  S.pack(K, V, C.step_cache(K, V, C.read_live(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, True{})),
    S.valid(K, V, C.State{cap, table, order, life, counts, cb}, invariant),
    S.populated(K, V, C.State{cap, table, order, life, counts, cb}, invariant),
    live_membership(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, S.membership(K, V, C.State{cap, table, order, life, counts, cb}, invariant),
      Order.lookup_is_ordered(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, R.and_right(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), S.membership(K, V, C.State{cap, table, order, life, counts, cb}, invariant)), found)))

law miss:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  {S.storage(K, V, P.finish_miss(K, V, c, True{})) == S.storage(K, V, c) : Bool}
def miss(K, V, c):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for result: Maybe<&2, T.Entry<K, V>>
  for decision: {C.lookup(K, V, c, code) == result : Maybe<&2, T.Entry<K, V>>}
  for invariant: {S.storage(K, V, c) == True{} : Bool}
  {S.storage(K, V, C.step_cache(K, V, P.refresh_prepare_found(K, V, c, code, result))) == True{} : Bool}
def found(K, V, c, code, result, decision, invariant):
  match result:
    case None{}: Equal.trans(Bool, S.storage(K, V, P.finish_miss(K, V, c, True{})), S.storage(K, V, c), True{}, miss(K, V, c), invariant)
    case Some{entry}: live(K, V, c, code, entry, invariant, decision)

law prepare:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for invariant: {S.storage(K, V, c) == True{} : Bool}
  {S.storage(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code))) == True{} : Bool}
def prepare(K, V, c, code, invariant):
  found(K, V, c, code, C.lookup(K, V, c, code), {==}, invariant)

# The successful lookup premise of the final phase is discharged by the actual
# preparation output, rather than assumed about the intermediate cache.
law complete:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for lifetime: T.Int64
  for now: T.Int64
  for invariant: {S.storage(K, V, c) == True{} : Bool}
  for returned: {Lookup.item(K, V, P.refresh_prepare(K, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {S.storage(K, V, P.refresh_at(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, lifetime, now)) == True{} : Bool}
def complete(K, V, c, code, entry, lifetime, now, invariant, returned):
  S.refresh_at(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, lifetime, now, prepare(K, V, c, code, invariant), Lookup.successful_prepare(K, V, c, code, entry, returned))
