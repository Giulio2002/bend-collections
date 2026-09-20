import Base
import ../src/cache.bend as C
import ./invariants.bend as Inv
import ./map_populated.bend as Pop
import ./map_key_presence.bend as Presence
import ./map_key_membership.bend as Keys
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_delete_frame.bend as Frame
import ./map_delete_critbit.bend as Valid
import ./map_delete_populated.bend as Packed
import ./map_delete.bend as Delete
import ./recency_unique.bend as U
import ./recency_membership.bend as Recency

law distinct:
  for +a: String
  for +b: String
  for unequal: {String.eq(a, b) == False{} : Bool}
  for equal: {a == b : String}
  Empty
def distinct(a, b, unequal, equal):
  R.false_true(Equal.trans(Bool, False{}, String.eq(a, b), True{}, Equal.sym(Bool, String.eq(a, b), False{}, unequal), Keys.eq_true(a, b, equal)))

law other:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +query: String
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for +populated: {Pop.populated(V, tree) == True{} : Bool}
  for unequal: {String.eq(query, removed) == False{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query) : Bool}
def other(V, tree, removed, query, valid, populated, unequal):
  Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), query)), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Equal.sym(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), query)), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query), Presence.lookup_presence(V, Map.del(&2, Maybe<&2, V>, tree, removed), query, Valid.preserves_critbit(Maybe<&2, V>, tree, removed, valid), Packed.preserves_populated(V, tree, removed, populated))), Equal.trans(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), query)), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, query)), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), query), I.lookup(Maybe<&2, V>, None{}, tree, query), Frame.other_lookup_unchanged(V, tree, removed, query, R.critbit_certificate(Maybe<&2, V>, tree, valid), e => distinct(query, removed, unequal, e))), Presence.lookup_presence(V, tree, query, valid, populated)))

law same:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), removed) == False{} : Bool}
def same(V, tree, removed, valid, populated):
  Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), removed), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), removed)), False{}, Equal.sym(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), removed)), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), removed), Presence.lookup_presence(V, Map.del(&2, Maybe<&2, V>, tree, removed), removed, Valid.preserves_critbit(Maybe<&2, V>, tree, removed, valid), Packed.preserves_populated(V, tree, removed, populated))), Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, removed), removed), None{}, Delete.critbit_delete_same(V, tree, removed, valid)))

law filter_branch:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +query: String
  for equal: Bool
  for +decision: {String.eq(query, removed) == equal : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query) == Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), query) : Bool}
def filter_branch(V, tree, removed, query, equal, decision, valid, populated):
  match equal:
    case False{}:
      Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), query), other(V, tree, removed, query, valid, populated, decision), Equal.sym(Bool, Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), query), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Recency.filter_other(Map.keys(&2, Maybe<&2, V>, tree), removed, query, decision)))
    case True{}:
      %Equal.sym(String, query, removed, U.equal_boolean(query, removed, decision)) : {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), _) == Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), _) : Bool}
      Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), removed), False{}, Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), removed), same(V, tree, removed, valid, populated), Equal.sym(Bool, Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), removed), False{}, U.filtering_removes_target(Map.keys(&2, Maybe<&2, V>, tree), removed)))

law filter_keys:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +removed: String
  for +query: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.del(&2, Maybe<&2, V>, tree, removed)), query) == Inv.member(C.without(Map.keys(&2, Maybe<&2, V>, tree), removed), query) : Bool}
def filter_keys(V, tree, removed, query, valid, populated):
  filter_branch(V, tree, removed, query, String.eq(query, removed), {==}, valid, populated)
