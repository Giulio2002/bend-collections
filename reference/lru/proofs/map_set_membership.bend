import Base
import ./invariants.bend as Inv
import ./map_populated.bend as Pop
import ./map_key_presence.bend as Presence
import ./map_insert.bend as I
import ./map_set_frame.bend as Frame
import ./map_set_critbit.bend as Valid
import ./recency_unique.bend as U

# Membership laws for actual native set, including insertion and replacement.
law other:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +query: String
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for +populated: {Pop.populated(V, tree) == True{} : Bool}
  for unequal: {String.eq(query, key) == False{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query) : Bool}
def other(V, tree, key, value, query, valid, populated, unequal):
  Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), query)), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Equal.sym(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), query)), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query), Presence.lookup_presence(V, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), query, Valid.preserves_critbit(Maybe<&2, V>, tree, key, Some{value}, valid), Pop.set_preserves_populated(V, tree, key, Some{value}, {==}, populated))), Equal.trans(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), query)), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, tree, query)), Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query), Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), query), I.lookup(Maybe<&2, V>, None{}, tree, query), Frame.other_lookup_unchanged(V, tree, key, Some{value}, query, unequal, valid)), Presence.lookup_presence(V, tree, query, valid, populated)))

law same:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), key) == True{} : Bool}
def same(V, tree, key, value, valid, populated):
  Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), key), Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), key)), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), key)), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), key), Presence.lookup_presence(V, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), key, Valid.preserves_critbit(Maybe<&2, V>, tree, key, Some{value}, valid), Pop.set_preserves_populated(V, tree, key, Some{value}, {==}, populated))), Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), I.lookup(Maybe<&2, V>, None{}, Map.set(&2, Maybe<&2, V>, tree, key, Some{value}), key), Some{value}, I.set_same(Maybe<&2, V>, None{}, tree, key, Some{value})))

law membership_branch:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +query: String
  for equal: Bool
  for decision: {String.eq(query, key) == equal : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query) == (equal || Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query)) : Bool}
def membership_branch(V, tree, key, value, query, equal, decision, valid, populated):
  match equal:
    case False{}: other(V, tree, key, value, query, valid, populated, decision)
    case True{}:
      %Equal.sym(String, query, key, U.equal_boolean(query, key, decision)) : {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), _) == True{} : Bool}
      same(V, tree, key, value, valid, populated)

# Exact pointwise union; no assumption about native enumeration order.
law membership:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +query: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query) == (String.eq(query, key) || Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query)) : Bool}
def membership(V, tree, key, value, query, valid, populated):
  membership_branch(V, tree, key, value, query, String.eq(query, key), {==}, valid, populated)

law existing_branch:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +query: String
  for equal: Bool
  for +decision: {String.eq(query, key) == equal : Bool}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  for present: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query) : Bool}
def existing_branch(V, tree, key, value, query, equal, decision, valid, populated, present):
  match equal:
    case False{}: other(V, tree, key, value, query, valid, populated, decision)
    case True{}:
      %Equal.sym(String, query, key, U.equal_boolean(query, key, decision)) : {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), _) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), _) : Bool}
      Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), key), True{}, Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key), same(V, tree, key, value, valid, populated), Equal.sym(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key), True{}, present))

law existing:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for +query: String
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  for present: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, tree, key, Some{value})), query) == Inv.member(Map.keys(&2, Maybe<&2, V>, tree), query) : Bool}
def existing(V, tree, key, value, query, valid, populated, present):
  existing_branch(V, tree, key, value, query, String.eq(query, key), {==}, valid, populated, present)
