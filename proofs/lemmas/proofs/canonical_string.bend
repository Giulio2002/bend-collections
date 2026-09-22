import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./canonical.bend as Can
import ./spec_lookup.bend as Lookup
import ./recency_unique.bend as Unique
import ./lookup_refinement.bend as L

# String instantiations of the canonical calculus. The checker specializes
# static (~) parameters per use, so these instances are what the PROOF closure
# checks for the built-in String equality (reflection and reflexivity are the
# checked recency_unique.equal_boolean and lookup_refinement.string_reflexive).

def lookup_agreement(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, related: E.states(~String, ~Lookup.string_same, V, a, b), +q: String) -> {S.find(~String, ~Lookup.string_same, V, Can.bindings(String, V, a), q) == S.find(~String, ~Lookup.string_same, V, Can.bindings(String, V, b), q) : Maybe<&2, T.Entry<String, V>>}:
  Can.lookup_agreement(~String, ~Lookup.string_same, ~Unique.equal_boolean, V, a, b, related, q)

def find_canonical(-V: Data, s: S.Model<String, V>, +q: String) -> {S.find(~String, ~Lookup.string_same, V, Can.bindings(String, V, s), q) == Can.canonical_find(~String, ~Lookup.string_same, V, E.canonical(~String, ~Lookup.string_same, V, s), q) : Maybe<&2, T.Entry<String, V>>}:
  Can.find_canonical(~String, ~Lookup.string_same, ~Unique.equal_boolean, V, s, q)

def entries_agreement(-V: Data, +a: S.Model<String, V>, +b: S.Model<String, V>, related: E.states(~String, ~Lookup.string_same, V, a, b)) -> {O.all_entries(~String, ~Lookup.string_same, V, a) == O.all_entries(~String, ~Lookup.string_same, V, b) : List<&2, T.Entry<String, V>>}:
  Can.entries_agreement(~String, ~Lookup.string_same, V, a, b, related)

def drop_transform(-V: Data, +cap: Nat, +b: List<&2, T.Entry<String, V>>, +o: List<&2, String>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: String) -> {E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, S.erase(~String, ~Lookup.string_same, V, b, key), S.unlist(~String, ~Lookup.string_same, o, key), l, m, f}) == Can.c_drop(~String, ~Lookup.string_same, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<String, V>}:
  Can.drop_transform(~String, ~Lookup.string_same, ~Unique.equal_boolean, V, cap, b, o, l, m, f, key)

def write_transform(-V: Data, +cap: Nat, +b: List<&2, T.Entry<String, V>>, +o: List<&2, String>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: String, +value: V, +deadline: T.Int64) -> {E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, b, key)}, Can.moved(~String, ~Lookup.string_same, o, key), l, m, f}) == Can.c_write(~String, ~Lookup.string_same, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<String, V>}:
  Can.write_transform(~String, ~Lookup.string_same, ~Unique.equal_boolean, ~L.string_reflexive, V, cap, b, o, l, m, f, key, value, deadline)

def move_transform(-V: Data, +cap: Nat, +b: List<&2, T.Entry<String, V>>, +o: List<&2, String>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: String) -> {E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, b, Can.moved(~String, ~Lookup.string_same, o, key), l, m, f}) == Can.c_move(~String, ~Lookup.string_same, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<String, V>}:
  Can.move_transform(~String, ~Lookup.string_same, ~Unique.equal_boolean, ~L.string_reflexive, V, cap, b, o, l, m, f, key)

def stray_unlist_erase(-V: Data, +o: List<&2, String>, b: List<&2, T.Entry<String, V>>, +key: String) -> {E.stray(~String, ~Lookup.string_same, V, S.unlist(~String, ~Lookup.string_same, o, key), S.erase(~String, ~Lookup.string_same, V, b, key)) == S.erase(~String, ~Lookup.string_same, V, E.stray(~String, ~Lookup.string_same, V, o, b), key) : List<&2, T.Entry<String, V>>}:
  Can.stray_unlist_erase(~String, ~Lookup.string_same, ~Unique.equal_boolean, V, o, b, key)

# The written/refreshed specification state has no stray binding when its
# predecessor has none.
def written_stray(-V: Data, +cap: Nat, +b: List<&2, T.Entry<String, V>>, +o: List<&2, String>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: String, +value: V, +deadline: T.Int64, none: {E.stray(~String, ~Lookup.string_same, V, o, b) == Nil{} : List<&2, T.Entry<String, V>>}) -> {E.stray(~String, ~Lookup.string_same, V, Can.moved(~String, ~Lookup.string_same, o, key), Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, b, key)}) == Nil{} : List<&2, T.Entry<String, V>>}:
  Equal.trans(List<&2, T.Entry<String, V>>, E.stray(~String, ~Lookup.string_same, V, Can.moved(~String, ~Lookup.string_same, o, key), Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, b, key)}), S.erase(~String, ~Lookup.string_same, V, E.stray(~String, ~Lookup.string_same, V, o, b), key), Nil{}, Equal.cong(E.Canonical<String, V>, List<&2, T.Entry<String, V>>, c => Can.stray_of(String, V, c), E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, Con{T.Item{key, value, deadline}, S.erase(~String, ~Lookup.string_same, V, b, key)}, Can.moved(~String, ~Lookup.string_same, o, key), l, m, f}), Can.c_write(~String, ~Lookup.string_same, V, E.canonical(~String, ~Lookup.string_same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline), write_transform(V, cap, b, o, l, m, f, key, value, deadline)), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, T.Entry<String, V>>, x => S.erase(~String, ~Lookup.string_same, V, x, key), E.stray(~String, ~Lookup.string_same, V, o, b), Nil{}, none))

def removed_stray(-V: Data, +o: List<&2, String>, +b: List<&2, T.Entry<String, V>>, +key: String, none: {E.stray(~String, ~Lookup.string_same, V, o, b) == Nil{} : List<&2, T.Entry<String, V>>}) -> {E.stray(~String, ~Lookup.string_same, V, S.unlist(~String, ~Lookup.string_same, o, key), S.erase(~String, ~Lookup.string_same, V, b, key)) == Nil{} : List<&2, T.Entry<String, V>>}:
  Equal.trans(List<&2, T.Entry<String, V>>, E.stray(~String, ~Lookup.string_same, V, S.unlist(~String, ~Lookup.string_same, o, key), S.erase(~String, ~Lookup.string_same, V, b, key)), S.erase(~String, ~Lookup.string_same, V, E.stray(~String, ~Lookup.string_same, V, o, b), key), Nil{}, stray_unlist_erase(V, o, b, key), Equal.cong(List<&2, T.Entry<String, V>>, List<&2, T.Entry<String, V>>, x => S.erase(~String, ~Lookup.string_same, V, x, key), E.stray(~String, ~Lookup.string_same, V, o, b), Nil{}, none))

def cons_equal(-A: Data, +x1: A, +x2: A, +l1: List<&2, A>, +l2: List<&2, A>, hx: {x1 == x2 : A}, hl: {l1 == l2 : List<&2, A>}) -> {Con{x1, l1} == Con{x2, l2} : List<&2, A>}:
  %Equal.sym(A, x1, x2, hx) : {Con{_, l1} == Con{x2, l2} : List<&2, A>}
  Equal.cong(List<&2, A>, List<&2, A>, zs => Con{x2, zs}, l1, l2, hl)

def symmetric_false(+a: String, +b: String, no: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  Can.symmetric_false(~String, ~Lookup.string_same, ~Unique.equal_boolean, ~L.string_reflexive, a, b, no)
