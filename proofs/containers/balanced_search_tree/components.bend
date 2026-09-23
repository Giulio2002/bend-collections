import Base
import ../../../src/containers/balanced_search_tree.bend as M
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as E

# These are checked component laws of the NEW indexed TreeMap, not a claim
# that the old recursive-tree proof establishes indexed rotations/refinement.
# Every theorem is explicitly instantiated, so no unchecked template body.

def empty_size() -> {M.size(~U32, ~U32, ~U32.cmp, M.new(~U32, ~U32, ~U32.cmp)) == (M.new(~U32, ~U32, ~U32.cmp), 0n) : M.TreeMap<U32, U32, U32.cmp> & Nat}:
  {==}

def empty_get(k: U32) -> {M.get(~U32, ~U32, ~U32.cmp, M.new(~U32, ~U32, ~U32.cmp), k) == (M.new(~U32, ~U32, ~U32.cmp), None{}) : M.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>}:
  {==}

def empty_remove(k: U32) -> {M.remove(~U32, ~U32, ~U32.cmp, M.new(~U32, ~U32, ~U32.cmp), k) == (M.new(~U32, ~U32, ~U32.cmp), None{}) : M.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>}:
  {==}

def singleton(+k: U32, v: U32) -> M.TreeMap<U32, U32, U32.cmp>:
  M.TM{1n, 1n, 1n, 1n, 0n, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{M.N{False{}, 0n, 0n, 0n, k}}}}, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{Some{v}}}}}

def put_empty(+k: U32, +v: U32) -> {M.put(~U32, ~U32, ~U32.cmp, M.new(~U32, ~U32, ~U32.cmp), k, v) == (singleton(k, v), Done{None{}}) : M.TreeMap<U32, U32, U32.cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>}:
  {==}

def zero_get(+v: U32) -> {M.get(~U32, ~U32, ~U32.cmp, singleton(0, v), 0) == (singleton(0, v), Some{v}) : M.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>}:
  {==}

def zero_replace(+old: U32, +v: U32) -> {M.put(~U32, ~U32, ~U32.cmp, singleton(0, old), 0, v) == (singleton(0, v), Done{Some{old}}) : M.TreeMap<U32, U32, U32.cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>}:
  {==}

def zero_remove(+v: U32) -> {M.remove(~U32, ~U32, ~U32.cmp, singleton(0, v), 0) == (M.TM{0n, 0n, 0n, 0n, 1n, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{M.Free{0n}}}}, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{None{}}}}}, Some{v}) : M.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>}:
  {==}

def reuse_first(+k: U32, +v: U32) -> {M.put(~U32, ~U32, ~U32.cmp, M.TM{0n, 0n, 0n, 0n, 1n, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{M.Free{0n}}}}, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{None{}}}}}, k, v) == (singleton(k, v), Done{None{}}) : M.TreeMap<U32, U32, U32.cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>}:
  {==}

def cursor_owns(m: M.TreeMap<U32, U32, U32.cmp>, next: Nat, current: Nat, lo: M.Bound<U32>, hi: M.Bound<U32>, forward: Bool) -> {M.iterator_finish(~U32, ~U32, ~U32.cmp, M.Cursor{m, next, current, lo, hi, forward}) == m : M.TreeMap<U32, U32, U32.cmp>}:
  {==}

def view_owns(m: M.TreeMap<U32, U32, U32.cmp>, lo: M.Bound<U32>, hi: M.Bound<U32>, descending: Bool) -> {M.view_finish(~U32, ~U32, ~U32.cmp, M.View{m, lo, hi, descending}) == m : M.TreeMap<U32, U32, U32.cmp>}:
  {==}

def set_requires_current(m: M.TreeMap<U32, U32, U32.cmp>, +next: Nat, +lo: M.Bound<U32>, +hi: M.Bound<U32>, +forward: Bool, v: U32) -> {M.iterator_set_value(~U32, ~U32, ~U32.cmp, M.Cursor{m, next, 0n, lo, hi, forward}, v) == (M.Cursor{m, next, 0n, lo, hi, forward}, Fail{M.NoCurrent{}}) : M.Cursor<U32, U32, U32.cmp> & Result<&2, &2, M.Error, U32>}:
  {==}

def rejected_view_put(m: M.TreeMap<U32, U32, U32.cmp>, +k: U32, +v: U32, +lo: M.Bound<U32>, +hi: M.Bound<U32>, +descending: Bool) -> {M.view_put_checked(~U32, ~U32, ~U32.cmp, m, k, v, lo, hi, descending, False{}) == (M.View{m, lo, hi, descending}, Fail{M.Rejected{M.OutOfRange{}, k, v}}) : M.View<U32, U32, U32.cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>}:
  {==}

def data_swap_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<&2, U32>>, i: Nat, v: U32) -> {D.swap_checked_at(~U32, l, d, c, n, a, i, v, False{}) == (D.DA{l, d, c, n, a}, Fail{E.IndexOutOfRange{}}) : D.DynArray<&2, U32> & Result<&2, &2, E.Error, U32>}:
  {==}

def data_swap_first(+old: U32, +v: U32) -> {D.swap_at(~U32, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{old}}}, 0n, v) == (D.DA{31n, 0n, 1n, 1n, ALeaf{Some{v}}}, Done{old}) : D.DynArray<&2, U32> & Result<&2, &2, E.Error, U32>}:
  {==}

# A valid total preorder whose keys are all comparator-equivalent. This law
# checks original-key retention for arbitrary different keys and payloads;
# it is still a singleton law, not an arbitrary-map refinement theorem.
def same_class(a: U32, b: U32) -> Cmp:
  EQ{}

def equivalent_singleton(+k: U32, v: U32) -> M.TreeMap<U32, U32, same_class>:
  M.TM{1n, 1n, 1n, 1n, 0n, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{M.N{False{}, 0n, 0n, 0n, k}}}}, D.DA{31n, 0n, 1n, 1n, ALeaf{Some{Some{v}}}}}

def equivalent_put_retains_key(+stored: U32, incoming: U32, +old: U32, +v: U32) -> {M.put(~U32, ~U32, ~same_class, equivalent_singleton(stored, old), incoming, v) == (equivalent_singleton(stored, v), Done{Some{old}}) : M.TreeMap<U32, U32, same_class> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>}:
  {==}

def two_entries(v0: U32, v1: U32) -> M.TreeMap<U32, U32, U32.cmp>:
  M.TM{2n, 1n, 1n, 2n, 0n,
    D.DA{31n, 1n, 2n, 2n, ANode{ALeaf{Some{M.N{False{}, 0n, 2n, 0n, 0}}}, ALeaf{Some{M.N{True{}, 0n, 0n, 1n, 1}}}}},
    D.DA{31n, 1n, 2n, 2n, ANode{ALeaf{Some{Some{v0}}}, ALeaf{Some{Some{v1}}}}}}

def next_after_remove(r: M.Cursor<U32, U32, U32.cmp> & Maybe<&2, U32>) -> Maybe<&2, M.Entry<U32, U32>>:
  (cursor, old) = r
  Pair.snd(M.Cursor<U32, U32, U32.cmp>, Maybe<&2, M.Entry<U32, U32>>, M.iterator_next(~U32, ~U32, ~U32.cmp, cursor))

def cursor_remove_preserves_next(v0: U32, +v1: U32) -> {next_after_remove(M.iterator_remove(~U32, ~U32, ~U32.cmp, M.Cursor{two_entries(v0, v1), 2n, 1n, M.Unbounded{}, M.Unbounded{}, True{}})) == Some{M.Entry{1, v1}} : Maybe<&2, M.Entry<U32, U32>>}:
  {==}
