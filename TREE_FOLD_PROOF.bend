import Base
import ./src/balanced_search_tree.bend as M
import ./TREE_MAP_COMPONENT_PROOF.bend as C

# Public fold component laws. These do not prove arbitrary-tree fold refinement.
def visit(acc: U32, key: U32, value: U32) -> U32:
  U32.add(U32.mul(acc, 31), U32.add(U32.mul(key, 7), value))

def empty_fold(+acc: U32) -> {M.fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, M.new(~U32, ~U32, ~U32.cmp), acc) == (M.new(~U32, ~U32, ~U32.cmp), acc) : M.TreeMap<U32, U32, U32.cmp> & U32}:
  {==}

def singleton_fold(+value: U32, +acc: U32) -> {M.fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, C.singleton(0, value), acc) == (C.singleton(0, value), visit(acc, 0, value)) : M.TreeMap<U32, U32, U32.cmp> & U32}:
  {==}

def two_ordered(+a: U32, +b: U32, +acc: U32) -> {M.fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, C.two_entries(a, b), acc) == (C.two_entries(a, b), visit(visit(acc, 0, a), 1, b)) : M.TreeMap<U32, U32, U32.cmp> & U32}:
  {==}

def two_descending(+a: U32, +b: U32, +acc: U32) -> {M.view_fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, M.descending_map(~U32, ~U32, ~U32.cmp, C.two_entries(a, b)), acc) == (M.descending_map(~U32, ~U32, ~U32.cmp, C.two_entries(a, b)), visit(visit(acc, 1, b), 0, a)) : M.View<U32, U32, U32.cmp> & U32}:
  {==}

def empty_exclusive(+a: U32, +b: U32, +acc: U32) -> {M.view_fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, M.View{C.two_entries(a, b), M.Exclusive{0}, M.Exclusive{0}, False{}}, acc) == (M.View{C.two_entries(a, b), M.Exclusive{0}, M.Exclusive{0}, False{}}, acc) : M.View<U32, U32, U32.cmp> & U32}:
  {==}

def upper_excluded(+a: U32, +b: U32, +acc: U32) -> {M.view_fold(~U32, ~U32, ~U32.cmp, ~U32, ~visit, M.View{C.two_entries(a, b), M.Inclusive{0}, M.Exclusive{1}, False{}}, acc) == (M.View{C.two_entries(a, b), M.Inclusive{0}, M.Exclusive{1}, False{}}, visit(acc, 0, a)) : M.View<U32, U32, U32.cmp> & U32}:
  {==}
