import Base
import ../../src/balanced_search_tree.bend as M

def finish(r: M.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>) -> U32:
  match r:
    case Tuple{m, Some{x}}:
      x
    case Tuple{m, None{}}:
      0

def look(r: M.TreeMap<U32, U32, U32.cmp> & Result<&2, &2, M.Rejected<U32, U32>, Maybe<&2, U32>>) -> U32:
  (m, status) = r
  finish(M.get(~U32, ~U32, ~U32.cmp, m, 7))

def main() -> U32:
  look(M.put(~U32, ~U32, ~U32.cmp, M.new(~U32, ~U32, ~U32.cmp), 7, 42))
