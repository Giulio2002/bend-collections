import Base
import ../../src/containers/intrusive_links.bend as K
import ../../src/containers/intrusive_doubly_linked_list.bend as IL
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Runtime smoke test of the ready-made link table: three entities linked at
# root 0, the middle one removed and prepended to root 1, both lists walked.
def ids(s: K.Links, +r: U32) -> K.Links & Result<&2, &1, E.Error, List<&1, U32>>:
  IL.to_list(~K.Links, ~U32, ~U32, ~U32, ~K.get_head, ~K.next, ~K.prev, ~(s => n => (s, n)), 16n, s, r)

def join(xs: List<&1, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      " " ++ U32.show(x) ++ join(rest)

def show(r: Result<&2, &1, E.Error, List<&1, U32>>) -> String:
  match r:
    case Done{xs}:
      join(xs)
    case Fail{e}:
      "error"

def report(r: K.Links & Result<&2, &1, E.Error, List<&1, U32>>, first: String) -> String:
  (s, b) = r
  first ++ " |" ++ show(b)

def both(r: K.Links & Result<&2, &1, E.Error, List<&1, U32>>) -> String:
  (s, a) = r
  report(ids(s, 1), show(a))

def main() -> IO(Unit):
  s0 = K.prepend(K.prepend(K.prepend(K.new(3n, 1n), 0, 3), 0, 2), 0, 1)
  s1 = K.prepend(K.remove(s0, 0, 2), 1, 2)
  IO.print(both(ids(s1, 0)))
