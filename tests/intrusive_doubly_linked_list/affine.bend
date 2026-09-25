import Base
import ./fixture.bend as F
import ../../src/containers/intrusive_doubly_linked_list.bend as L
import ../../src/containers/types/intrusive_doubly_linked_list.bend as E

# Fold an affine array accumulator through an affine application world.
# No duplication capability is available for either of the two arrays.
def add_done(s: F.World, v: U32, r: Array<U32> & U32) -> F.World & Array<U32>:
  (acc, old) = r
  (s, Array.set(U32, acc, 0, (old + v : U32)))

def add(s: F.World, c: Unit, acc: Array<U32>, v: U32) -> F.World & Array<U32>:
  add_done(s, v, Array.get(U32, acc, 0))

def output(r: Array<U32> & U32) -> U32:
  (acc, n) = r
  n

def finish(r: F.World & Result<&2, &1, E.Error, Array<U32>>) -> U32:
  match r:
    case Tuple{s, Fail{e}}: 0
    case Tuple{s, Done{acc}}: output(Array.get(U32, acc, 0))

def main() -> U32:
  s : F.World = F.prepend(F.prepend(F.prepend(F.new(), 0, 3), 0, 2), 0, 1)
  finish(L.fold_left(~F.World, ~U32, ~U32, ~Array<U32>, ~Unit, ~F.Reader, ~F.get_head, ~F.next, ~F.value, ~add, 3n, s, F.Room{0}, Unit{}, Array.new(U32, 0n, 0)))
