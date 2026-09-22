import Base
import ../../src/containers/dynamic_array.bend as A
import ../../src/containers/types/dynamic_array.bend as E

def call(r: A.DynArray<(U32 -> U32)> & Result<&2, &1, E.Error, (U32 -> U32)>) -> U32:
  match r:
    case Tuple{a, Done{f}}:
      f(7)
    case Tuple{a, Fail{e}}:
      0

def pop(r: A.DynArray<(U32 -> U32)> & Result<&1, &2, E.Rejected<(U32 -> U32)>, Unit>) -> U32:
  (a, result) = r
  call(A.pop_owned(~(U32 -> U32), a))

def replace(r: A.DynArray<(U32 -> U32)> & Result<&1, &2, E.Rejected<(U32 -> U32)>, Unit>) -> U32:
  (a, result) = r
  pop(A.set_owned(~(U32 -> U32), a, 0n, x => (x + 5 : U32)))

def main() -> U32:
  replace(A.push_owned(~(U32 -> U32), A.new_owned(~(U32 -> U32)), x => (x + 99 : U32)))
