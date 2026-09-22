import Base
import ../../src/containers/deque.bend as DQ
import ../../src/containers/types/deque.bend as E

def main() -> DQ.Deque<U32> & List<&2, E.Obs<U32>>:
  DQ.run(~U32, [E.PushBack{1}, E.PushBack{2}, E.PushFront{3}, E.PushFront{4}, E.PushBack{5}, E.ToList{}, E.PopFront{}, E.PopBack{}, E.PeekFront{}, E.PeekBack{}, E.Length{}, E.ToList{}], DQ.new(~U32))
