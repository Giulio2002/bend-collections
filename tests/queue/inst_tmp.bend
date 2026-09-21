import Base
import ../../src/queue.bend as Q
import ../../types/queue.bend as E

def main() -> Q.Queue<U32> & List<&2, E.Obs<U32>>:
  Q.run(~U32, [E.Enqueue{1}, E.Enqueue{2}, E.Dequeue{}, E.Enqueue{3}, E.Enqueue{4}, E.Peek{}, E.ToList{}, E.Length{}], Q.new(~U32))
