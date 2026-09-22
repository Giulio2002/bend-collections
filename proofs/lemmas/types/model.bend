import Base

# Negative{n} denotes -(n+1), so zero has exactly one representation.
type Integer is Data:
  Positive{magnitude: Nat}
  Negative{predecessor: Nat}

type Int64 is Data:
  I64{bits: Word(64n)}

type Metrics is Data:
  Counts{inserts: Word(64n), evictions: Word(64n), removals: Word(64n), hits: Word(64n), misses: Word(64n)}

type Entry<-K: Data, -V: Data> is Data:
  Item{key: K, value: V, deadline: Int64}

type Event<-K: Data, -V: Data> is Data:
  Evicted{key: K, value: V}

def zero_metrics() -> Metrics:
  Counts{Word.zero(64n), Word.zero(64n), Word.zero(64n), Word.zero(64n), Word.zero(64n)}
