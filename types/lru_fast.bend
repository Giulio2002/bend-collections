import Base
import ./lru_model.bend as T

# Public operations of the indexed LRU cache (src/lru/fast.bend) and their
# observations, shared by the runtime and the independent specification
# (spec/lru_fast.bend). Times are the retained 64-bit `Int64`.

type Op<-V: Data> is Data:
  Len{}
  Capacity{}
  SetLifetime{ns: T.Int64}
  Metrics{}
  Add{key: String, value: V, now: T.Int64}
  Get{key: String, now: T.Int64}
  Peek{key: String, now: T.Int64}
  Contains{key: String, now: T.Int64}
  Remove{key: String}
  Purge{}
  Resize{capacity: U32}
  Keys{now: T.Int64}

type Obs<-V: Data> is Data:
  ONum{n: U32}
  OMetrics{m: T.Metrics}
  OFlag{b: Bool}
  OVal{v: Maybe<&2, V>}
  OResized{r: Result<&2, &2, String, U32>}
  OKeys{ks: List<&2, String>}
  OUnit{}
