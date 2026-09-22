import Base

# Independent model: a map from String keys to values is an association
# list with at most one entry per key. Nothing here refers to buckets,
# hashing, probing or slots.

type Entry<-V: Data> is Data:
  E{key: String, val: V}

def chr_eq(a: Char, b: Char) -> Bool:
  match a b:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

def str_eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{h, t} SNil{}:
      False{}
    case SCon{x, s} SCon{y, t}:
      Bool.and(chr_eq(x, y), str_eq(s, t))

def lookup(~V: Data, m: List<&2, Entry<V>>, +k: String) -> Maybe<&2, V>:
  match m:
    case Nil{}:
      None{}
    case Con{E{+j, +v}, t}:
      Bool.pick(Maybe<&2, V>, str_eq(j, k), Some{v}, lookup(~V, t, k))

def is_some(~V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def has(~V: Data, m: List<&2, Entry<V>>, +k: String) -> Bool:
  is_some(~V, lookup(~V, m, k))

# Replace the entry of k in place, or add it at the end.
def set(~V: Data, m: List<&2, Entry<V>>, +k: String, +x: V) -> List<&2, Entry<V>>:
  match m:
    case Nil{}:
      Con{E{k, x}, Nil{}}
    case Con{E{+j, +v}, +t}:
      Bool.pick(List<&2, Entry<V>>, str_eq(j, k), Con{E{k, x}, t}, Con{E{j, v}, set(~V, t, k, x)})

def remove(~V: Data, m: List<&2, Entry<V>>, +k: String) -> List<&2, Entry<V>>:
  match m:
    case Nil{}:
      Nil{}
    case Con{E{+j, +v}, +t}:
      Bool.pick(List<&2, Entry<V>>, str_eq(j, k), t, Con{E{j, v}, remove(~V, t, k)})

def keys(~V: Data, m: List<&2, Entry<V>>) -> List<&2, String>:
  match m:
    case Nil{}:
      Nil{}
    case Con{E{j, v}, t}:
      Con{j, keys(~V, t)}

def size(~V: Data, m: List<&2, Entry<V>>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{e, t}:
      1n+size(~V, t)

def mem(+k: String, ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{j, t}:
      Bool.or(str_eq(j, k), mem(k, t))

def nodup(ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+j, +t}:
      Bool.and(Bool.not(mem(j, t)), nodup(t))

def get_m(~V: Data, dflt: V, m: Maybe<&2, V>) -> V:
  match m:
    case None{}:
      dflt
    case Some{v}:
      v

# the value of key, or dflt
def get(~V: Data, dflt: V, m: List<&2, Entry<V>>, +key: String) -> V:
  get_m(~V, dflt, lookup(~V, m, key))
