import Base

# Neutral datatypes shared by src/balanced_search_tree.bend and
# spec/balanced_search_tree.bend.

type Entry<-K: Data, -V: Data> is Data:
  Entry{key: K, val: V}

def key(-K: Data, -V: Data, e: Entry<K, V>) -> K:
  match e:
    case Entry{k, v}:
      k

def val(-K: Data, -V: Data, e: Entry<K, V>) -> V:
  match e:
    case Entry{k, v}:
      v

type Error is Data:
  KeyNotFound{}
  EmptyTree{}

type Op<-K: Data, -V: Data> is Data:
  Length{}
  Insert{key: K, val: V}
  Remove{key: K}
  Lookup{key: K}
  Contains{key: K}
  Min{}
  Max{}
  LowerBound{key: K}
  Range{lo: K, hi: K}
  ToList{}

type Obs<-K: Data, -V: Data> is Data:
  ONat{value: Nat}
  OUnit{}
  OBool{value: Bool}
  OVal{result: Result<&2, &2, Error, V>}
  OEntry{result: Result<&2, &2, Error, Entry<K, V>>}
  OList{entries: List<&2, Entry<K, V>>}
