import Base
import ./balanced_search_tree.bend as BE

# Neutral datatypes shared by src/prefix_trie.bend and spec/prefix_trie.bend.
# Entries are BE.Entry<String, V> (key, value) pairs.

type Error is Data:
  KeyNotFound{}

type Op<-V: Data> is Data:
  Insert{key: String, val: V}
  Lookup{key: String}
  Remove{key: String}
  Contains{key: String}
  PrefixEntries{prefix: String}
  LongestPrefix{text: String}

type Obs<-V: Data> is Data:
  OUnit{}
  OVal{result: Result<&2, &2, Error, V>}
  OBool{value: Bool}
  OList{entries: List<&2, BE.Entry<String, V>>}
  OEntry{result: Result<&2, &2, Error, BE.Entry<String, V>>}
