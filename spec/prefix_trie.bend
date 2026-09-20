import Base
import ./common.bend as SC
import ./balanced_search_tree.bend as M
import ../types/balanced_search_tree.bend as BE
import ../types/prefix_trie.bend as E

# Independent model: a finite map from String keys to values, as its list of
# entries in strictly increasing String.order (lexicographic on character
# codes) -- the ordered-map model of spec/balanced_search_tree.bend at
# (String, String.order). Enumeration is that order. Nothing here refers to
# tries, nodes or characters stored in nodes.

def ins(-V: Data, +k: String, +v: V, xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>>:
  M.ins(~String, ~String.order, V, k, v, xs)

def del(-V: Data, +k: String, xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>>:
  M.del(~String, ~String.order, V, k, xs)

def find(-V: Data, +k: String, xs: List<&2, BE.Entry<String, V>>) -> Maybe<&2, V>:
  M.find(~String, ~String.order, V, k, xs)

# p is a prefix of s (characters compared by code).
def is_prefix(p: String, s: String) -> Bool:
  match p s:
    case SNil{} _:
      True{}
    case SCon{a, p2} SNil{}:
      False{}
    case SCon{Chr{a}, p2} SCon{Chr{b}, s2}:
      Bool.and(Cmp.is_eq(U32.cmp(a, b)), is_prefix(p2, s2))

def keep_if(-V: Data, b: Bool, e: BE.Entry<String, V>, rest: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>>:
  match b:
    case True{}:
      Con{e, rest}
    case False{}:
      rest

# Entries whose key starts with p, in key order.
def with_prefix(-V: Data, +p: String, xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      keep_if(V, is_prefix(p, BE.key(String, V, e)), e, with_prefix(V, p, t))

# acc, or e when e is strictly longer than acc.
def longer_if(-V: Data, b: Bool, e: BE.Entry<String, V>, a: BE.Entry<String, V>) -> Maybe<&2, BE.Entry<String, V>>:
  match b:
    case True{}:
      Some{e}
    case False{}:
      Some{a}

def longer(-V: Data, +e: BE.Entry<String, V>, acc: Maybe<&2, BE.Entry<String, V>>) -> Maybe<&2, BE.Entry<String, V>>:
  match acc:
    case None{}:
      Some{e}
    case Some{+a}:
      longer_if(V, Nat.is_lt(String.length(BE.key(String, V, a)), String.length(BE.key(String, V, e))), e, a)

def pick(-V: Data, b: Bool, +e: BE.Entry<String, V>, acc: Maybe<&2, BE.Entry<String, V>>) -> Maybe<&2, BE.Entry<String, V>>:
  match b:
    case True{}:
      longer(V, e, acc)
    case False{}:
      acc

# The entry whose key is a prefix of s of maximal length (acc if none is
# longer than acc).
def best(-V: Data, xs: List<&2, BE.Entry<String, V>>, +s: String, acc: Maybe<&2, BE.Entry<String, V>>) -> Maybe<&2, BE.Entry<String, V>>:
  match xs:
    case Nil{}:
      acc
    case Con{+e, t}:
      best(V, t, s, pick(V, is_prefix(BE.key(String, V, e), s), e, acc))

def value(-V: Data, m: Maybe<&2, V>) -> Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{v}:
      Done{v}

def entry(-V: Data, m: Maybe<&2, BE.Entry<String, V>>) -> Result<&2, &2, E.Error, BE.Entry<String, V>>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{e}:
      Done{e}

def is_some(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def remove_at(-V: Data, m: Maybe<&2, V>, +k: String, +xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>> & E.Obs<V>:
  match m:
    case None{}:
      (xs, E.OVal{Fail{E.KeyNotFound{}}})
    case Some{v}:
      (del(V, k, xs), E.OVal{Done{v}})

def step(-V: Data, +xs: List<&2, BE.Entry<String, V>>, op: E.Op<V>) -> List<&2, BE.Entry<String, V>> & E.Obs<V>:
  match op:
    case E.Insert{+k, +v}:
      (ins(V, k, v, xs), E.OUnit{})
    case E.Lookup{+k}:
      (xs, E.OVal{value(V, find(V, k, xs))})
    case E.Remove{+k}:
      remove_at(V, find(V, k, xs), k, xs)
    case E.Contains{+k}:
      (xs, E.OBool{is_some(V, find(V, k, xs))})
    case E.PrefixEntries{+p}:
      (xs, E.OList{with_prefix(V, p, xs)})
    case E.LongestPrefix{+s}:
      (xs, E.OEntry{entry(V, best(V, xs, s, None{}))})

def cons_obs(-V: Data, o: E.Obs<V>, r: List<&2, BE.Entry<String, V>> & List<&2, E.Obs<V>>) -> List<&2, BE.Entry<String, V>> & List<&2, E.Obs<V>>:
  (m, os) = r
  (m, Con{o, os})

def run(-V: Data, ops: List<&2, E.Op<V>>, +xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>> & List<&2, E.Obs<V>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(V, Pair.snd(List<&2, BE.Entry<String, V>>, E.Obs<V>, step(V, xs, op)), run(V, rest, Pair.fst(List<&2, BE.Entry<String, V>>, E.Obs<V>, step(V, xs, op))))
