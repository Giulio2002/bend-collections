import Base
import ../../lib/common.bend as C
import ../../../src/containers/types/balanced_search_tree.bend as E

# Independent model: a finite map as its list of entries in strictly
# increasing key order (w.r.t. the comparator ~cmp). Nothing here refers to
# trees, heights or rebalancing.

def ins_at(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, c: Cmp, +k: K, +v: V, +e: E.Entry<K, V>, t: List<&2, E.Entry<K, V>>, rest: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match c:
    case LT{}:
      Con{E.Entry{k, v}, Con{e, t}}
    case EQ{}:
      Con{E.Entry{k, v}, t}
    case GT{}:
      Con{e, rest}

# Map k to v: replace the entry with key k, or insert it in key order.
def ins(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, +v: V, xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match xs:
    case Nil{}:
      Con{E.Entry{k, v}, Nil{}}
    case Con{+e, +t}:
      ins_at(~K, ~cmp, V, cmp(k, E.key(K, V, e)), k, v, e, t, ins(~K, ~cmp, V, k, v, t))

def keep(c: Cmp) -> Bool:
  match c:
    case EQ{}:
      False{}
    case _:
      True{}

def keep_at(-K: Data, -V: Data, b: Bool, +e: E.Entry<K, V>, rest: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match b:
    case True{}:
      Con{e, rest}
    case False{}:
      rest

# Entries whose key is not k.
def del(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      keep_at(K, V, keep(cmp(k, E.key(K, V, e))), e, del(~K, ~cmp, V, k, t))

def find_at(-K: Data, -V: Data, c: Cmp, +e: E.Entry<K, V>, rest: Maybe<&2, V>) -> Maybe<&2, V>:
  match c e:
    case EQ{} E.Entry{k, v}:
      Some{v}
    case _ _:
      rest

# Value of the first entry with key k.
def find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, xs: List<&2, E.Entry<K, V>>) -> Maybe<&2, V>:
  match xs:
    case Nil{}:
      None{}
    case Con{+e, t}:
      find_at(K, V, cmp(k, E.key(K, V, e)), e, find(~K, ~cmp, V, k, t))

def lb_at(-K: Data, -V: Data, c: Cmp, +e: E.Entry<K, V>, rest: Maybe<&2, E.Entry<K, V>>) -> Maybe<&2, E.Entry<K, V>>:
  match c:
    case LT{}:
      rest
    case _:
      Some{e}

# First entry whose key is >= k.
def lower(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, xs: List<&2, E.Entry<K, V>>) -> Maybe<&2, E.Entry<K, V>>:
  match xs:
    case Nil{}:
      None{}
    case Con{+e, t}:
      lb_at(K, V, cmp(E.key(K, V, e), k), e, lower(~K, ~cmp, V, k, t))

def in_range(lo_key: Cmp, key_hi: Cmp) -> Bool:
  Bool.and(Bool.not(Cmp.is_gt(lo_key)), Cmp.is_lt(key_hi))

# Entries with lo <= key < hi, in order.
def range(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +lo: K, +hi: K, xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      keep_at(K, V, in_range(cmp(lo, E.key(K, V, e)), cmp(E.key(K, V, e), hi)), e, range(~K, ~cmp, V, lo, hi, t))

def value(-V: Data, m: Maybe<&2, V>) -> Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{v}:
      Done{v}

def entry(-K: Data, -V: Data, m: Maybe<&2, E.Entry<K, V>>, err: E.Error) -> Result<&2, &2, E.Error, E.Entry<K, V>>:
  match m:
    case None{}:
      Fail{err}
    case Some{e}:
      Done{e}

def is_some(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def remove_at(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, m: Maybe<&2, V>, +k: K, +xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>> & E.Obs<K, V>:
  match m:
    case None{}:
      (xs, E.OVal{Fail{E.KeyNotFound{}}})
    case Some{v}:
      (del(~K, ~cmp, V, k, xs), E.OVal{Done{v}})

def step(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, op: E.Op<K, V>) -> List<&2, E.Entry<K, V>> & E.Obs<K, V>:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(E.Entry<K, V>, xs)})
    case E.Insert{+k, +v}:
      (ins(~K, ~cmp, V, k, v, xs), E.OUnit{})
    case E.Remove{+k}:
      remove_at(~K, ~cmp, V, find(~K, ~cmp, V, k, xs), k, xs)
    case E.Lookup{+k}:
      (xs, E.OVal{value(V, find(~K, ~cmp, V, k, xs))})
    case E.Contains{+k}:
      (xs, E.OBool{is_some(V, find(~K, ~cmp, V, k, xs))})
    case E.Min{}:
      (xs, E.OEntry{entry(K, V, C.head(E.Entry<K, V>, xs), E.EmptyTree{})})
    case E.Max{}:
      (xs, E.OEntry{entry(K, V, C.last(E.Entry<K, V>, xs), E.EmptyTree{})})
    case E.LowerBound{+k}:
      (xs, E.OEntry{entry(K, V, lower(~K, ~cmp, V, k, xs), E.KeyNotFound{})})
    case E.Range{+lo, +hi}:
      (xs, E.OList{range(~K, ~cmp, V, lo, hi, xs)})
    case E.ToList{}:
      (xs, E.OList{xs})

def cons_obs(-K: Data, -V: Data, o: E.Obs<K, V>, r: List<&2, E.Entry<K, V>> & List<&2, E.Obs<K, V>>) -> List<&2, E.Entry<K, V>> & List<&2, E.Obs<K, V>>:
  (m, os) = r
  (m, Con{o, os})

def run(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, ops: List<&2, E.Op<K, V>>, +xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>> & List<&2, E.Obs<K, V>>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(K, V, Pair.snd(List<&2, E.Entry<K, V>>, E.Obs<K, V>, step(~K, ~cmp, V, xs, op)), run(~K, ~cmp, V, rest, Pair.fst(List<&2, E.Entry<K, V>>, E.Obs<K, V>, step(~K, ~cmp, V, xs, op))))
