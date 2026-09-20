import Base
import ../spec/common.bend as SC
import ../types/balanced_search_tree.bend as BE
import ../types/prefix_trie.bend as E

# Prefix trie from String keys to values of an erased type V.
# Representation: first-child/next-sibling tree. A TNode holds one character
# code c, the value stored for the key spelled by the path ending at it, the
# list of its children (down) and its next sibling. Sibling lists are kept in
# strictly increasing character-code order, so a preorder walk enumerates
# keys in String.order. The root carries the value of the empty key.
# Removal prunes nodes that no longer carry a value or children.
#
# Errors: lookup/remove of an absent key and longest_prefix with no matching
# key return Fail{KeyNotFound}; the state is unchanged.
# Cost (key length m, alphabet branching b, entries listed r with total key
# length R): insert/lookup/remove/contains O(m * b) (sibling lists are
# scanned linearly); longest_prefix O(m * b); prefix_entries
# O(m * b + nodes below the prefix + R).

type Trie<-V: Data> is Data:
  TNil{}
  TNode{c: U32, val: Maybe<&2, V>, down: Trie<V>, next: Trie<V>}

type PrefixTrie<-V: Data> is Data:
  PT{val: Maybe<&2, V>, kids: Trie<V>}

# cmp(x, character code of the first node of t).
def hc(-V: Data, +x: U32, t: Trie<V>) -> Cmp:
  match t:
    case TNil{}:
      EQ{}
    case TNode{c, val, down, next}:
      U32.cmp(x, c)

# A path spelling x·rest ending in v, followed by siblings `next`.
def chain(-V: Data, rest: String, +x: U32, v: V, next: Trie<V>) -> Trie<V>:
  match rest:
    case SNil{}:
      TNode{x, Some{v}, TNil{}, next}
    case SCon{Chr{y}, r}:
      TNode{x, None{}, chain(V, r, y, v, TNil{}), next}

# Store v at key x·rest in the sibling list t; a = hc(x, t).
def ins(-V: Data, t: Trie<V>, +x: U32, a: Cmp, +rest: String, v: V) -> Trie<V>:
  match t a rest:
    case TNil{} _ _:
      chain(V, rest, x, v, TNil{})
    case TNode{c, val, down, next} LT{} _:
      chain(V, rest, x, v, TNode{c, val, down, next})
    case TNode{c, val, down, +next} GT{} _:
      TNode{c, val, down, ins(V, next, x, hc(V, x, next), rest, v)}
    case TNode{c, val, +down, next} EQ{} SNil{}:
      TNode{c, Some{v}, down, next}
    case TNode{c, val, +down, next} EQ{} SCon{Chr{+y}, +r}:
      TNode{c, val, ins(V, down, y, hc(V, y, down), r, v), next}

def find(-V: Data, t: Trie<V>, +x: U32, a: Cmp, +rest: String) -> Maybe<&2, V>:
  match t a rest:
    case TNil{} _ _:
      None{}
    case TNode{c, val, down, next} LT{} _:
      None{}
    case TNode{c, val, down, +next} GT{} _:
      find(V, next, x, hc(V, x, next), rest)
    case TNode{c, val, +down, next} EQ{} SNil{}:
      val
    case TNode{c, val, +down, next} EQ{} SCon{Chr{+y}, +r}:
      find(V, down, y, hc(V, y, down), r)

# A node, or just its siblings when it carries neither value nor children.
def prune(-V: Data, +c: U32, val: Maybe<&2, V>, down: Trie<V>, next: Trie<V>) -> Trie<V>:
  match val down:
    case None{} TNil{}:
      next
    case None{} TNode{c2, v2, d2, n2}:
      TNode{c, None{}, TNode{c2, v2, d2, n2}, next}
    case Some{w} TNil{}:
      TNode{c, Some{w}, TNil{}, next}
    case Some{w} TNode{c2, v2, d2, n2}:
      TNode{c, Some{w}, TNode{c2, v2, d2, n2}, next}

def rem(-V: Data, t: Trie<V>, +x: U32, a: Cmp, +rest: String) -> Trie<V>:
  match t a rest:
    case TNil{} _ _:
      TNil{}
    case TNode{c, val, down, next} LT{} _:
      TNode{c, val, down, next}
    case TNode{c, val, down, +next} GT{} _:
      TNode{c, val, down, rem(V, next, x, hc(V, x, next), rest)}
    case TNode{c, val, +down, next} EQ{} SNil{}:
      prune(V, c, None{}, down, next)
    case TNode{c, val, +down, next} EQ{} SCon{Chr{+y}, +r}:
      prune(V, c, val, rem(V, down, y, hc(V, y, down), r), next)

def opt(-V: Data, k: String, m: Maybe<&2, V>) -> List<&2, BE.Entry<String, V>>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      Con{BE.Entry{k, v}, Nil{}}

# Prefix every key with the character c.
def mapc(-V: Data, +c: U32, xs: List<&2, BE.Entry<String, V>>) -> List<&2, BE.Entry<String, V>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{BE.Entry{k, v}, t}:
      Con{BE.Entry{SCon{Chr{c}, k}, v}, mapc(V, c, t)}

# Entries of a sibling list in key order (keys relative to the list's parent).
def ent(-V: Data, t: Trie<V>) -> List<&2, BE.Entry<String, V>>:
  match t:
    case TNil{}:
      Nil{}
    case TNode{+c, val, down, next}:
      SC.append(BE.Entry<String, V>, opt(V, SCon{Chr{c}, SNil{}}, val), SC.append(BE.Entry<String, V>, mapc(V, c, ent(V, down)), ent(V, next)))

def pe(-V: Data, t: Trie<V>, +x: U32, a: Cmp, +rest: String) -> List<&2, BE.Entry<String, V>>:
  match t a rest:
    case TNil{} _ _:
      Nil{}
    case TNode{c, val, down, next} LT{} _:
      Nil{}
    case TNode{c, val, down, +next} GT{} _:
      pe(V, next, x, hc(V, x, next), rest)
    case TNode{+c, val, +down, next} EQ{} SNil{}:
      mapc(V, c, SC.append(BE.Entry<String, V>, opt(V, SNil{}, val), ent(V, down)))
    case TNode{+c, val, +down, next} EQ{} SCon{Chr{+y}, +r}:
      mapc(V, c, pe(V, down, y, hc(V, y, down), r))

def here(-V: Data, m: Maybe<&2, V>) -> Maybe<&2, BE.Entry<String, V>>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{BE.Entry{SNil{}, v}}

def shift(-V: Data, +c: U32, m: Maybe<&2, BE.Entry<String, V>>) -> Maybe<&2, BE.Entry<String, V>>:
  match m:
    case None{}:
      None{}
    case Some{BE.Entry{k, v}}:
      Some{BE.Entry{SCon{Chr{c}, k}, v}}

def orM(-V: Data, m: Maybe<&2, BE.Entry<String, V>>, d: Maybe<&2, BE.Entry<String, V>>) -> Maybe<&2, BE.Entry<String, V>>:
  match m:
    case None{}:
      d
    case Some{e}:
      Some{e}

# Deepest stored key along x·rest (relative to the list's parent).
def lp(-V: Data, t: Trie<V>, +x: U32, a: Cmp, +rest: String) -> Maybe<&2, BE.Entry<String, V>>:
  match t a rest:
    case TNil{} _ _:
      None{}
    case TNode{c, val, down, next} LT{} _:
      None{}
    case TNode{c, val, down, +next} GT{} _:
      lp(V, next, x, hc(V, x, next), rest)
    case TNode{+c, val, +down, next} EQ{} SNil{}:
      shift(V, c, here(V, val))
    case TNode{+c, val, +down, next} EQ{} SCon{Chr{+y}, +r}:
      shift(V, c, orM(V, lp(V, down, y, hc(V, y, down), r), here(V, val)))

# ---- public API ----

def new(-V: Data) -> PrefixTrie<V>:
  PT{None{}, TNil{}}

def insert(-V: Data, s: PrefixTrie<V>, key: String, v: V) -> PrefixTrie<V>:
  match s key:
    case PT{val, kids} SNil{}:
      PT{Some{v}, kids}
    case PT{val, +kids} SCon{Chr{+x}, +r}:
      PT{val, ins(V, kids, x, hc(V, x, kids), r, v)}

def get(-V: Data, s: PrefixTrie<V>, key: String) -> Maybe<&2, V>:
  match s key:
    case PT{val, kids} SNil{}:
      val
    case PT{val, +kids} SCon{Chr{+x}, +r}:
      find(V, kids, x, hc(V, x, kids), r)

def result(-V: Data, m: Maybe<&2, V>) -> Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{v}:
      Done{v}

def lookup(-V: Data, s: PrefixTrie<V>, key: String) -> Result<&2, &2, E.Error, V>:
  result(V, get(V, s, key))

def present(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def contains(-V: Data, s: PrefixTrie<V>, key: String) -> Bool:
  present(V, get(V, s, key))

def delete(-V: Data, s: PrefixTrie<V>, key: String) -> PrefixTrie<V>:
  match s key:
    case PT{val, kids} SNil{}:
      PT{None{}, kids}
    case PT{val, +kids} SCon{Chr{+x}, +r}:
      PT{val, rem(V, kids, x, hc(V, x, kids), r)}

def remove_at(-V: Data, m: Maybe<&2, V>, +s: PrefixTrie<V>, +key: String) -> PrefixTrie<V> & Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      (s, Fail{E.KeyNotFound{}})
    case Some{v}:
      (delete(V, s, key), Done{v})

# Remove key, returning its value.
def remove(-V: Data, +s: PrefixTrie<V>, +key: String) -> PrefixTrie<V> & Result<&2, &2, E.Error, V>:
  remove_at(V, get(V, s, key), s, key)

# All entries whose key starts with p, in key order.
def prefix_entries(-V: Data, s: PrefixTrie<V>, p: String) -> List<&2, BE.Entry<String, V>>:
  match s p:
    case PT{val, kids} SNil{}:
      SC.append(BE.Entry<String, V>, opt(V, SNil{}, val), ent(V, kids))
    case PT{val, +kids} SCon{Chr{+x}, +r}:
      pe(V, kids, x, hc(V, x, kids), r)

def entry(-V: Data, m: Maybe<&2, BE.Entry<String, V>>) -> Result<&2, &2, E.Error, BE.Entry<String, V>>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{e}:
      Done{e}

# The stored key that is the longest prefix of text.
def longest_prefix(-V: Data, s: PrefixTrie<V>, text: String) -> Result<&2, &2, E.Error, BE.Entry<String, V>>:
  match s text:
    case PT{val, kids} SNil{}:
      entry(V, here(V, val))
    case PT{val, +kids} SCon{Chr{+x}, +r}:
      entry(V, orM(V, lp(V, kids, x, hc(V, x, kids), r), here(V, val)))

# ---- trace runner ----

def obs_val(-V: Data, r: PrefixTrie<V> & Result<&2, &2, E.Error, V>) -> PrefixTrie<V> & E.Obs<V>:
  (s, x) = r
  (s, E.OVal{x})

def step(-V: Data, +s: PrefixTrie<V>, op: E.Op<V>) -> PrefixTrie<V> & E.Obs<V>:
  match op:
    case E.Insert{k, v}:
      (insert(V, s, k, v), E.OUnit{})
    case E.Lookup{k}:
      (s, E.OVal{lookup(V, s, k)})
    case E.Remove{k}:
      obs_val(V, remove(V, s, k))
    case E.Contains{k}:
      (s, E.OBool{contains(V, s, k)})
    case E.PrefixEntries{p}:
      (s, E.OList{prefix_entries(V, s, p)})
    case E.LongestPrefix{t}:
      (s, E.OEntry{longest_prefix(V, s, t)})

def record(-V: Data, acc: List<&2, E.Obs<V>>, r: PrefixTrie<V> & E.Obs<V>) -> PrefixTrie<V> & List<&2, E.Obs<V>>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(-V: Data, op: E.Op<V>, st: PrefixTrie<V> & List<&2, E.Obs<V>>) -> PrefixTrie<V> & List<&2, E.Obs<V>>:
  (s, acc) = st
  record(V, acc, step(V, s, op))

def run_acc(-V: Data, ops: List<&2, E.Op<V>>, st: PrefixTrie<V> & List<&2, E.Obs<V>>) -> PrefixTrie<V> & List<&2, E.Obs<V>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(V, rest, step_acc(V, op, st))

def finish(-V: Data, st: PrefixTrie<V> & List<&2, E.Obs<V>>) -> PrefixTrie<V> & List<&2, E.Obs<V>>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs<V>, acc))

def run(-V: Data, ops: List<&2, E.Op<V>>, s: PrefixTrie<V>) -> PrefixTrie<V> & List<&2, E.Obs<V>>:
  finish(V, run_acc(V, ops, (s, Nil{})))
