import Base
import ./native_map.bend as Native
import ../src/cache.bend as C
import ../types/model.bend as T

# Executable representation predicates, not assumed correctness or a map oracle.
def member(xs: List<&2, String>, +key: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, tail}:
      String.eq(h, key) || member(tail, key)

def unique(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, +tail}:
      Bool.not(member(tail, h)) && unique(tail)

def included(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, tail}:
      member(ys, h) && included(tail, ys)

def bit_value(r: String & Bool) -> Bool:
  (key, bit) = r
  bit

def routed(-V: Data, m: Map<&2, V>, +position: Nat, +side: Bool) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{key, value}:
      Bool.not(Bool.xor(bit_value(Map.bit(key, position)), side))
    case MNode{p, lo, hi}:
      routed(V, lo, position, side) && routed(V, hi, position, side)

def nonempty(-V: Data, m: Map<&2, V>) -> Bool:
  match m:
    case MTip{}:
      False{}
    case other:
      True{}

def below(-V: Data, m: Map<&2, V>, parent: Nat) -> Bool:
  match m:
    case MNode{p, lo, hi}:
      Nat.is_lt(parent, p)
    case other:
      True{}

# Every pair of leaves below a node agrees on every bit strictly before
# its discriminator. Routing alone does not constrain these skipped bits.
def same_prefix(+a: String, +b: String, limit: Nat) -> Bool:
  match limit:
    case 0n:
      True{}
    case 1n+ +p:
      Bool.not(Bool.xor(bit_value(Map.bit(a, p)), bit_value(Map.bit(b, p)))) && same_prefix(a, b, p)

def prefix_against(-V: Data, +key: String, m: Map<&2, V>, +limit: Nat) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{other, value}:
      same_prefix(key, other, limit)
    case MNode{p, lo, hi}:
      prefix_against(V, key, lo, limit) && prefix_against(V, key, hi, limit)

def common_prefix(-V: Data, m: Map<&2, V>, +whole: Map<&2, V>, +limit: Nat) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{key, value}:
      prefix_against(V, key, whole, limit)
    case MNode{p, lo, hi}:
      common_prefix(V, lo, whole, limit) && common_prefix(V, hi, whole, limit)

def critbit(-V: Data, m: Map<&2, V>) -> Bool:
  match m:
    case MTip{}:
      True{}
    case MLeaf{key, value}:
      True{}
    case MNode{+p, +lo, +hi}:
      common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && nonempty(V, lo) && nonempty(V, hi) && below(V, lo, p) && below(V, hi, p) && routed(V, lo, p, False{}) && routed(V, hi, p, True{}) && critbit(V, lo) && critbit(V, hi)

def identities(~K: Data, ~encode: K -> String, -V: Data, entries: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> Bool:
  match entries:
    case Nil{}:
      True{}
    case Con{Tuple{code, None{}}, tail}:
      False{}
    case Con{Tuple{code, Some{T.Item{k, v, d}}}, tail}:
      String.eq(code, encode(k)) && identities(~K, ~encode, V, tail)

def representation(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{+cap, +table, +order, life, counts, cb} = c
  +keys = Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)
  Nat.is_gt(cap, 0n) && Nat.is_le(List.length(&2, String, order), cap) && unique(order) && unique(keys) && included(order, keys) && included(keys, order) && critbit(Maybe<&2, T.Entry<K, V>>, table) && identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table))

# Reachability is not yet characterized by a theorem. Defining the predicate is
# not evidence that actual operations preserve it; that induction remains open.

def string_identity(s: String) -> String:
  s

law initial_representation:
  for -V: Data
  for capacity_predecessor: Nat
  {representation(~String, ~string_identity, V, C.init(String, V, 1n+capacity_predecessor)) == True{} : Bool}
def initial_representation(V, capacity_predecessor):
  {==}

# A discriminator at 33 routes these children correctly, yet misses their first
# differing presence bit at zero. The strengthened predicate rejects that tree.
law skipped_prefix_rejected:
  {critbit(Nat, MNode{33n, MLeaf{"", 0n}, MLeaf{"aa", 1n}}) == False{} : Bool}
def skipped_prefix_rejected():
  {==}

# Lookup preserves even the strengthened discriminator/prefix predicate. The
# general storage preservation law does not need an assumed valid input tree.
law lookup_preserves_critbit:
  for -V: Data
  for +d: V
  for +m: Map<&2, V>
  for +key: String
  {critbit(V, Native.lookup_map(V, Map.get(V, d, m, key))) == critbit(V, m) : Bool}
def lookup_preserves_critbit(V, d, m, key):
  Equal.cong(Map<&2, V>, Bool, tree => critbit(V, tree), Native.lookup_map(V, Map.get(V, d, m, key)), m, Native.lookup_preserves_map(V, d, m, key))
