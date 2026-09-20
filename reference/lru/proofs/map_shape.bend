import Base
import ./map_insert.bend as I
import ./native_map.bend as N

# Value erasure records the existing native tree's full discriminators and keys.
# It is a proof observation, never a lookup or runtime storage representation.
def skeleton(-V: Data, m: Map<&2, V>) -> Map<&2, Unit>:
  match m:
    case MTip{}:
      MTip{}
    case MLeaf{k, v}:
      MLeaf{k, Unit{}}
    case MNode{p, lo, hi}:
      MNode{p, skeleton(V, lo), skeleton(V, hi)}

# The native replacement helper creates a leaf on Tip. Its shape theorem must
# therefore be restricted to paths on which actual seek has found a leaf.
def certificate(-V: Data, m: Map<&2, V>, key: String, x: V, found: Maybe<&2, String>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{stored}:
      {skeleton(V, Map.put(&2, V, m, key, x)) == skeleton(V, m) : Map<&2, Unit>}

law lift_left:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for +x: V
  for found: Maybe<&2, String>
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  for cp: certificate(V, lo, key, x, found)
  certificate(V, MNode{p, lo, hi}, key, x, found)
def lift_left(V, lo, hi, p, key, x, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{stored}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {skeleton(V, Map.put.bit(&2, V, x, p, lo, hi, _)) == skeleton(V, MNode{p, lo, hi}) : Map<&2, Unit>}
      Equal.cong(Map<&2, Unit>, Map<&2, Unit>, child => MNode{p, child, skeleton(V, hi)}, skeleton(V, Map.put(&2, V, lo, key, x)), skeleton(V, lo), cp)

law lift_right:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for +x: V
  for found: Maybe<&2, String>
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  for cp: certificate(V, hi, key, x, found)
  certificate(V, MNode{p, lo, hi}, key, x, found)
def lift_right(V, lo, hi, p, key, x, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{stored}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {skeleton(V, Map.put.bit(&2, V, x, p, lo, hi, _)) == skeleton(V, MNode{p, lo, hi}) : Map<&2, Unit>}
      Equal.cong(Map<&2, Unit>, Map<&2, Unit>, child => MNode{p, skeleton(V, lo), child}, skeleton(V, Map.put(&2, V, hi, key, x)), skeleton(V, hi), cp)

law branch:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for x: V
  for bit: Bool
  for +e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: certificate(V, lo, key, x, I.seek_found(V, Map.seek(&2, V, lo, key)))
  for hp: certificate(V, hi, key, x, I.seek_found(V, Map.seek(&2, V, hi, key)))
  certificate(V, MNode{p, lo, hi}, key, x, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)))
def branch(V, lo, hi, p, key, x, bit, e, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, x, _)
      lift_left(V, lo, hi, p, key, x, I.seek_found(V, Map.seek(&2, V, lo, key)), e, lp)
    case True{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, p, key, e)) : certificate(V, MNode{p, lo, hi}, key, x, _)
      lift_right(V, lo, hi, p, key, x, I.seek_found(V, Map.seek(&2, V, hi, key)), e, hp)

law replacement_shape:
  for -V: Data
  for m: Map<&2, V>
  for +key: String
  for +x: V
  certificate(V, m, key, x, I.seek_found(V, Map.seek(&2, V, m, key)))
def replacement_shape(V, m, key, x):
  match m:
    case MTip{}:
      Unit{}
    case MLeaf{k, v}:
      {==}
    case MNode{+p, +lo, +hi}:
      branch(V, lo, hi, p, key, x, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), replacement_shape(V, lo, key, x), replacement_shape(V, hi, key, x))

# Unlike the helper certificate, this conclusion is a concrete structural
# equality. The premise is actual seek's result, not an assumed Map.set law.
law put_found_shape:
  for -V: Data
  for +m: Map<&2, V>
  for +key: String
  for +x: V
  for stored: String
  for found: {I.seek_found(V, Map.seek(&2, V, m, key)) == Some{stored} : Maybe<&2, String>}
  {skeleton(V, Map.put(&2, V, m, key, x)) == skeleton(V, m) : Map<&2, Unit>}
def put_found_shape(V, m, key, x, stored, found):
  %found : certificate(V, m, key, x, _)
  replacement_shape(V, m, key, x)

law keys_skeleton_go:
  for -V: Data
  for m: Map<&2, V>
  for +acc: List<&2, String>
  {Map.keys.go(&2, Unit, skeleton(V, m), acc) == Map.keys.go(&2, V, m, acc) : List<&2, String>}
def keys_skeleton_go(V, m, acc):
  match m:
    case MTip{}:
      {==}
    case MLeaf{k, v}:
      {==}
    case MNode{p, +lo, +hi}:
      Equal.trans(List<&2, String>, Map.keys.go(&2, Unit, skeleton(V, lo), Map.keys.go(&2, Unit, skeleton(V, hi), acc)), Map.keys.go(&2, Unit, skeleton(V, lo), Map.keys.go(&2, V, hi, acc)), Map.keys.go(&2, V, lo, Map.keys.go(&2, V, hi, acc)), Equal.cong(List<&2, String>, List<&2, String>, tail => Map.keys.go(&2, Unit, skeleton(V, lo), tail), Map.keys.go(&2, Unit, skeleton(V, hi), acc), Map.keys.go(&2, V, hi, acc), keys_skeleton_go(V, hi, acc)), keys_skeleton_go(V, lo, Map.keys.go(&2, V, hi, acc)))

law set_found_replaces:
  for -V: Data
  for +m: Map<&2, V>
  for +key: String
  for +x: V
  for found: {I.seek_found(V, Map.seek(&2, V, m, key)) == Some{key} : Maybe<&2, String>}
  {Map.set(&2, V, m, key, x) == Map.put(&2, V, m, key, x) : Map<&2, V>}
def set_found_replaces(V, m, key, x, found):
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, m, key), (m, key, I.seek_found(V, Map.seek(&2, V, m, key))), I.seek_shape(V, m, key)) : {Map.set.go(&2, V, x, _) == Map.put(&2, V, m, key, x) : Map<&2, V>}
  %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, m, key)), Some{key}, found) : {Map.set.go(&2, V, x, (m, key, _)) == Map.put(&2, V, m, key, x) : Map<&2, V>}
  %Equal.sym((String & String) & Cmp, String.cmp(key, key), ((key, key), EQ{}), N.string_compare_self(key)) : {Map.set.fin.go(&2, V, m, key, x, _) == Map.put(&2, V, m, key, x) : Map<&2, V>}
  {==}

law set_existing_shape:
  for -V: Data
  for +m: Map<&2, V>
  for +key: String
  for +x: V
  for +found: {I.seek_found(V, Map.seek(&2, V, m, key)) == Some{key} : Maybe<&2, String>}
  {skeleton(V, Map.set(&2, V, m, key, x)) == skeleton(V, m) : Map<&2, Unit>}
def set_existing_shape(V, m, key, x, found):
  Equal.trans(Map<&2, Unit>, skeleton(V, Map.set(&2, V, m, key, x)), skeleton(V, Map.put(&2, V, m, key, x)), skeleton(V, m), Equal.cong(Map<&2, V>, Map<&2, Unit>, tree => skeleton(V, tree), Map.set(&2, V, m, key, x), Map.put(&2, V, m, key, x), set_found_replaces(V, m, key, x, found)), put_found_shape(V, m, key, x, key, found))

law set_existing_keys:
  for -V: Data
  for +m: Map<&2, V>
  for +key: String
  for +x: V
  for found: {I.seek_found(V, Map.seek(&2, V, m, key)) == Some{key} : Maybe<&2, String>}
  {Map.keys(&2, V, Map.set(&2, V, m, key, x)) == Map.keys(&2, V, m) : List<&2, String>}
def set_existing_keys(V, m, key, x, found):
  %keys_skeleton_go(V, Map.set(&2, V, m, key, x), Nil{}) : {_ == Map.keys(&2, V, m) : List<&2, String>}
  %Equal.sym(Map<&2, Unit>, skeleton(V, Map.set(&2, V, m, key, x)), skeleton(V, m), set_existing_shape(V, m, key, x, found)) : {Map.keys(&2, Unit, _) == Map.keys(&2, V, m) : List<&2, String>}
  keys_skeleton_go(V, m, Nil{})
