import Base
import ./native_map.bend as N

# Projections of actual native results; no alternative lookup algorithm.
def value(-V: Data, result: Map<&2, V> & V) -> V:
  (tree, found) = result
  found

def lookup(-V: Data, d: V, m: Map<&2, V>, key: String) -> V:
  value(V, Map.get(V, d, m, key))

def route_bit(r: String & Bool) -> Bool:
  (key, bit) = r
  bit

law route_pair:
  for r: String & Bool
  {r == (N.routed_key(r), route_bit(r)) : String & Bool}
def route_pair(r):
  match r:
    case Tuple{key, bit}:
      {==}

law route_shape:
  for +key: String
  for +position: Nat
  {Map.bit(key, position) == (key, route_bit(Map.bit(key, position))) : String & Bool}
def route_shape(key, position):
  %N.bit_preserves_key(key, position) : {Map.bit(key, position) == (_, route_bit(Map.bit(key, position))) : String & Bool}
  route_pair(Map.bit(key, position))

law low_value:
  for -V: Data
  for p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & V
  {value(V, Map.lo(&2, V, V, p, hi, r)) == value(V, r) : V}
def low_value(V, p, hi, r):
  match r:
    case Tuple{tree, found}:
      {==}

law high_value:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & V
  {value(V, Map.hi(&2, V, V, p, lo, r)) == value(V, r) : V}
def high_value(V, p, lo, r):
  match r:
    case Tuple{tree, found}:
      {==}

law node_left:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  {lookup(V, d, MNode{p, lo, hi}, key) == lookup(V, d, lo, key) : V}
def node_left(V, d, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {value(V, Map.get.bit(V, d, lo, hi, p, _)) == lookup(V, d, lo, key) : V}
  low_value(V, p, hi, Map.get(V, d, lo, key))

law node_right:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  {lookup(V, d, MNode{p, lo, hi}, key) == lookup(V, d, hi, key) : V}
def node_right(V, d, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {value(V, Map.get.bit(V, d, lo, hi, p, _)) == lookup(V, d, hi, key) : V}
  high_value(V, p, lo, Map.get(V, d, hi, key))

law leaf_same:
  for -V: Data
  for d: V
  for key: String
  for x: V
  {lookup(V, d, MLeaf{key, x}, key) == x : V}
def leaf_same(V, d, key, x):
  Equal.cong(Map<&2, V> & V, V, r => value(V, r), Map.get(V, d, MLeaf{key, x}, key), (MLeaf{key, x}, x), N.singleton_get(V, d, key, x))

law splice_same_bit:
  for -V: Data
  for +d: V
  for +x: V
  for +rest: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  {lookup(V, d, Map.ins.splice.bit(&2, V, x, rest, p, (key, bit)), key) == x : V}
def splice_same_bit(V, d, x, rest, p, key, bit, e):
  match bit:
    case False{}:
      Equal.trans(V, lookup(V, d, MNode{p, MLeaf{key, x}, rest}, key), lookup(V, d, MLeaf{key, x}, key), x, node_left(V, d, MLeaf{key, x}, rest, p, key, e), leaf_same(V, d, key, x))
    case True{}:
      Equal.trans(V, lookup(V, d, MNode{p, rest, MLeaf{key, x}}, key), lookup(V, d, MLeaf{key, x}, key), x, node_right(V, d, rest, MLeaf{key, x}, p, key, e), leaf_same(V, d, key, x))

law splice_same:
  for -V: Data
  for d: V
  for x: V
  for rest: Map<&2, V>
  for +p: Nat
  for +key: String
  {lookup(V, d, Map.ins.splice(&2, V, p, key, x, rest), key) == x : V}
def splice_same(V, d, x, rest, p, key):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, route_bit(Map.bit(key, p))), route_shape(key, p)) : {lookup(V, d, Map.ins.splice.bit(&2, V, x, rest, p, _), key) == x : V}
  splice_same_bit(V, d, x, rest, p, key, route_bit(Map.bit(key, p)), route_shape(key, p))

law deep_same_bit:
  for -V: Data
  for +d: V
  for +x: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +q: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, q) == (key, bit) : String & Bool}
  for lp: {lookup(V, d, Map.ins(&2, V, lo, key, x, p), key) == x : V}
  for hp: {lookup(V, d, Map.ins(&2, V, hi, key, x, p), key) == x : V}
  {lookup(V, d, Map.ins.deep(&2, V, x, lo, hi, p, q, (key, bit)), key) == x : V}
def deep_same_bit(V, d, x, lo, hi, p, q, key, bit, e, lp, hp):
  match bit:
    case False{}:
      Equal.trans(V, lookup(V, d, MNode{q, Map.ins(&2, V, lo, key, x, p), hi}, key), lookup(V, d, Map.ins(&2, V, lo, key, x, p), key), x, node_left(V, d, Map.ins(&2, V, lo, key, x, p), hi, q, key, e), lp)
    case True{}:
      Equal.trans(V, lookup(V, d, MNode{q, lo, Map.ins(&2, V, hi, key, x, p)}, key), lookup(V, d, Map.ins(&2, V, hi, key, x, p), key), x, node_right(V, d, lo, Map.ins(&2, V, hi, key, x, p), q, key, e), hp)

law insertion_branch_same:
  for -V: Data
  for d: V
  for x: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for +q: Nat
  for +key: String
  for descend: Bool
  for lp: {lookup(V, d, Map.ins(&2, V, lo, key, x, p), key) == x : V}
  for hp: {lookup(V, d, Map.ins(&2, V, hi, key, x, p), key) == x : V}
  {lookup(V, d, Map.ins.if(&2, V, key, x, lo, hi, q, p, descend), key) == x : V}
def insertion_branch_same(V, d, x, lo, hi, p, q, key, descend, lp, hp):
  match descend:
    case False{}:
      splice_same(V, d, x, MNode{q, lo, hi}, p, key)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, q), (key, route_bit(Map.bit(key, q))), route_shape(key, q)) : {lookup(V, d, Map.ins.deep(&2, V, x, lo, hi, p, q, _), key) == x : V}
      deep_same_bit(V, d, x, lo, hi, p, q, key, route_bit(Map.bit(key, q)), route_shape(key, q), lp, hp)

# This actual native insertion law needs no well-formedness assumption: querying
# the new key follows the same bits used to choose its newly inserted leaf.
# Other-key preservation DOES require valid discriminator/difference properties.
law insertion_same:
  for -V: Data
  for +d: V
  for m: Map<&2, V>
  for +key: String
  for +x: V
  for +p: Nat
  {lookup(V, d, Map.ins(&2, V, m, key, x, p), key) == x : V}
def insertion_same(V, d, m, key, x, p):
  match m:
    case MTip{}:
      leaf_same(V, d, key, x)
    case MLeaf{k, v}:
      splice_same(V, d, x, MLeaf{k, v}, p, key)
    case MNode{+q, +lo, +hi}:
      insertion_branch_same(V, d, x, lo, hi, p, q, key, Nat.is_lt(q, p), insertion_same(V, d, lo, key, x, p), insertion_same(V, d, hi, key, x, p))

def seek_found(-V: Data, r: Map<&2, V> & String & Maybe<&2, String>) -> Maybe<&2, String>:
  (tree, key, found) = r
  found

law seek_low_found:
  for -V: Data
  for p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & String & Maybe<&2, String>
  {seek_found(V, Map.lo(&2, V, String & Maybe<&2, String>, p, hi, r)) == seek_found(V, r) : Maybe<&2, String>}
def seek_low_found(V, p, hi, r):
  match r:
    case Tuple{tree, Tuple{key, found}}:
      {==}

law seek_high_found:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & String & Maybe<&2, String>
  {seek_found(V, Map.hi(&2, V, String & Maybe<&2, String>, p, lo, r)) == seek_found(V, r) : Maybe<&2, String>}
def seek_high_found(V, p, lo, r):
  match r:
    case Tuple{tree, Tuple{key, found}}:
      {==}

law seek_left:
  for -V: Data
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  {seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)) == seek_found(V, Map.seek(&2, V, lo, key)) : Maybe<&2, String>}
def seek_left(V, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {seek_found(V, Map.seek.bit(&2, V, lo, hi, p, _)) == seek_found(V, Map.seek(&2, V, lo, key)) : Maybe<&2, String>}
  seek_low_found(V, p, hi, Map.seek(&2, V, lo, key))

law seek_right:
  for -V: Data
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  {seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)) == seek_found(V, Map.seek(&2, V, hi, key)) : Maybe<&2, String>}
def seek_right(V, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {seek_found(V, Map.seek.bit(&2, V, lo, hi, p, _)) == seek_found(V, Map.seek(&2, V, hi, key)) : Maybe<&2, String>}
  seek_high_found(V, p, lo, Map.seek(&2, V, hi, key))

law replace_left:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for x: V
  for +e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  {lookup(V, d, Map.put(&2, V, MNode{p, lo, hi}, key, x), key) == lookup(V, d, Map.put(&2, V, lo, key, x), key) : V}
def replace_left(V, d, lo, hi, p, key, x, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {lookup(V, d, Map.put.bit(&2, V, x, p, lo, hi, _), key) == lookup(V, d, Map.put(&2, V, lo, key, x), key) : V}
  node_left(V, d, Map.put(&2, V, lo, key, x), hi, p, key, e)

law replace_right:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for x: V
  for +e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  {lookup(V, d, Map.put(&2, V, MNode{p, lo, hi}, key, x), key) == lookup(V, d, Map.put(&2, V, hi, key, x), key) : V}
def replace_right(V, d, lo, hi, p, key, x, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {lookup(V, d, Map.put.bit(&2, V, x, p, lo, hi, _), key) == lookup(V, d, Map.put(&2, V, hi, key, x), key) : V}
  node_right(V, d, lo, Map.put(&2, V, hi, key, x), p, key, e)

def replacement_certificate(-V: Data, d: V, m: Map<&2, V>, key: String, x: V, found: Maybe<&2, String>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{stored}:
      @equal: {key == stored : String} -> {lookup(V, d, Map.put(&2, V, m, key, x), key) == x : V}

law certificate_left:
  for -V: Data
  for +d: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for +x: V
  for found: Maybe<&2, String>
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  for cp: replacement_certificate(V, d, lo, key, x, found)
  replacement_certificate(V, d, MNode{p, lo, hi}, key, x, found)
def certificate_left(V, d, lo, hi, p, key, x, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{stored}:
      equal => Equal.trans(V, lookup(V, d, Map.put(&2, V, MNode{p, lo, hi}, key, x), key), lookup(V, d, Map.put(&2, V, lo, key, x), key), x, replace_left(V, d, lo, hi, p, key, x, e), cp(equal))

law certificate_right:
  for -V: Data
  for +d: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for +x: V
  for found: Maybe<&2, String>
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  for cp: replacement_certificate(V, d, hi, key, x, found)
  replacement_certificate(V, d, MNode{p, lo, hi}, key, x, found)
def certificate_right(V, d, lo, hi, p, key, x, found, e, cp):
  match found:
    case None{}:
      Unit{}
    case Some{stored}:
      equal => Equal.trans(V, lookup(V, d, Map.put(&2, V, MNode{p, lo, hi}, key, x), key), lookup(V, d, Map.put(&2, V, hi, key, x), key), x, replace_right(V, d, lo, hi, p, key, x, e), cp(equal))

law certificate_branch:
  for -V: Data
  for d: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for x: V
  for bit: Bool
  for +e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: replacement_certificate(V, d, lo, key, x, seek_found(V, Map.seek(&2, V, lo, key)))
  for hp: replacement_certificate(V, d, hi, key, x, seek_found(V, Map.seek(&2, V, hi, key)))
  replacement_certificate(V, d, MNode{p, lo, hi}, key, x, seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)))
def certificate_branch(V, d, lo, hi, p, key, x, bit, e, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, String>, seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), seek_found(V, Map.seek(&2, V, lo, key)), seek_left(V, lo, hi, p, key, e)) : replacement_certificate(V, d, MNode{p, lo, hi}, key, x, _)
      certificate_left(V, d, lo, hi, p, key, x, seek_found(V, Map.seek(&2, V, lo, key)), e, lp)
    case True{}:
      %Equal.sym(Maybe<&2, String>, seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), seek_found(V, Map.seek(&2, V, hi, key)), seek_right(V, lo, hi, p, key, e)) : replacement_certificate(V, d, MNode{p, lo, hi}, key, x, _)
      certificate_right(V, d, lo, hi, p, key, x, seek_found(V, Map.seek(&2, V, hi, key)), e, hp)

law replacement_at_seek:
  for -V: Data
  for +d: V
  for m: Map<&2, V>
  for +key: String
  for +x: V
  replacement_certificate(V, d, m, key, x, seek_found(V, Map.seek(&2, V, m, key)))
def replacement_at_seek(V, d, m, key, x):
  match m:
    case MTip{}:
      Unit{}
    case MLeaf{stored, old}:
      equal =>
        %equal : {lookup(V, d, MLeaf{_, x}, key) == x : V}
        leaf_same(V, d, key, x)
    case MNode{+p, +lo, +hi}:
      certificate_branch(V, d, lo, hi, p, key, x, route_bit(Map.bit(key, p)), route_shape(key, p), replacement_at_seek(V, d, lo, key, x), replacement_at_seek(V, d, hi, key, x))

law seek_low_shape:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for key: String
  for r: Map<&2, V> & String & Maybe<&2, String>
  for e: {r == (lo, key, seek_found(V, r)) : Map<&2, V> & String & Maybe<&2, String>}
  {Map.lo(&2, V, String & Maybe<&2, String>, p, hi, r) == (MNode{p, lo, hi}, key, seek_found(V, Map.lo(&2, V, String & Maybe<&2, String>, p, hi, r))) : Map<&2, V> & String & Maybe<&2, String>}
def seek_low_shape(V, p, lo, hi, key, r, e):
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, r, (lo, key, seek_found(V, r)), e) : {Map.lo(&2, V, String & Maybe<&2, String>, p, hi, _) == (MNode{p, lo, hi}, key, seek_found(V, Map.lo(&2, V, String & Maybe<&2, String>, p, hi, _))) : Map<&2, V> & String & Maybe<&2, String>}
  {==}

law seek_high_shape:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for key: String
  for r: Map<&2, V> & String & Maybe<&2, String>
  for e: {r == (hi, key, seek_found(V, r)) : Map<&2, V> & String & Maybe<&2, String>}
  {Map.hi(&2, V, String & Maybe<&2, String>, p, lo, r) == (MNode{p, lo, hi}, key, seek_found(V, Map.hi(&2, V, String & Maybe<&2, String>, p, lo, r))) : Map<&2, V> & String & Maybe<&2, String>}
def seek_high_shape(V, p, lo, hi, key, r, e):
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, r, (hi, key, seek_found(V, r)), e) : {Map.hi(&2, V, String & Maybe<&2, String>, p, lo, _) == (MNode{p, lo, hi}, key, seek_found(V, Map.hi(&2, V, String & Maybe<&2, String>, p, lo, _))) : Map<&2, V> & String & Maybe<&2, String>}
  {==}

law seek_branch_shape:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for p: Nat
  for +key: String
  for +bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: {Map.seek(&2, V, lo, key) == (lo, key, seek_found(V, Map.seek(&2, V, lo, key))) : Map<&2, V> & String & Maybe<&2, String>}
  for hp: {Map.seek(&2, V, hi, key) == (hi, key, seek_found(V, Map.seek(&2, V, hi, key))) : Map<&2, V> & String & Maybe<&2, String>}
  {Map.seek(&2, V, MNode{p, lo, hi}, key) == (MNode{p, lo, hi}, key, seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))) : Map<&2, V> & String & Maybe<&2, String>}
def seek_branch_shape(V, lo, hi, p, key, bit, e, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {Map.seek.bit(&2, V, lo, hi, p, _) == (MNode{p, lo, hi}, key, seek_found(V, Map.seek.bit(&2, V, lo, hi, p, _))) : Map<&2, V> & String & Maybe<&2, String>}
      seek_low_shape(V, p, lo, hi, key, Map.seek(&2, V, lo, key), lp)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {Map.seek.bit(&2, V, lo, hi, p, _) == (MNode{p, lo, hi}, key, seek_found(V, Map.seek.bit(&2, V, lo, hi, p, _))) : Map<&2, V> & String & Maybe<&2, String>}
      seek_high_shape(V, p, lo, hi, key, Map.seek(&2, V, hi, key), hp)

law seek_shape:
  for -V: Data
  for m: Map<&2, V>
  for +key: String
  {Map.seek(&2, V, m, key) == (m, key, seek_found(V, Map.seek(&2, V, m, key))) : Map<&2, V> & String & Maybe<&2, String>}
def seek_shape(V, m, key):
  match m:
    case MTip{}:
      {==}
    case MLeaf{k, v}:
      {==}
    case MNode{+p, +lo, +hi}:
      seek_branch_shape(V, lo, hi, p, key, route_bit(Map.bit(key, p)), route_shape(key, p), seek_shape(V, lo, key), seek_shape(V, hi, key))

law set_comparison_case:
  for -V: Data
  for +d: V
  for m: Map<&2, V>
  for +key: String
  for +stored: String
  for x: V
  for c: Cmp
  for e: {N.comparison_tag(String, String.cmp(key, stored)) == c : Cmp}
  for cp: @equal: {key == stored : String} -> {lookup(V, d, Map.put(&2, V, m, key, x), key) == x : V}
  {lookup(V, d, Map.set.fin.go(&2, V, m, key, x, ((key, stored), c)), key) == x : V}
def set_comparison_case(V, d, m, key, stored, x, c, e, cp):
  match c:
    case LT{}:
      insertion_same(V, d, m, key, x, Map.diff(key, stored))
    case GT{}:
      insertion_same(V, d, m, key, x, Map.diff(key, stored))
    case EQ{}:
      cp(N.string_equal_from_comparison(key, stored, e))

law set_found_case:
  for -V: Data
  for d: V
  for m: Map<&2, V>
  for +key: String
  for +stored: String
  for x: V
  for cp: @equal: {key == stored : String} -> {lookup(V, d, Map.put(&2, V, m, key, x), key) == x : V}
  {lookup(V, d, Map.set.fin(&2, V, m, key, x, key, stored), key) == x : V}
def set_found_case(V, d, m, key, stored, x, cp):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {lookup(V, d, Map.set.fin.go(&2, V, m, key, x, _), key) == x : V}
  set_comparison_case(V, d, m, key, stored, x, N.comparison_tag(String, String.cmp(key, stored)), {==}, cp)

law set_seek_case:
  for -V: Data
  for d: V
  for m: Map<&2, V>
  for key: String
  for x: V
  for found: Maybe<&2, String>
  for cp: replacement_certificate(V, d, m, key, x, found)
  {lookup(V, d, Map.set.go(&2, V, x, (m, key, found)), key) == x : V}
def set_seek_case(V, d, m, key, x, found, cp):
  match found:
    case None{}:
      leaf_same(V, d, key, x)
    case Some{stored}:
      set_found_case(V, d, m, key, stored, x, cp)

# Public native Map update/lookup same-key law. All seek/routing/comparator
# premises are discharged above against Base; no valid-tree premise is needed
# for this particular property. Other-key preservation remains a separate law.
law set_same:
  for -V: Data
  for +d: V
  for +m: Map<&2, V>
  for +key: String
  for +x: V
  {lookup(V, d, Map.set(&2, V, m, key, x), key) == x : V}
def set_same(V, d, m, key, x):
  %Equal.sym(Map<&2, V> & String & Maybe<&2, String>, Map.seek(&2, V, m, key), (m, key, seek_found(V, Map.seek(&2, V, m, key))), seek_shape(V, m, key)) : {lookup(V, d, Map.set.go(&2, V, x, _), key) == x : V}
  set_seek_case(V, d, m, key, x, seek_found(V, Map.seek(&2, V, m, key)), replacement_at_seek(V, d, m, key, x))
