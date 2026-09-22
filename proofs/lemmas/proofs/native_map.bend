import Base

# These unfold installed Base algorithms; no map axioms or replacement map.
law empty_lookup:
  for -V: Data
  for d: V
  for k: String
  {Map.get(V, d, Map.new(&2, V), k) == (MTip{}, d) : Map<&2, V> & V}
def empty_lookup(V, d, k):
  {==}

law empty_set:
  for -V: Data
  for k: String
  for v: V
  {Map.set(&2, V, Map.new(&2, V), k, v) == MLeaf{k, v} : Map<&2, V>}
def empty_set(V, k, v):
  {==}

law empty_delete:
  for -V: Data
  for k: String
  {Map.del(&2, V, Map.new(&2, V), k) == MTip{} : Map<&2, V>}
def empty_delete(V, k):
  {==}

law empty_has:
  for -V: Data
  for k: String
  {Map.has(&2, V, Map.new(&2, V), k) == (MTip{}, False{}) : Map<&2, V> & Bool}
def empty_has(V, k):
  {==}

# Presence bits are the key distinction between zero characters and end of string.
law zero_character_presence:
  for tail: String
  {Map.bit.go(SCon{Chr{0}, tail}, 0n, 0n) == (SCon{Chr{0}, tail}, True{}) : String & Bool}
def zero_character_presence(tail):
  {==}

law empty_presence:
  {Map.bit.go(SNil{}, 0n, 0n) == (SNil{}, False{}) : String & Bool}
def empty_presence():
  {==}

law boolean_compare_self:
  for b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}
def boolean_compare_self(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law word_compare_self:
  for n: Nat
  for w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}
def word_compare_self(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Bool.cmp(b, b), EQ{},
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, word_compare_self(p, t)),
            boolean_compare_self(b))

law character_compare_self:
  for c: Char
  {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}
def character_compare_self(c):
  match c:
    case Chr{U32{w}}:
      %word_compare_self(32n, w) : {((Chr{U32{w}}, Chr{U32{w}}), Word.cmp(32n, w, w)) == ((Chr{U32{w}}, Chr{U32{w}}), _) : (Char & Char) & Cmp}
      {==}

law string_compare_self:
  for s: String
  {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}
def string_compare_self(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym((Char & Char) & Cmp, Char.cmp(h, h), ((h, h), EQ{}), character_compare_self(h)) : {String.cmp.fin(t, t, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      %Equal.sym((String & String) & Cmp, String.cmp(t, t), ((t, t), EQ{}), string_compare_self(t)) : {String.cmp.rec(h, h, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      {==}

law singleton_get:
  for -V: Data
  for d: V
  for k: String
  for v: V
  {Map.get(V, d, MLeaf{k, v}, k) == (MLeaf{k, v}, v) : Map<&2, V> & V}
def singleton_get(V, d, k, v):
  %Equal.sym((String & String) & Cmp, String.cmp(k, k), ((k, k), EQ{}), string_compare_self(k)) : {Map.get.leaf(V, d, v, _) == (MLeaf{k, v}, v) : Map<&2, V> & V}
  {==}

law singleton_update:
  for -V: Data
  for k: String
  for old: V
  for value: V
  {Map.set(&2, V, MLeaf{k, old}, k, value) == MLeaf{k, value} : Map<&2, V>}
def singleton_update(V, k, old, value):
  %Equal.sym((String & String) & Cmp, String.cmp(k, k), ((k, k), EQ{}), string_compare_self(k)) : {Map.set.fin.go(&2, V, MLeaf{k, old}, k, value, _) == MLeaf{k, value} : Map<&2, V>}
  {==}

law singleton_delete:
  for -V: Data
  for k: String
  for v: V
  {Map.del(&2, V, MLeaf{k, v}, k) == MTip{} : Map<&2, V>}
def singleton_delete(V, k, v):
  %Equal.sym((String & String) & Cmp, String.cmp(k, k), ((k, k), EQ{}), string_compare_self(k)) : {Map.del.fin(&2, V, Map.pop.leaf(&2, V, v, _)) == MTip{} : Map<&2, V>}
  {==}

# General routing foundation: actual Base bit traversal preserves the entire
# string, irrespective of the requested bit, character codes, or tree validity.
def routed_key(r: String & Bool) -> String:
  (key, bit) = r
  key

law recursive_bit_key:
  for c: Char
  for r: String & Bool
  {routed_key(Map.bit.go.rec(c, r)) == SCon{c, routed_key(r)} : String}
def recursive_bit_key(c, r):
  match r:
    case Tuple{key, bit}:
      {==}

law bit_go_preserves_key:
  for key: String
  for +character: Nat
  for +offset: Nat
  {routed_key(Map.bit.go(key, character, offset)) == key : String}
def bit_go_preserves_key(key, character, offset):
  match key character offset:
    case SNil{} ci off:
      {==}
    case SCon{Chr{x}, tail} 0n 0n:
      {==}
    case SCon{Chr{x}, tail} 0n 1n+off:
      {==}
    case SCon{Chr{x}, +tail} 1n+ci off:
      +c = {Chr{x} : Char}
      Equal.trans(String, routed_key(Map.bit.go.rec(c, Map.bit.go(tail, ci, off))),
        SCon{c, routed_key(Map.bit.go(tail, ci, off))}, SCon{c, tail},
        recursive_bit_key(c, Map.bit.go(tail, ci, off)),
        Equal.cong(String, String, t => SCon{c, t}, routed_key(Map.bit.go(tail, ci, off)), tail, bit_go_preserves_key(tail, ci, off)))

law bit_at_preserves_key:
  for key: String
  for coordinates: Nat & Nat
  {routed_key(Map.bit.at(key, coordinates)) == key : String}
def bit_at_preserves_key(key, coordinates):
  match coordinates:
    case Tuple{ci, off}:
      bit_go_preserves_key(key, ci, off)

law bit_preserves_key:
  for key: String
  for position: Nat
  {routed_key(Map.bit(key, position)) == key : String}
def bit_preserves_key(key, position):
  bit_at_preserves_key(key, Nat.divmod(position, 33n))

# A comparison certificate has content precisely in the EQ branch.
def comparison_identity(-A: Type, a: A, b: A, c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      {a == b : A}
    case GT{}:
      Unit

law word_comparison_step:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Cmp
  for x: Bool
  for y: Bool
  for proof: comparison_identity(Word(n), a, b, c)
  comparison_identity(Word(1n+n), WCon{x, a}, WCon{y, b}, Word.cmp.fin(x, y, c))
def word_comparison_step(n, a, b, c, x, y, proof):
  match c:
    case LT{}:
      Unit{}
    case GT{}:
      Unit{}
    case EQ{}:
      match x y:
        case False{} False{}:
          Equal.cong(Word(n), Word(1n+n), t => WCon{False{}, t}, a, b, proof)
        case True{} True{}:
          Equal.cong(Word(n), Word(1n+n), t => WCon{True{}, t}, a, b, proof)
        case False{} True{}:
          Unit{}
        case True{} False{}:
          Unit{}

law word_comparison_identity:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  comparison_identity(Word(n), a, b, Word.cmp(n, a, b))
def word_comparison_identity(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{x, +at} WCon{y, +bt}:
          word_comparison_step(p, at, bt, Word.cmp(p, at, bt), x, y, word_comparison_identity(p, at, bt))

law comparison_lift:
  for -A: Type
  for -B: Type
  for f: A -> B
  for a: A
  for b: A
  for c: Cmp
  for proof: comparison_identity(A, a, b, c)
  comparison_identity(B, f(a), f(b), c)
def comparison_lift(A, B, f, a, b, c, proof):
  match c:
    case LT{}:
      Unit{}
    case GT{}:
      Unit{}
    case EQ{}:
      Equal.cong(A, B, f, a, b, proof)

def comparison_result_identity(-A: Type, r: (A & A) & Cmp) -> Type:
  ((a, b), c) = r
  comparison_identity(A, a, b, c)

law character_comparison_identity:
  for a: Char
  for b: Char
  comparison_result_identity(Char, Char.cmp(a, b))
def character_comparison_identity(a, b):
  match a b:
    case Chr{U32{+x}} Chr{U32{+y}}:
      comparison_lift(Word(32n), Char, w => Chr{U32{w}}, x, y, Word.cmp(32n, x, y), word_comparison_identity(32n, x, y))

law string_comparison_rec_identity:
  for h: Char
  for r: (String & String) & Cmp
  for proof: comparison_result_identity(String, r)
  comparison_result_identity(String, String.cmp.rec(h, h, r))
def string_comparison_rec_identity(h, r, proof):
  match r:
    case Tuple{Tuple{a, b}, c}:
      comparison_lift(String, String, t => SCon{h, t}, a, b, c, proof)

law string_comparison_fin_identity:
  for t1: String
  for t2: String
  for hc: (Char & Char) & Cmp
  for hp: comparison_result_identity(Char, hc)
  for tp: comparison_result_identity(String, String.cmp(t1, t2))
  comparison_result_identity(String, String.cmp.fin(t1, t2, hc))
def string_comparison_fin_identity(t1, t2, hc, hp, tp):
  match hc:
    case Tuple{Tuple{h1, h2}, LT{}}:
      Unit{}
    case Tuple{Tuple{h1, h2}, GT{}}:
      Unit{}
    case Tuple{Tuple{h1, h2}, EQ{}}:
      %hp : comparison_result_identity(String, String.cmp.rec(h1, _, String.cmp(t1, t2)))
      string_comparison_rec_identity(h1, String.cmp(t1, t2), tp)

law string_comparison_identity:
  for a: String
  for b: String
  comparison_result_identity(String, String.cmp(a, b))
def string_comparison_identity(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Unit{}
    case SCon{h, t} SNil{}:
      Unit{}
    case SCon{+h1, +t1} SCon{+h2, +t2}:
      string_comparison_fin_identity(t1, t2, Char.cmp(h1, h2), character_comparison_identity(h1, h2), string_comparison_identity(t1, t2))

def comparison_tag(-A: Type, r: (A & A) & Cmp) -> Cmp:
  (pair, c) = r
  c

law string_comparison_shape_step:
  for h1: Char
  for h2: Char
  for t1: String
  for t2: String
  for c: Cmp
  for tp: {String.cmp(t1, t2) == ((t1, t2), comparison_tag(String, String.cmp(t1, t2))) : (String & String) & Cmp}
  {String.cmp.fin(t1, t2, ((h1, h2), c)) == ((SCon{h1, t1}, SCon{h2, t2}), comparison_tag(String, String.cmp.fin(t1, t2, ((h1, h2), c)))) : (String & String) & Cmp}
def string_comparison_shape_step(h1, h2, t1, t2, c, tp):
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      %Equal.sym((String & String) & Cmp, String.cmp(t1, t2), ((t1, t2), comparison_tag(String, String.cmp(t1, t2))), tp) : {String.cmp.rec(h1, h2, _) == ((SCon{h1, t1}, SCon{h2, t2}), comparison_tag(String, String.cmp.rec(h1, h2, _))) : (String & String) & Cmp}
      {==}

law string_comparison_shape:
  for a: String
  for b: String
  {String.cmp(a, b) == ((a, b), comparison_tag(String, String.cmp(a, b))) : (String & String) & Cmp}
def string_comparison_shape(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{U32{+x}}, +t1} SCon{Chr{U32{+y}}, +t2}:
      string_comparison_shape_step(Chr{U32{x}}, Chr{U32{y}}, t1, t2, Word.cmp(32n, x, y), string_comparison_shape(t1, t2))

law string_comparison_original_identity:
  for +a: String
  for +b: String
  comparison_identity(String, a, b, comparison_tag(String, String.cmp(a, b)))
def string_comparison_original_identity(a, b):
  %string_comparison_shape(a, b) : comparison_result_identity(String, _)
  string_comparison_identity(a, b)

law string_equal_from_comparison:
  for a: String
  for b: String
  for e: {comparison_tag(String, String.cmp(a, b)) == EQ{} : Cmp}
  {a == b : String}
def string_equal_from_comparison(a, b, e):
  %e : comparison_identity(String, a, b, _)
  string_comparison_original_identity(a, b)

law string_equal_comparison:
  for a: String
  for b: String
  for e: {a == b : String}
  {String.cmp(a, b) == ((a, b), EQ{}) : (String & String) & Cmp}
def string_equal_comparison(a, b, e):
  %e : {String.cmp(a, _) == ((a, _), EQ{}) : (String & String) & Cmp}
  string_compare_self(a)

# First-difference base and common-prefix reduction laws for the existing
# algorithm. The unequal-character msb/routing theorem is still outstanding.
law difference_empty_left:
  for h: Char
  for tail: String
  {Map.diff(SNil{}, SCon{h, tail}) == 0n : Nat}
def difference_empty_left(h, tail):
  {==}

law difference_empty_right:
  for h: Char
  for tail: String
  {Map.diff(SCon{h, tail}, SNil{}) == 0n : Nat}
def difference_empty_right(h, tail):
  {==}

law difference_common_character:
  for h: Char
  for a: String
  for b: String
  {Map.diff(SCon{h, a}, SCon{h, b}) == Nat.add(33n, Map.diff(a, b)) : Nat}
def difference_common_character(h, a, b):
  match h:
    case Chr{U32{w}}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_compare_self(32n, w)) : {Map.diff.fin(a, b, (Map.diff.chr(U32.xor(U32{w}, U32{w})), Cmp.is_eq(_))) == Nat.add(33n, Map.diff(a, b)) : Nat}
      {==}

law difference_empty_presence:
  for h: Char
  for tail: String
  {Map.bit.go(SCon{h, tail}, Map.diff(SNil{}, SCon{h, tail}), 0n) == (SCon{h, tail}, True{}) : String & Bool}
def difference_empty_presence(h, tail):
  match h:
    case Chr{x}:
      {==}

def lookup_map(-V: Data, r: Map<&2, V> & V) -> Map<&2, V>:
  (m, value) = r
  m

law lookup_leaf_preserves:
  for -V: Data
  for d: V
  for v: V
  for key: String
  for stored: String
  for c: Cmp
  {lookup_map(V, Map.get.leaf(V, d, v, ((key, stored), c))) == MLeaf{stored, v} : Map<&2, V>}
def lookup_leaf_preserves(V, d, v, key, stored, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law lookup_lo_projection:
  for -V: Data
  for p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & V
  {lookup_map(V, Map.lo(&2, V, V, p, hi, r)) == MNode{p, lookup_map(V, r), hi} : Map<&2, V>}
def lookup_lo_projection(V, p, hi, r):
  match r:
    case Tuple{lo, value}:
      {==}

law lookup_hi_projection:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & V
  {lookup_map(V, Map.hi(&2, V, V, p, lo, r)) == MNode{p, lo, lookup_map(V, r)} : Map<&2, V>}
def lookup_hi_projection(V, p, lo, r):
  match r:
    case Tuple{hi, value}:
      {==}

law lookup_branch_preserves:
  for -V: Data
  for +d: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for kb: String & Bool
  for lp: @key: String -> {lookup_map(V, Map.get(V, d, lo, key)) == lo : Map<&2, V>}
  for hp: @key: String -> {lookup_map(V, Map.get(V, d, hi, key)) == hi : Map<&2, V>}
  {lookup_map(V, Map.get.bit(V, d, lo, hi, p, kb)) == MNode{p, lo, hi} : Map<&2, V>}
def lookup_branch_preserves(V, d, lo, hi, p, kb, lp, hp):
  match kb:
    case Tuple{+key, False{}}:
      Equal.trans(Map<&2, V>, lookup_map(V, Map.lo(&2, V, V, p, hi, Map.get(V, d, lo, key))), MNode{p, lookup_map(V, Map.get(V, d, lo, key)), hi}, MNode{p, lo, hi}, lookup_lo_projection(V, p, hi, Map.get(V, d, lo, key)), Equal.cong(Map<&2, V>, Map<&2, V>, m => MNode{p, m, hi}, lookup_map(V, Map.get(V, d, lo, key)), lo, lp(key)))
    case Tuple{+key, True{}}:
      Equal.trans(Map<&2, V>, lookup_map(V, Map.hi(&2, V, V, p, lo, Map.get(V, d, hi, key))), MNode{p, lo, lookup_map(V, Map.get(V, d, hi, key))}, MNode{p, lo, hi}, lookup_hi_projection(V, p, lo, Map.get(V, d, hi, key)), Equal.cong(Map<&2, V>, Map<&2, V>, m => MNode{p, lo, m}, lookup_map(V, Map.get(V, d, hi, key)), hi, hp(key)))

law lookup_preserves_map:
  for -V: Data
  for +d: V
  for m: Map<&2, V>
  for +key: String
  {lookup_map(V, Map.get(V, d, m, key)) == m : Map<&2, V>}
def lookup_preserves_map(V, d, m, key):
  match m:
    case MTip{}:
      {==}
    case MLeaf{+stored, v}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), comparison_tag(String, String.cmp(key, stored))), string_comparison_shape(key, stored)) : {lookup_map(V, Map.get.leaf(V, d, v, _)) == MLeaf{stored, v} : Map<&2, V>}
      lookup_leaf_preserves(V, d, v, key, stored, comparison_tag(String, String.cmp(key, stored)))
    case MNode{+p, +lo, +hi}:
      lookup_branch_preserves(V, d, lo, hi, p, Map.bit(key, p), q => lookup_preserves_map(V, d, lo, q), q => lookup_preserves_map(V, d, hi, q))

law natural_add_associative:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}
def natural_add_associative(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.add(b, c)), Nat.add(Nat.add(p, b), c), natural_add_associative(p, b, c))

law natural_add_right_zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}
def natural_add_right_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, natural_add_right_zero(p))

law keys_accumulator_size:
  for -V: Data
  for m: Map<&2, V>
  for +acc: List<&2, String>
  {List.length(&2, String, Map.keys.go(&2, V, m, acc)) == Nat.add(Map.size(&2, V, m), List.length(&2, String, acc)) : Nat}
def keys_accumulator_size(V, m, acc):
  match m:
    case MTip{}:
      {==}
    case MLeaf{key, value}:
      {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Nat, List.length(&2, String, Map.keys.go(&2, V, lo, Map.keys.go(&2, V, hi, acc))), Nat.add(Map.size(&2, V, lo), List.length(&2, String, Map.keys.go(&2, V, hi, acc))), keys_accumulator_size(V, lo, Map.keys.go(&2, V, hi, acc))) : {_ == Nat.add(Nat.add(Map.size(&2, V, lo), Map.size(&2, V, hi)), List.length(&2, String, acc)) : Nat}
      %Equal.sym(Nat, List.length(&2, String, Map.keys.go(&2, V, hi, acc)), Nat.add(Map.size(&2, V, hi), List.length(&2, String, acc)), keys_accumulator_size(V, hi, acc)) : {Nat.add(Map.size(&2, V, lo), _) == Nat.add(Nat.add(Map.size(&2, V, lo), Map.size(&2, V, hi)), List.length(&2, String, acc)) : Nat}
      natural_add_associative(Map.size(&2, V, lo), Map.size(&2, V, hi), List.length(&2, String, acc))

law keys_size:
  for -V: Data
  for +m: Map<&2, V>
  {List.length(&2, String, Map.keys(&2, V, m)) == Map.size(&2, V, m) : Nat}
def keys_size(V, m):
  Equal.trans(Nat, List.length(&2, String, Map.keys(&2, V, m)), Nat.add(Map.size(&2, V, m), 0n), Map.size(&2, V, m), keys_accumulator_size(V, m, Nil{}), natural_add_right_zero(Map.size(&2, V, m)))

law entries_accumulator_size:
  for -V: Data
  for m: Map<&2, V>
  for +acc: List<&2, Sigma<&2, &2, String, _ => V>>
  {List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list.go(&2, V, m, acc)) == Nat.add(Map.size(&2, V, m), List.length(&2, Sigma<&2, &2, String, _ => V>, acc)) : Nat}
def entries_accumulator_size(V, m, acc):
  match m:
    case MTip{}:
      {==}
    case MLeaf{key, value}:
      {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Nat, List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list.go(&2, V, lo, Map.to_list.go(&2, V, hi, acc))), Nat.add(Map.size(&2, V, lo), List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list.go(&2, V, hi, acc))), entries_accumulator_size(V, lo, Map.to_list.go(&2, V, hi, acc))) : {_ == Nat.add(Nat.add(Map.size(&2, V, lo), Map.size(&2, V, hi)), List.length(&2, Sigma<&2, &2, String, _ => V>, acc)) : Nat}
      %Equal.sym(Nat, List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list.go(&2, V, hi, acc)), Nat.add(Map.size(&2, V, hi), List.length(&2, Sigma<&2, &2, String, _ => V>, acc)), entries_accumulator_size(V, hi, acc)) : {Nat.add(Map.size(&2, V, lo), _) == Nat.add(Nat.add(Map.size(&2, V, lo), Map.size(&2, V, hi)), List.length(&2, Sigma<&2, &2, String, _ => V>, acc)) : Nat}
      natural_add_associative(Map.size(&2, V, lo), Map.size(&2, V, hi), List.length(&2, Sigma<&2, &2, String, _ => V>, acc))

law entries_size:
  for -V: Data
  for +m: Map<&2, V>
  {List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list(&2, V, m)) == Map.size(&2, V, m) : Nat}
def entries_size(V, m):
  Equal.trans(Nat, List.length(&2, Sigma<&2, &2, String, _ => V>, Map.to_list(&2, V, m)), Nat.add(Map.size(&2, V, m), 0n), Map.size(&2, V, m), entries_accumulator_size(V, m, Nil{}), natural_add_right_zero(Map.size(&2, V, m)))
