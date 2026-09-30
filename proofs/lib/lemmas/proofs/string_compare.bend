import Base

# String, word and character comparison lemmas and two natural-addition
# lemmas, split out of native_map.bend so that code which only needs these
# does not import the lemmas about Base's Map internals.

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

