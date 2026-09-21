import Base
import ../../types/lru_model.bend as T

# Identity preserves all Base String characters, including Chr{0}.
def string_encode(s: String) -> String:
  s

def string_decode(s: String) -> String:
  s

# A unary integer codec: chosen for a simple total inverse, not speed.
# Every character has code 0; the first character encodes the sign.
def natural_encode(n: Nat) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{Chr{0}, natural_encode(p)}

def natural_decode(s: String) -> Nat:
  String.length(s)

def integer_encode(n: T.Integer) -> String:
  match n:
    case T.Positive{p}:
      SCon{Chr{1}, natural_encode(p)}
    case T.Negative{p}:
      SCon{Chr{0}, natural_encode(p)}

def integer_decode_sign(sign: Bool, n: Nat) -> T.Integer:
  match sign:
    case True{}:
      T.Negative{n}
    case False{}:
      T.Positive{n}

def integer_decode(s: String) -> T.Integer:
  match s:
    case SNil{}:
      T.Positive{0n}
    case SCon{Chr{c}, t}:
      integer_decode_sign(U32.is_zero(c), natural_decode(t))

law string_roundtrip:
  for s: String
  {string_decode(string_encode(s)) == s : String}
def string_roundtrip(s):
  {==}

law natural_roundtrip:
  for n: Nat
  {natural_decode(natural_encode(n)) == n : Nat}
def natural_roundtrip(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %natural_roundtrip(p) : {1n+natural_decode(natural_encode(p)) == 1n+_ : Nat}
      {==}

law integer_roundtrip:
  for n: T.Integer
  {integer_decode(integer_encode(n)) == n : T.Integer}
def integer_roundtrip(n):
  match n:
    case T.Positive{p}:
      Equal.cong(Nat, T.Integer, x => T.Positive{x}, natural_decode(natural_encode(p)), p, natural_roundtrip(p))
    case T.Negative{p}:
      Equal.cong(Nat, T.Integer, x => T.Negative{x}, natural_decode(natural_encode(p)), p, natural_roundtrip(p))

law integer_injective:
  for a: T.Integer
  for b: T.Integer
  for e: {integer_encode(a) == integer_encode(b) : String}
  {a == b : T.Integer}
def integer_injective(a, b, e):
  Equal.trans(T.Integer, a, integer_decode(integer_encode(a)), b,
    Equal.sym(T.Integer, integer_decode(integer_encode(a)), a, integer_roundtrip(a)),
    Equal.trans(T.Integer, integer_decode(integer_encode(a)), integer_decode(integer_encode(b)), b,
      Equal.cong(String, T.Integer, integer_decode, integer_encode(a), integer_encode(b), e), integer_roundtrip(b)))

law string_injective:
  for a: String
  for b: String
  for e: {string_encode(a) == string_encode(b) : String}
  {a == b : String}
def string_injective(a, b, e):
  e

# Fixed-width binary words are a practical integer codec; unlike unary Integer,
# a 64-bit key always occupies 64 characters. Leading zero bits are retained.
def bit_char(b: Bool) -> Char:
  match b:
    case False{}:
      '0'
    case True{}:
      '1'

def char_bit(c: Char) -> Bool:
  match c:
    case Chr{x}:
      U32.is_eq(x, 49)

def word_encode(n: Nat, w: Word(n)) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      match w:
        case WCon{b, rest}:
          SCon{bit_char(b), word_encode(p, rest)}

def word_decode(n: Nat, s: String) -> Word(n):
  match n s:
    case 0n rest:
      WNil{}
    case 1n+p SNil{}:
      WCon{False{}, word_decode(p, SNil{})}
    case 1n+p SCon{h, t}:
      WCon{char_bit(h), word_decode(p, t)}

law bit_roundtrip:
  for b: Bool
  {char_bit(bit_char(b)) == b : Bool}
def bit_roundtrip(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law word_roundtrip:
  for n: Nat
  for w: Word(n)
  {word_decode(n, word_encode(n, w)) == w : Word(n)}
def word_roundtrip(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, rest}:
          %bit_roundtrip(b) : {WCon{char_bit(bit_char(b)), word_decode(p, word_encode(p, rest))} == WCon{_, rest} : Word(1n+p)}
          %word_roundtrip(p, rest) : {WCon{char_bit(bit_char(b)), word_decode(p, word_encode(p, rest))} == WCon{char_bit(bit_char(b)), _} : Word(1n+p)}
          {==}

law word_injective:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {word_encode(n, a) == word_encode(n, b) : String}
  {a == b : Word(n)}
def word_injective(n, a, b, e):
  Equal.trans(Word(n), a, word_decode(n, word_encode(n, a)), b,
    Equal.sym(Word(n), word_decode(n, word_encode(n, a)), a, word_roundtrip(n, a)),
    Equal.trans(Word(n), word_decode(n, word_encode(n, a)), word_decode(n, word_encode(n, b)), b,
      Equal.cong(String, Word(n), word_decode(n), word_encode(n, a), word_encode(n, b), e), word_roundtrip(n, b)))

law string_equality_preserved:
  for a: String
  for b: String
  for e: {a == b : String}
  {string_encode(a) == string_encode(b) : String}
def string_equality_preserved(a, b, e):
  e

law integer_equality_preserved:
  for a: T.Integer
  for b: T.Integer
  for e: {a == b : T.Integer}
  {integer_encode(a) == integer_encode(b) : String}
def integer_equality_preserved(a, b, e):
  Equal.cong(T.Integer, String, integer_encode, a, b, e)

law word_equality_preserved:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {a == b : Word(n)}
  {word_encode(n, a) == word_encode(n, b) : String}
def word_equality_preserved(n, a, b, e):
  Equal.cong(Word(n), String, word_encode(n), a, b, e)

# The Word64 key codec used by the adapter for bigint keys.
def word64_encode(w: Word(64n)) -> String:
  word_encode(64n, w)

law word64_injective:
  for a: Word(64n)
  for b: Word(64n)
  for e: {word64_encode(a) == word64_encode(b) : String}
  {a == b : Word(64n)}
def word64_injective(a, b, e):
  word_injective(64n, a, b, e)
