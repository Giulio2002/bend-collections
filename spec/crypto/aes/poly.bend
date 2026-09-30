import Base

# Polynomials over GF(2), as FIPS 197 section 4 and SP 800-38D section 6.3 use
# them. A polynomial is the list of its coefficients, the coefficient of x^0
# first; a residue modulo a polynomial m(x) of degree n is a Word(n) of n
# coefficients (Base's Word: a Bool vector, index 0 first).

# Coefficient-wise sum (XOR); the longer tail is kept.
def add(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case Nil{} _:
      b
    case x <> xs Nil{}:
      x <> xs
    case x <> xs y <> ys:
      Bool.xor(x, y) <> add(xs, ys)

# c * a for a constant c in GF(2).
def scale(+c: Bool, a: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      Nil{}
    case x <> xs:
      Bool.and(c, x) <> scale(c, xs)

# The schoolbook product: (c + x*q(x)) * b(x) = c*b(x) + x*(q(x)*b(x)).
def mul(a: List<&2, Bool>, +b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      Nil{}
    case c <> q:
      add(scale(c, b), False{} <> mul(q, b))

# The coefficient of x^(n-1) of a residue.
def top(n: Nat, w: Word(n)) -> Bool:
  match n w:
    case 0n WNil{}:
      False{}
    case 1n WCon{b, t}:
      b
    case 2n+p WCon{b, t}:
      top(1n+p, t)

def wscale(n: Nat, c: Bool, w: Word(n)) -> Word(n):
  match c:
    case True{}:
      w
    case False{}:
      Word.zero(n)

# The constant polynomial c as a residue.
def constant(n: Nat, c: Bool) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{c, Word.zero(p)}

# Multiplication by x modulo m(x) = x^n + low(x) (deg low < n): shift every
# coefficient up one degree; the coefficient that reaches x^n is replaced by
# low(x), since x^n = low(x) modulo m(x).
def times_x(+n: Nat, +low: Word(n), +r: Word(n)) -> Word(n):
  Word.xor(n, wscale(n, top(n, r), low), Word.shl(n, r))

# p(x) modulo m(x) = x^n + low(x), by Horner's rule:
# p(x) = c + x*q(x), so p mod m = c + x*(q mod m) mod m.
def reduce(+n: Nat, +low: Word(n), p: List<&2, Bool>) -> Word(n):
  match p:
    case Nil{}:
      Word.zero(n)
    case c <> q:
      Word.xor(n, constant(n, c), times_x(n, low, reduce(n, low, q)))

# The coefficients of a residue, as a polynomial.
def coefficients(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n w:
    case 0n WNil{}:
      Nil{}
    case 1n+p WCon{b, t}:
      b <> coefficients(p, t)
