import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/crypto/aes/poly.bend as P

# Polynomial arithmetic over GF(2), for any modulus m(x) = x^n + low(x):
# reducing the product a(x) * b(x) modulo m equals the shift-and-add
# evaluation of SP 800-38D's Algorithm 1 (sa below): Z accumulates b(x)*x^i
# (mod m) for every set coefficient a_i. With n = 128 and low = R this is
# the GHASH product; the implementation computes sa.

# ---- one bit ----

def bxor_false(+b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bxor_comm(+a: Bool, +b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bxor_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def bxor_self(+a: Bool) -> {Bool.xor(a, a) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bswap4(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> {Bool.xor(Bool.xor(a, b), Bool.xor(c, d)) == Bool.xor(Bool.xor(a, c), Bool.xor(b, d)) : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

# ---- words: XOR is a commutative group, shifts and tops are linear ----

def xor_zero_l(+n: Nat, +w: Word(n)) -> {Word.xor(n, Word.zero(n), w) == w : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      %xor_zero_l(p, t) : {WCon{b, Word.xor(p, Word.zero(p), t)} == WCon{b, _} : Word(1n+p)}
      {==}

def xor_zero_r(+n: Nat, +w: Word(n)) -> {Word.xor(n, w, Word.zero(n)) == w : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      %xor_zero_r(p, t) : {WCon{Bool.xor(b, False{}), Word.xor(p, t, Word.zero(p))} == WCon{b, _} : Word(1n+p)}
      %bxor_false(b) : {WCon{Bool.xor(b, False{}), Word.xor(p, t, Word.zero(p))} == WCon{_, Word.xor(p, t, Word.zero(p))} : Word(1n+p)}
      {==}

def xor_self(+n: Nat, +w: Word(n)) -> {Word.xor(n, w, w) == Word.zero(n) : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      %xor_self(p, t) : {WCon{Bool.xor(b, b), Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
      %bxor_self(b) : {WCon{Bool.xor(b, b), Word.xor(p, t, t)} == WCon{_, Word.xor(p, t, t)} : Word(1n+p)}
      {==}

def xor_assoc(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}:
  match n a b c:
    case 0n WNil{} WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, s} WCon{y, t} WCon{z, u}:
      %xor_assoc(p, s, t, u) : {WCon{Bool.xor(Bool.xor(x, y), z), Word.xor(p, Word.xor(p, s, t), u)} == WCon{Bool.xor(x, Bool.xor(y, z)), _} : Word(1n+p)}
      %bxor_assoc(x, y, z) : {WCon{Bool.xor(Bool.xor(x, y), z), Word.xor(p, Word.xor(p, s, t), u)} == WCon{_, Word.xor(p, Word.xor(p, s, t), u)} : Word(1n+p)}
      {==}

def xor_swap4(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n), +d: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), Word.xor(n, c, d)) == Word.xor(n, Word.xor(n, a, c), Word.xor(n, b, d)) : Word(n)}:
  match n a b c d:
    case 0n WNil{} WNil{} WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, s} WCon{y, t} WCon{z, u} WCon{w, v}:
      %xor_swap4(p, s, t, u, v) : {WCon{Bool.xor(Bool.xor(x, y), Bool.xor(z, w)), Word.xor(p, Word.xor(p, s, t), Word.xor(p, u, v))} == WCon{Bool.xor(Bool.xor(x, z), Bool.xor(y, w)), _} : Word(1n+p)}
      %bswap4(x, y, z, w) : {WCon{Bool.xor(Bool.xor(x, y), Bool.xor(z, w)), Word.xor(p, Word.xor(p, s, t), Word.xor(p, u, v))} == WCon{_, Word.xor(p, Word.xor(p, s, t), Word.xor(p, u, v))} : Word(1n+p)}
      {==}

def put_xor(+p: Nat, +c: Bool, +d: Bool, +s: Word(p), +t: Word(p)) -> {Word.shl.put(p, Bool.xor(c, d), Word.xor(p, s, t)) == Word.xor(p, Word.shl.put(p, c, s), Word.shl.put(p, d, t)) : Word(p)}:
  match p s t:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+q WCon{x, s1} WCon{y, t1}:
      %put_xor(q, x, y, s1, t1) : {WCon{Bool.xor(c, d), Word.shl.put(q, Bool.xor(x, y), Word.xor(q, s1, t1))} == WCon{Bool.xor(c, d), _} : Word(1n+q)}
      {==}

def shl_xor(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.shl(n, Word.xor(n, a, b)) == Word.xor(n, Word.shl(n, a), Word.shl(n, b)) : Word(n)}:
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, s} WCon{y, t}:
      %put_xor(p, x, y, s, t) : {WCon{False{}, Word.shl.put(p, Bool.xor(x, y), Word.xor(p, s, t))} == WCon{False{}, _} : Word(1n+p)}
      {==}

def top_xor(+n: Nat, +a: Word(n), +b: Word(n)) -> {P.top(n, Word.xor(n, a, b)) == Bool.xor(P.top(n, a), P.top(n, b)) : Bool}:
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n WCon{x, s} WCon{y, t}:
      {==}
    case 2n+p WCon{x, s} WCon{y, t}:
      top_xor(1n+p, s, t)

def top_zero(+n: Nat) -> {P.top(n, Word.zero(n)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      top_zero(1n+p)

def put_zero(+p: Nat) -> {Word.shl.put(p, False{}, Word.zero(p)) == Word.zero(p) : Word(p)}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %put_zero(q) : {WCon{False{}, Word.shl.put(q, False{}, Word.zero(q))} == WCon{False{}, _} : Word(1n+q)}
      {==}

def shl_zero(+n: Nat) -> {Word.shl(n, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %put_zero(p) : {WCon{False{}, Word.shl.put(p, False{}, Word.zero(p))} == WCon{False{}, _} : Word(1n+p)}
      {==}

def wscale_xor(+n: Nat, +c: Bool, +d: Bool, +w: Word(n)) -> {P.wscale(n, Bool.xor(c, d), w) == Word.xor(n, P.wscale(n, c, w), P.wscale(n, d, w)) : Word(n)}:
  match c d:
    case True{} True{}:
      Equal.sym(Word(n), Word.xor(n, w, w), Word.zero(n), xor_self(n, w))
    case True{} False{}:
      Equal.sym(Word(n), Word.xor(n, w, Word.zero(n)), w, xor_zero_r(n, w))
    case False{} True{}:
      Equal.sym(Word(n), Word.xor(n, Word.zero(n), w), w, xor_zero_l(n, w))
    case False{} False{}:
      Equal.sym(Word(n), Word.xor(n, Word.zero(n), Word.zero(n)), Word.zero(n), xor_zero_l(n, Word.zero(n)))

# ---- multiplication by x modulo m ----

def tx_xor(+n: Nat, +low: Word(n), +a: Word(n), +b: Word(n)) -> {P.times_x(n, low, Word.xor(n, a, b)) == Word.xor(n, P.times_x(n, low, a), P.times_x(n, low, b)) : Word(n)}:
  %Equal.sym(Bool, P.top(n, Word.xor(n, a, b)), Bool.xor(P.top(n, a), P.top(n, b)), top_xor(n, a, b)) : {Word.xor(n, P.wscale(n, _, low), Word.shl(n, Word.xor(n, a, b))) == Word.xor(n, P.times_x(n, low, a), P.times_x(n, low, b)) : Word(n)}
  %Equal.sym(Word(n), P.wscale(n, Bool.xor(P.top(n, a), P.top(n, b)), low), Word.xor(n, P.wscale(n, P.top(n, a), low), P.wscale(n, P.top(n, b), low)), wscale_xor(n, P.top(n, a), P.top(n, b), low)) : {Word.xor(n, _, Word.shl(n, Word.xor(n, a, b))) == Word.xor(n, P.times_x(n, low, a), P.times_x(n, low, b)) : Word(n)}
  %Equal.sym(Word(n), Word.shl(n, Word.xor(n, a, b)), Word.xor(n, Word.shl(n, a), Word.shl(n, b)), shl_xor(n, a, b)) : {Word.xor(n, Word.xor(n, P.wscale(n, P.top(n, a), low), P.wscale(n, P.top(n, b), low)), _) == Word.xor(n, P.times_x(n, low, a), P.times_x(n, low, b)) : Word(n)}
  xor_swap4(n, P.wscale(n, P.top(n, a), low), P.wscale(n, P.top(n, b), low), Word.shl(n, a), Word.shl(n, b))

def tx_zero(+n: Nat, +low: Word(n)) -> {P.times_x(n, low, Word.zero(n)) == Word.zero(n) : Word(n)}:
  %Equal.sym(Bool, P.top(n, Word.zero(n)), False{}, top_zero(n)) : {Word.xor(n, P.wscale(n, _, low), Word.shl(n, Word.zero(n))) == Word.zero(n) : Word(n)}
  %Equal.sym(Word(n), Word.shl(n, Word.zero(n)), Word.zero(n), shl_zero(n)) : {Word.xor(n, Word.zero(n), _) == Word.zero(n) : Word(n)}
  xor_zero_l(n, Word.zero(n))

def tx_wscale(+n: Nat, +low: Word(n), +c: Bool, +v: Word(n)) -> {P.times_x(n, low, P.wscale(n, c, v)) == P.wscale(n, c, P.times_x(n, low, v)) : Word(n)}:
  match c:
    case True{}:
      {==}
    case False{}:
      tx_zero(n, low)

# ---- reduction modulo m is linear ----

def constant_xor(+n: Nat, +c: Bool, +d: Bool) -> {P.constant(n, Bool.xor(c, d)) == Word.xor(n, P.constant(n, c), P.constant(n, d)) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Word(p), Word.xor(p, Word.zero(p), Word.zero(p)), Word.zero(p), xor_zero_l(p, Word.zero(p))) : {WCon{Bool.xor(c, d), Word.zero(p)} == WCon{Bool.xor(c, d), _} : Word(1n+p)}
      {==}

def red_add(+n: Nat, +low: Word(n), +p: List<&2, Bool>, +q: List<&2, Bool>) -> {P.reduce(n, low, P.add(p, q)) == Word.xor(n, P.reduce(n, low, p), P.reduce(n, low, q)) : Word(n)}:
  match p q:
    case Nil{} _:
      Equal.sym(Word(n), Word.xor(n, Word.zero(n), P.reduce(n, low, q)), P.reduce(n, low, q), xor_zero_l(n, P.reduce(n, low, q)))
    case x <> xs Nil{}:
      Equal.sym(Word(n), Word.xor(n, P.reduce(n, low, x <> xs), Word.zero(n)), P.reduce(n, low, x <> xs), xor_zero_r(n, P.reduce(n, low, x <> xs)))
    case x <> xs y <> ys:
      %Equal.sym(Word(n), P.reduce(n, low, P.add(xs, ys)), Word.xor(n, P.reduce(n, low, xs), P.reduce(n, low, ys)), red_add(n, low, xs, ys)) : {Word.xor(n, P.constant(n, Bool.xor(x, y)), P.times_x(n, low, _)) == Word.xor(n, P.reduce(n, low, x <> xs), P.reduce(n, low, y <> ys)) : Word(n)}
      %Equal.sym(Word(n), P.times_x(n, low, Word.xor(n, P.reduce(n, low, xs), P.reduce(n, low, ys))), Word.xor(n, P.times_x(n, low, P.reduce(n, low, xs)), P.times_x(n, low, P.reduce(n, low, ys))), tx_xor(n, low, P.reduce(n, low, xs), P.reduce(n, low, ys))) : {Word.xor(n, P.constant(n, Bool.xor(x, y)), _) == Word.xor(n, P.reduce(n, low, x <> xs), P.reduce(n, low, y <> ys)) : Word(n)}
      %Equal.sym(Word(n), P.constant(n, Bool.xor(x, y)), Word.xor(n, P.constant(n, x), P.constant(n, y)), constant_xor(n, x, y)) : {Word.xor(n, _, Word.xor(n, P.times_x(n, low, P.reduce(n, low, xs)), P.times_x(n, low, P.reduce(n, low, ys)))) == Word.xor(n, P.reduce(n, low, x <> xs), P.reduce(n, low, y <> ys)) : Word(n)}
      xor_swap4(n, P.constant(n, x), P.constant(n, y), P.times_x(n, low, P.reduce(n, low, xs)), P.times_x(n, low, P.reduce(n, low, ys)))

def scale_true(+b: List<&2, Bool>) -> {P.scale(True{}, b) == b : List<&2, Bool>}:
  match b:
    case Nil{}:
      {==}
    case x <> xs:
      %scale_true(xs) : {x <> P.scale(True{}, xs) == x <> _ : List<&2, Bool>}
      {==}

def constant_false_xor(+n: Nat) -> {Word.xor(n, P.constant(n, False{}), Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      xor_zero_l(1n+p, Word.zero(1n+p))

def red_scale_false(+n: Nat, +low: Word(n), +b: List<&2, Bool>) -> {P.reduce(n, low, P.scale(False{}, b)) == Word.zero(n) : Word(n)}:
  match b:
    case Nil{}:
      {==}
    case x <> xs:
      %Equal.sym(Word(n), P.reduce(n, low, P.scale(False{}, xs)), Word.zero(n), red_scale_false(n, low, xs)) : {Word.xor(n, P.constant(n, False{}), P.times_x(n, low, _)) == Word.zero(n) : Word(n)}
      %Equal.sym(Word(n), P.times_x(n, low, Word.zero(n)), Word.zero(n), tx_zero(n, low)) : {Word.xor(n, P.constant(n, False{}), _) == Word.zero(n) : Word(n)}
      constant_false_xor(n)

def red_scale(+n: Nat, +low: Word(n), +c: Bool, +b: List<&2, Bool>) -> {P.reduce(n, low, P.scale(c, b)) == P.wscale(n, c, P.reduce(n, low, b)) : Word(n)}:
  match c:
    case True{}:
      %scale_true(b) : {P.reduce(n, low, P.scale(True{}, b)) == P.reduce(n, low, _) : Word(n)}
      {==}
    case False{}:
      red_scale_false(n, low, b)

def constant_false_l(+n: Nat, +w: Word(n)) -> {Word.xor(n, P.constant(n, False{}), w) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      xor_zero_l(1n+p, w)

def red_shift(+n: Nat, +low: Word(n), +p: List<&2, Bool>) -> {P.reduce(n, low, False{} <> p) == P.times_x(n, low, P.reduce(n, low, p)) : Word(n)}:
  constant_false_l(n, P.times_x(n, low, P.reduce(n, low, p)))

# ---- the shift-and-add product ----

# sum over the set coefficients a_i of v * x^i (mod m)
def sm(+n: Nat, +low: Word(n), a: List<&2, Bool>, +v: Word(n)) -> Word(n):
  match a:
    case Nil{}:
      Word.zero(n)
    case c <> r:
      Word.xor(n, P.wscale(n, c, v), sm(n, low, r, P.times_x(n, low, v)))

# Algorithm 1 of SP 800-38D: Z ^= a_i ? V : 0, V = V * x.
def sa(+n: Nat, +low: Word(n), a: List<&2, Bool>, z: Word(n), +v: Word(n)) -> Word(n):
  match a:
    case Nil{}:
      z
    case c <> r:
      sa(n, low, r, Word.xor(n, z, P.wscale(n, c, v)), P.times_x(n, low, v))

def tx_sm(+n: Nat, +low: Word(n), +a: List<&2, Bool>, +v: Word(n)) -> {P.times_x(n, low, sm(n, low, a, v)) == sm(n, low, a, P.times_x(n, low, v)) : Word(n)}:
  match a:
    case Nil{}:
      tx_zero(n, low)
    case c <> r:
      %tx_sm(n, low, r, P.times_x(n, low, v)) : {P.times_x(n, low, Word.xor(n, P.wscale(n, c, v), sm(n, low, r, P.times_x(n, low, v)))) == Word.xor(n, P.wscale(n, c, P.times_x(n, low, v)), _) : Word(n)}
      %tx_wscale(n, low, c, v) : {P.times_x(n, low, Word.xor(n, P.wscale(n, c, v), sm(n, low, r, P.times_x(n, low, v)))) == Word.xor(n, _, P.times_x(n, low, sm(n, low, r, P.times_x(n, low, v)))) : Word(n)}
      tx_xor(n, low, P.wscale(n, c, v), sm(n, low, r, P.times_x(n, low, v)))

def red_mul(+n: Nat, +low: Word(n), +a: List<&2, Bool>, +b: List<&2, Bool>) -> {P.reduce(n, low, P.mul(a, b)) == sm(n, low, a, P.reduce(n, low, b)) : Word(n)}:
  match a:
    case Nil{}:
      {==}
    case c <> q:
      %tx_sm(n, low, q, P.reduce(n, low, b)) : {P.reduce(n, low, P.add(P.scale(c, b), False{} <> P.mul(q, b))) == Word.xor(n, P.wscale(n, c, P.reduce(n, low, b)), _) : Word(n)}
      %red_mul(n, low, q, b) : {P.reduce(n, low, P.add(P.scale(c, b), False{} <> P.mul(q, b))) == Word.xor(n, P.wscale(n, c, P.reduce(n, low, b)), P.times_x(n, low, _)) : Word(n)}
      %red_shift(n, low, P.mul(q, b)) : {P.reduce(n, low, P.add(P.scale(c, b), False{} <> P.mul(q, b))) == Word.xor(n, P.wscale(n, c, P.reduce(n, low, b)), _) : Word(n)}
      %red_scale(n, low, c, b) : {P.reduce(n, low, P.add(P.scale(c, b), False{} <> P.mul(q, b))) == Word.xor(n, _, P.reduce(n, low, False{} <> P.mul(q, b))) : Word(n)}
      red_add(n, low, P.scale(c, b), False{} <> P.mul(q, b))

def sa_sm(+n: Nat, +low: Word(n), +a: List<&2, Bool>, +z: Word(n), +v: Word(n)) -> {sa(n, low, a, z, v) == Word.xor(n, z, sm(n, low, a, v)) : Word(n)}:
  match a:
    case Nil{}:
      Equal.sym(Word(n), Word.xor(n, z, Word.zero(n)), z, xor_zero_r(n, z))
    case c <> r:
      %xor_assoc(n, z, P.wscale(n, c, v), sm(n, low, r, P.times_x(n, low, v))) : {sa(n, low, c <> r, z, v) == _ : Word(n)}
      sa_sm(n, low, r, Word.xor(n, z, P.wscale(n, c, v)), P.times_x(n, low, v))

# ---- a residue is its own reduction ----

# The first n coefficients of a list, zero-filled.
def wof(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n bs:
    case 0n _:
      WNil{}
    case 1n+p Nil{}:
      WCon{False{}, wof(p, Nil{})}
    case 1n+p b <> rest:
      WCon{b, wof(p, rest)}

def wof_nil(+n: Nat) -> {Word.zero(n) == wof(n, Nil{}) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %wof_nil(p) : {WCon{False{}, Word.zero(p)} == WCon{False{}, _} : Word(1n+p)}
      {==}

def wof_false_nil(+q: Nat) -> {wof(q, [False{}]) == wof(q, Nil{}) : Word(q)}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def put_wof(+p: Nat, +c: Bool, +l: List<&2, Bool>) -> {Word.shl.put(p, c, wof(p, l)) == wof(p, c <> l) : Word(p)}:
  match p l:
    case 0n _:
      {==}
    case 1n+q Nil{}:
      %Equal.sym(Word(q), Word.shl.put(q, False{}, wof(q, Nil{})), wof(q, [False{}]), put_wof(q, False{}, Nil{})) : {WCon{c, _} == WCon{c, wof(q, Nil{})} : Word(1n+q)}
      %wof_false_nil(q) : {WCon{c, wof(q, [False{}])} == WCon{c, _} : Word(1n+q)}
      {==}
    case 1n+q x <> xs:
      %put_wof(q, x, xs) : {WCon{c, Word.shl.put(q, x, wof(q, xs))} == WCon{c, _} : Word(1n+q)}
      {==}

def shl_wof(+n: Nat, +l: List<&2, Bool>) -> {Word.shl(n, wof(n, l)) == wof(n, False{} <> l) : Word(n)}:
  match n l:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      %wof_false_nil(p) : {WCon{False{}, Word.shl.put(p, False{}, wof(p, Nil{}))} == WCon{False{}, _} : Word(1n+p)}
      %put_wof(p, False{}, Nil{}) : {WCon{False{}, Word.shl.put(p, False{}, wof(p, Nil{}))} == WCon{False{}, _} : Word(1n+p)}
      {==}
    case 1n+p x <> xs:
      %put_wof(p, x, xs) : {WCon{False{}, Word.shl.put(p, x, wof(p, xs))} == WCon{False{}, _} : Word(1n+p)}
      {==}

def top_short(+p: Nat, +l: List<&2, Bool>, +h: {Nat.is_le(List.length(&2, Bool, l), p) == True{} : Bool}) -> {P.top(1n+p, wof(1n+p, l)) == False{} : Bool}:
  match p l:
    case 0n Nil{}:
      {==}
    case 0n x <> xs:
      Empty.absurd({P.top(1n, wof(1n, x <> xs)) == False{} : Bool}, L.false_true(h))
    case 1n+q Nil{}:
      top_short(q, Nil{}, N.zero_le(q))
    case 1n+q x <> xs:
      top_short(q, xs, h)

def red_short(+n: Nat, +low: Word(n), +l: List<&2, Bool>, +h: {Nat.is_le(List.length(&2, Bool, l), n) == True{} : Bool}) -> {P.reduce(n, low, l) == wof(n, l) : Word(n)}:
  match n l:
    case _ Nil{}:
      wof_nil(n)
    case 0n x <> xs:
      Empty.absurd({P.reduce(0n, low, x <> xs) == wof(0n, x <> xs) : Word(0n)}, L.false_true(h))
    case 1n+p x <> xs:
      +hp = {h : {Nat.is_le(List.length(&2, Bool, xs), p) == True{} : Bool}}
      %Equal.sym(Word(1n+p), P.reduce(1n+p, low, xs), wof(1n+p, xs), red_short(1n+p, low, xs, N.le_trans(List.length(&2, Bool, xs), p, 1n+p, hp, N.le_succ(p)))) : {Word.xor(1n+p, P.constant(1n+p, x), P.times_x(1n+p, low, _)) == wof(1n+p, x <> xs) : Word(1n+p)}
      %Equal.sym(Bool, P.top(1n+p, wof(1n+p, xs)), False{}, top_short(p, xs, hp)) : {Word.xor(1n+p, P.constant(1n+p, x), Word.xor(1n+p, P.wscale(1n+p, _, low), Word.shl(1n+p, wof(1n+p, xs)))) == wof(1n+p, x <> xs) : Word(1n+p)}
      %Equal.sym(Word(1n+p), Word.xor(1n+p, Word.zero(1n+p), Word.shl(1n+p, wof(1n+p, xs))), Word.shl(1n+p, wof(1n+p, xs)), xor_zero_l(1n+p, Word.shl(1n+p, wof(1n+p, xs)))) : {Word.xor(1n+p, P.constant(1n+p, x), _) == wof(1n+p, x <> xs) : Word(1n+p)}
      %Equal.sym(Word(1n+p), Word.shl(1n+p, wof(1n+p, xs)), wof(1n+p, False{} <> xs), shl_wof(1n+p, xs)) : {Word.xor(1n+p, P.constant(1n+p, x), _) == wof(1n+p, x <> xs) : Word(1n+p)}
      %Equal.sym(Word(p), Word.xor(p, Word.zero(p), wof(p, xs)), wof(p, xs), xor_zero_l(p, wof(p, xs))) : {WCon{Bool.xor(x, False{}), _} == wof(1n+p, x <> xs) : Word(1n+p)}
      %Equal.sym(Bool, Bool.xor(x, False{}), x, bxor_false(x)) : {WCon{_, wof(p, xs)} == wof(1n+p, x <> xs) : Word(1n+p)}
      {==}

def wof_coefficients(+n: Nat, +w: Word(n)) -> {wof(n, P.coefficients(n, w)) == w : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      %wof_coefficients(p, t) : {WCon{b, wof(p, P.coefficients(p, t))} == WCon{b, _} : Word(1n+p)}
      {==}

def coefficients_le(+n: Nat, +w: Word(n)) -> {Nat.is_le(List.length(&2, Bool, P.coefficients(n, w)), n) == True{} : Bool}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      coefficients_le(p, t)

def red_coefficients(+n: Nat, +low: Word(n), +w: Word(n)) -> {P.reduce(n, low, P.coefficients(n, w)) == w : Word(n)}:
  Equal.trans(Word(n), P.reduce(n, low, P.coefficients(n, w)), wof(n, P.coefficients(n, w)), w,
    red_short(n, low, P.coefficients(n, w), coefficients_le(n, w)), wof_coefficients(n, w))

# The product of two residues, reduced, is Algorithm 1 from Z = 0.
def mul_sa(+n: Nat, +low: Word(n), +a: Word(n), +b: Word(n)) -> {P.reduce(n, low, P.mul(P.coefficients(n, a), P.coefficients(n, b))) == sa(n, low, P.coefficients(n, a), Word.zero(n), b) : Word(n)}:
  %Equal.sym(Word(n), sa(n, low, P.coefficients(n, a), Word.zero(n), b), Word.xor(n, Word.zero(n), sm(n, low, P.coefficients(n, a), b)), sa_sm(n, low, P.coefficients(n, a), Word.zero(n), b)) : {P.reduce(n, low, P.mul(P.coefficients(n, a), P.coefficients(n, b))) == _ : Word(n)}
  %Equal.sym(Word(n), Word.xor(n, Word.zero(n), sm(n, low, P.coefficients(n, a), b)), sm(n, low, P.coefficients(n, a), b), xor_zero_l(n, sm(n, low, P.coefficients(n, a), b))) : {P.reduce(n, low, P.mul(P.coefficients(n, a), P.coefficients(n, b))) == _ : Word(n)}
  %red_coefficients(n, low, b) : {P.reduce(n, low, P.mul(P.coefficients(n, a), P.coefficients(n, b))) == sm(n, low, P.coefficients(n, a), _) : Word(n)}
  red_mul(n, low, P.coefficients(n, a), P.coefficients(n, b))
