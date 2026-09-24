import Base
import ../../src/math/natural.bend as M
import ../support/text.bend as X

# Differential driver: every argv token "op:a:b:c" prints one result line,
# checked against CPython's math/builtins by tools/check_math.py.

def res(r: Result<&2, &2, M.MathError, Nat>) -> String:
  match r:
    case Done{x}:
      Nat.show(x)
    case Fail{M.ZeroDivision{}}:
      "ZeroDivision"
    case Fail{M.Domain{}}:
      "Domain"
    case Fail{M.NotInvertible{}}:
      "NotInvertible"

def qr(r: Result<&2, &2, M.MathError, M.QuotRem>) -> String:
  match r:
    case Done{M.QR{q, m}}:
      Nat.show(q) ++ "," ++ Nat.show(m)
    case Fail{e}:
      "ZeroDivision"

def nats(xs: List<&2, String>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.nat_of(h), nats(t)}

def tail(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def names() -> List<&2, String>:
  Con{"gcd", Con{"lcm", Con{"isqrt", Con{"iroot", Con{"ilog", Con{"factorial", Con{"perm", Con{"comb", Con{"pow_mod", Con{"mod_inverse", Con{"divmod", Con{"bit_length", Con{"clamp", Con{"gcd_all", Con{"lcm_all", Con{"prod", Con{"sum", Nil{}}}}}}}}}}}}}}}}}}

def pick_i(+hit: Bool, +i: Nat, +acc: Nat) -> Nat:
  match hit:
    case True{}:
      i
    case False{}:
      acc

def index_go(xs: List<&2, String>, +op: String, +i: Nat, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      index_go(t, op, 1n+i, pick_i(String.eq(h, op), i, acc))

def run(code: Nat, +parts: List<&2, String>, +a: Nat, +b: Nat, +c: Nat) -> String:
  match code:
    case 0n:
      Nat.show(M.gcd(a, b))
    case 1n:
      Nat.show(M.lcm(a, b))
    case 2n:
      Nat.show(M.isqrt(a))
    case 3n:
      res(M.iroot(a, b))
    case 4n:
      res(M.ilog(a, b))
    case 5n:
      Nat.show(M.factorial(a))
    case 6n:
      Nat.show(M.perm(a, b))
    case 7n:
      Nat.show(M.comb(a, b))
    case 8n:
      res(M.pow_mod(a, b, c))
    case 9n:
      res(M.mod_inverse(a, b))
    case 10n:
      qr(M.divmod(a, b))
    case 11n:
      Nat.show(M.bit_length(a))
    case 12n:
      res(M.clamp(a, b, c))
    case 13n:
      Nat.show(M.gcd_all(nats(tail(parts))))
    case 14n:
      Nat.show(M.lcm_all(nats(tail(parts))))
    case 15n:
      Nat.show(M.prod(nats(tail(parts))))
    case 16n:
      Nat.show(M.sum(nats(tail(parts))))
    case 17n+x:
      "?"

def case2(+parts: List<&2, String>) -> String:
  run(index_go(names(), X.field(parts, 0n), 0n, 99n), parts, X.nat_field(parts, 1n), X.nat_field(parts, 2n), X.nat_field(parts, 3n))

def case1(s: String) -> String:
  case2(X.fields(s))

def all(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{case1(h), all(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(all(X.shared(args)))
