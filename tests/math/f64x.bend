import Base
import ../../src/math/f64.bend as F
import ../../src/math/u64.bend as W
import ../../src/math/num.bend as N
import ../support/text.bend as X

# Differential driver for the rounding, conversion, exponent, neighbour,
# remainder and ratio functions of the software binary64: argv token
# "op:a:b:c:d" with doubles as their bit patterns "hi_lo" (two decimal words)
# prints the result the same way; booleans print as 1/0, errors as E:dom or
# E:ovf, pairs joined by "|". tools/check_f64x.py compares with CPython.

def read_parts(xs: List<&2, String>) -> F.F64:
  match xs:
    case Con{h, Con{l, t}}:
      F.of_bits(X.u32_of(h), X.u32_of(l))
    case _:
      F.zero(False{})

def read(s: String) -> F.F64:
  read_parts(String.split(s, '_'))

def show(+x: F.F64) -> String:
  U32.show(F.word_hi(x)) ++ "_" ++ U32.show(F.word_lo(x))

def show_w(+w: W.U64) -> String:
  match w:
    case W.U64{l, h}:
      U32.show(h) ++ "_" ++ U32.show(l)

def b(v: Bool) -> String:
  match v:
    case True{}:
      "1"
    case False{}:
      "0"

def err(e: N.NumError) -> String:
  match e:
    case N.BadDomain{}:
      "E:dom"
    case N.Overflow{}:
      "E:ovf"
    case _:
      "E:?"

def show_r64(r: Result<&2, &2, N.NumError, W.U64>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{w}:
      show_w(w)

def show_r32(r: Result<&2, &2, N.NumError, U32>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{u}:
      U32.show(u)

def show_rb(r: Result<&2, &2, N.NumError, Bool>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{v}:
      b(v)

def show_exp(e: F.Exp) -> String:
  match e:
    case F.Exp{neg, mag}:
      b(neg) ++ "|" ++ Nat.show(mag)

def show_fx(p: F.F64 & F.Exp) -> String:
  (m, e) = p
  show(m) ++ "|" ++ show_exp(e)

def show_pair(p: F.F64 & F.F64) -> String:
  (a, c) = p
  show(a) ++ "|" ++ show(c)

def show_ratio(r: Result<&2, &2, N.NumError, F.Ratio>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{F.Ratio{neg, num, den}}:
      b(neg) ++ "|" ++ show_w(num) ++ "|" ++ Nat.show(den)

def to_w(+x: F.F64) -> W.U64:
  F.to_bits(x)

def hit_eq(+i: Nat, +acc: Nat, same: Bool) -> Nat:
  match same:
    case True{}:
      i
    case False{}:
      acc

def hit(+a: String, +c: String, +i: Nat, +acc: Nat) -> Nat:
  hit_eq(i, acc, String.eq(a, c))

def pick(+op: String) -> Nat:
  hit(op, "trunc", 0n, hit(op, "floor", 1n, hit(op, "ceil", 2n, hit(op, "round", 3n, hit(op, "to_u64", 4n, hit(op, "to_u32", 5n, hit(op, "of_u64", 6n, hit(op, "frexp", 7n, hit(op, "ldexp", 8n, hit(op, "ulp", 9n, hit(op, "nextafter", 10n, hit(op, "fmin", 11n, hit(op, "fmax", 12n, hit(op, "isnormal", 13n, hit(op, "issubnormal", 14n, hit(op, "is_integer", 15n, hit(op, "modf", 16n, hit(op, "fmod", 17n, hit(op, "remainder", 18n, hit(op, "isclose", 19n, hit(op, "ratio", 20n, hit(op, "floor_u64", 21n, hit(op, "ceil_u64", 22n, hit(op, "round_u64", 23n, hit(op, "bits", 24n, 99n)))))))))))))))))))))))))

def run_code(code: Nat, +x: F.F64, +y: F.F64, +z: F.F64, +t: F.F64, +neg: Bool, +k: Nat) -> String:
  match code:
    case 0n:
      show(F.trunc(x))
    case 1n:
      show(F.floor(x))
    case 2n:
      show(F.ceil(x))
    case 3n:
      show(F.round(x))
    case 4n:
      show_r64(F.to_u64(x))
    case 5n:
      show_r32(F.to_u32(x))
    case 6n:
      show(F.of_u64(to_w(x)))
    case 7n:
      show_fx(F.frexp(x))
    case 8n:
      show(F.ldexp(x, F.Exp{neg, k}))
    case 9n:
      show(F.ulp(x))
    case 10n:
      show(F.nextafter(x, y))
    case 11n:
      show(F.fmin(x, y))
    case 12n:
      show(F.fmax(x, y))
    case 13n:
      b(F.is_normal(x))
    case 14n:
      b(F.is_subnormal(x))
    case 15n:
      b(F.is_integer(x))
    case 16n:
      show_pair(F.modf(x))
    case 17n:
      show(F.fmod(x, y))
    case 18n:
      show(F.remainder(x, y))
    case 19n:
      show_rb(F.isclose(x, y, z, t))
    case 20n:
      show_ratio(F.as_integer_ratio(x))
    case 21n:
      show_r64(F.floor_u64(x))
    case 22n:
      show_r64(F.ceil_u64(x))
    case 23n:
      show_r64(F.round_u64(x))
    case 24n:
      show(F.of_bits64(F.to_bits(x)))
    case _:
      "?"

def nz(+n: Nat) -> Bool:
  Bool.not(Nat.is_eq(n, 0n))

def case_parts(+parts: List<&2, String>) -> String:
  run_code(pick(X.field(parts, 0n)), read(X.field(parts, 1n)), read(X.field(parts, 2n)), read(X.field(parts, 3n)), read(X.field(parts, 4n)), nz(X.nat_field(parts, 2n)), X.nat_field(parts, 3n))

def case1(s: String) -> String:
  case_parts(X.fields(s))

def all(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{case1(h), all(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(all(X.program_args(args)))
