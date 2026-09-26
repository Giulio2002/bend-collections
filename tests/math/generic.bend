import Base
import ../../src/math/num.bend as N
import ../../src/math/generic.bend as G
import ../../src/math/instances.bend as I
import ../../src/math/u64.bend as W
import ../../src/math/f64.bend as F
import ../support/text.bend as X

# Differential driver for the templated math: argv token "type:op:a:b:c"
# (type u32, u64, f32 or f64; a u64 or an f64 is "hi_lo", its two words,
# an f32 a decimal literal) prints
# one result line, checked against Python by tools/check_generic.py. f32
# results print as their bit pattern; the driver runs the templates once per
# type, so the same code is exercised for every instance.

def err(e: N.NumError) -> String:
  match e:
    case N.DivByZero{}:
      "ZeroDivision"
    case N.BadDomain{}:
      "Domain"
    case N.NoInverse{}:
      "NotInvertible"
    case N.Overflow{}:
      "Overflow"

def res(~T: Data, ~sh: T -> String, r: Result<&2, &2, N.NumError, T>) -> String:
  match r:
    case Done{x}:
      sh(x)
    case Fail{e}:
      err(e)

def res_nat(r: Result<&2, &2, N.NumError, Nat>) -> String:
  match r:
    case Done{x}:
      Nat.show(x)
    case Fail{e}:
      err(e)

def qr(~T: Data, ~sh: T -> String, r: Result<&2, &2, N.NumError, G.QuotRem<T>>) -> String:
  match r:
    case Done{G.TQR{q, m}}:
      sh(q) ++ "," ++ sh(m)
    case Fail{e}:
      err(e)

def vals(~T: Data, ~rd: String -> T, xs: List<&2, String>) -> List<&2, T>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{rd(h), vals(~T, ~rd, t)}

def drop2(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Con{a, Con{b, t}}:
      t
    case _:
      Nil{}

def names() -> List<&2, String>:
  Con{"gcd", Con{"lcm", Con{"isqrt", Con{"iroot", Con{"ilog", Con{"factorial", Con{"perm", Con{"comb", Con{"pow_mod", Con{"mod_inverse", Con{"divmod", Con{"bit_length", Con{"clamp", Con{"gcd_all", Con{"lcm_all", Con{"prod", Con{"sum", Con{"min", Con{"max", Con{"abs", Con{"sign", Con{"pow", Nil{}}}}}}}}}}}}}}}}}}}}}}}

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

def op_code(+op: String) -> Nat:
  index_go(names(), op, 0n, 99n)

# the ordered-ring functions (every type)
def run_ord(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~sh: T -> String, ~rd: String -> T, code: Nat, +parts: List<&2, String>) -> String:
  match code:
    case 12n:
      res(~T, ~sh, G.clamp(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n)), rd(X.field(parts, 4n))))
    case 15n:
      res(~T, ~sh, G.prod(~T, ~op, ~test, vals(~T, ~rd, drop2(parts))))
    case 16n:
      res(~T, ~sh, G.sum(~T, ~op, ~test, vals(~T, ~rd, drop2(parts))))
    case 17n:
      sh(G.min(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 18n:
      sh(G.max(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 19n:
      sh(G.abs(~T, ~op, ~test, rd(X.field(parts, 2n))))
    case 20n:
      sh(G.sign(~T, ~op, ~test, rd(X.field(parts, 2n))))
    case 21n:
      res(~T, ~sh, G.pow(~T, ~op, ~test, rd(X.field(parts, 2n)), X.nat_field(parts, 3n)))
    case _:
      "?"

# the integer functions, then the ordered-ring ones
def run_int(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, ~sh: T -> String, ~rd: String -> T, code: Nat, +parts: List<&2, String>) -> String:
  match code:
    case 0n:
      sh(G.gcd(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 1n:
      res(~T, ~sh, G.lcm(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 2n:
      sh(G.isqrt(~T, ~op, ~test, rd(X.field(parts, 2n))))
    case 3n:
      res(~T, ~sh, G.iroot(~T, ~op, ~test, rd(X.field(parts, 2n)), X.nat_field(parts, 3n)))
    case 4n:
      res_nat(G.ilog(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 5n:
      res(~T, ~sh, G.factorial(~T, ~op, ~test, rd(X.field(parts, 2n))))
    case 6n:
      res(~T, ~sh, G.perm(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 7n:
      res(~T, ~sh, G.comb(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 8n:
      res(~T, ~sh, G.pow_mod(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n)), rd(X.field(parts, 4n))))
    case 9n:
      res(~T, ~sh, G.mod_inverse(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 10n:
      qr(~T, ~sh, G.divmod(~T, ~op, ~test, rd(X.field(parts, 2n)), rd(X.field(parts, 3n))))
    case 11n:
      Nat.show(G.bit_length(~T, ~op, ~test, rd(X.field(parts, 2n))))
    case 13n:
      sh(G.gcd_all(~T, ~op, ~test, vals(~T, ~rd, drop2(parts))))
    case 14n:
      res(~T, ~sh, G.lcm_all(~T, ~op, ~test, vals(~T, ~rd, drop2(parts))))
    case _:
      run_ord(~T, ~op, ~test, ~sh, ~rd, code, parts)

def u64_show(a: W.U64) -> String:
  match a:
    case W.U64{lo, hi}:
      U32.show(hi) ++ "_" ++ U32.show(lo)

def u64_parts(xs: List<&2, String>) -> W.U64:
  match xs:
    case Con{h, Con{l, t}}:
      W.U64{X.u32_of(l), X.u32_of(h)}
    case _:
      W.U64{0, 0}

def u64_read(s: String) -> W.U64:
  u64_parts(String.split(s, '_'))

def f32_show(x: F32) -> String:
  U32.show(F32.bits(x))

def f32_read(s: String) -> F32:
  Maybe.default(&2, F32, F32.read(s), 0.0)

def f64_show_w(+x: F.F64) -> String:
  U32.show(F.word_hi(x)) ++ "_" ++ U32.show(F.word_lo(x))

def f64_show(x: F.F64) -> String:
  f64_show_w(x)

def f64_parts(xs: List<&2, String>) -> F.F64:
  match xs:
    case Con{h, Con{l, t}}:
      F.of_bits(X.u32_of(h), X.u32_of(l))
    case _:
      F.zero(False{})

def f64_read(s: String) -> F.F64:
  f64_parts(String.split(s, '_'))

def case_pick(t: Nat, +parts: List<&2, String>) -> String:
  match t:
    case 1n:
      run_int(~U32, ~I.u32_op, ~I.u32_is, ~U32.show, ~X.u32_of, op_code(X.field(parts, 1n)), parts)
    case 2n:
      run_int(~W.U64, ~I.u64_op, ~I.u64_is, ~u64_show, ~u64_read, op_code(X.field(parts, 1n)), parts)
    case 3n:
      run_ord(~F32, ~I.f32_op, ~I.f32_is, ~f32_show, ~f32_read, op_code(X.field(parts, 1n)), parts)
    case 4n:
      run_ord(~F.F64, ~F.f64_op, ~F.f64_is, ~f64_show, ~f64_read, op_code(X.field(parts, 1n)), parts)
    case _:
      "?"

def ty_code(+ty: String) -> Nat:
  pick_i(String.eq(ty, "f64"), 4n, pick_i(String.eq(ty, "f32"), 3n, pick_i(String.eq(ty, "u64"), 2n, pick_i(String.eq(ty, "u32"), 1n, 0n))))

def case_ty(+ty: String, +parts: List<&2, String>) -> String:
  case_pick(ty_code(ty), parts)

def case_parts(+parts: List<&2, String>) -> String:
  case_ty(X.field(parts, 0n), parts)

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
    X.print_lines(all(X.shared(args)))
