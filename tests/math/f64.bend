import Base
import ../../src/math/f64.bend as F
import ../support/text.bend as X

def read_parts(xs: List<&2, String>) -> F.F64:
  match xs:
    case Con{h, Con{l, t}}:
      F.of_bits(X.u32_of(h), X.u32_of(l))
    case _:
      F.zero(False{})

# Differential driver for the software binary64: argv token "op:x:y" with
# each operand its bit pattern "hi_lo" (two decimal words) prints the result
# the same way (booleans as 1/0); tools/check_f64.py compares with the
# machine's doubles.

def read(s: String) -> F.F64:
  read_parts(String.split(s, '_'))

def show_w(+x: F.F64) -> String:
  U32.show(F.word_hi(x)) ++ "_" ++ U32.show(F.word_lo(x))

def show(x: F.F64) -> String:
  show_w(x)

def b(v: Bool) -> String:
  match v:
    case True{}:
      "1"
    case False{}:
      "0"

def hit_eq(+i: Nat, +acc: Nat, same: Bool) -> Nat:
  match same:
    case True{}:
      i
    case False{}:
      acc

def hit(+a: String, +b: String, +i: Nat, +acc: Nat) -> Nat:
  hit_eq(i, acc, String.eq(a, b))

def pick(+op: String) -> Nat:
  hit(op, "add", 0n, hit(op, "sub", 1n, hit(op, "mul", 2n, hit(op, "div", 3n, hit(op, "sqrt", 4n, hit(op, "lt", 5n, hit(op, "le", 6n, hit(op, "eq", 7n, hit(op, "neg", 8n, hit(op, "abs", 9n, hit(op, "copysign", 10n, hit(op, "of_nat", 11n, 99n))))))))))))

def run_code(code: Nat, +x: F.F64, +y: F.F64, +n: Nat) -> String:
  match code:
    case 0n:
      show(F.add(x, y))
    case 1n:
      show(F.sub(x, y))
    case 2n:
      show(F.mul(x, y))
    case 3n:
      show(F.div(x, y))
    case 4n:
      show(F.sqrt(x))
    case 5n:
      b(F.lt(x, y))
    case 6n:
      b(F.le(x, y))
    case 7n:
      b(F.eq(x, y))
    case 8n:
      show(F.neg(x))
    case 9n:
      show(F.abs(x))
    case 10n:
      show(F.copysign(x, y))
    case 11n:
      show(F.of_nat(n))
    case _:
      "?"

def run(+op: String, +x: F.F64, +y: F.F64, +n: Nat) -> String:
  run_code(pick(op), x, y, n)

def case_parts(+parts: List<&2, String>) -> String:
  run(X.field(parts, 0n), read(X.field(parts, 1n)), read(X.field(parts, 2n)), X.nat_field(parts, 1n))

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
