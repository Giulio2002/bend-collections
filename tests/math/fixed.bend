import Base
import ../../src/math/fixed.bend as F
import ../../src/math/number.bend as NB
import ../../src/math/u64.bend as W
import ../support/text.bend as X

# Differential driver for src/math/fixed.bend and src/math/number.bend:
# argv token "type:op:a:b" (type u32, u64 or nat; a u64 is "hi_lo"; shift
# amounts and pow exponents are U32; a byte list is "b0.b1.b2...") prints one
# result line, checked by tools/check_fixed.py against Python (with Rust's
# u32/u64 semantics). Maybe prints "None" or the value, an overflowing result
# "value,flag".

def bshow(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def opt(~T: Data, ~sh: T -> String, r: Maybe<&2, T>) -> String:
  match r:
    case Some{x}:
      sh(x)
    case None{}:
      "None"

def ov(~T: Data, ~sh: T -> String, r: F.Over<T>) -> String:
  match r:
    case F.OV{v, f}:
      sh(v) ++ "," ++ bshow(f)

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

def u32s(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.u32_of(h), u32s(t)}

def bytes(s: String) -> List<&2, U32>:
  u32s(String.split(s, '.'))

def names() -> List<&2, String>:
  Con{"checked_add", Con{"checked_sub", Con{"checked_mul", Con{"checked_div", Con{"checked_rem", Con{"checked_pow", Con{"checked_shl", Con{"checked_shr", Con{"wrapping_add", Con{"wrapping_sub", Con{"wrapping_mul", Con{"wrapping_pow", Con{"wrapping_shl", Con{"wrapping_shr", Con{"saturating_add", Con{"saturating_sub", Con{"saturating_mul", Con{"saturating_pow", Con{"overflowing_add", Con{"overflowing_sub", Con{"overflowing_mul", Con{"overflowing_pow", Con{"overflowing_shl", Con{"overflowing_shr", Con{"bit_count", Con{"is_prime", Con{"next_prime", Con{"to_bytes_le", Con{"to_bytes_be", Con{"from_bytes_le", Con{"from_bytes_be", Con{"egcd", Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

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

def run_u32(code: Nat, +parts: List<&2, String>) -> String:
  match code:
    case 0n:
      opt(~U32, ~U32.show, F.u32_checked_add(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 1n:
      opt(~U32, ~U32.show, F.u32_checked_sub(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 2n:
      opt(~U32, ~U32.show, F.u32_checked_mul(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 3n:
      opt(~U32, ~U32.show, F.u32_checked_div(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 4n:
      opt(~U32, ~U32.show, F.u32_checked_rem(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 5n:
      opt(~U32, ~U32.show, F.u32_checked_pow(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 6n:
      opt(~U32, ~U32.show, F.u32_checked_shl(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 7n:
      opt(~U32, ~U32.show, F.u32_checked_shr(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 8n:
      U32.show(F.u32_wrapping_add(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 9n:
      U32.show(F.u32_wrapping_sub(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 10n:
      U32.show(F.u32_wrapping_mul(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 11n:
      U32.show(F.u32_wrapping_pow(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 12n:
      U32.show(F.u32_wrapping_shl(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 13n:
      U32.show(F.u32_wrapping_shr(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 14n:
      U32.show(F.u32_saturating_add(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 15n:
      U32.show(F.u32_saturating_sub(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 16n:
      U32.show(F.u32_saturating_mul(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 17n:
      U32.show(F.u32_saturating_pow(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 18n:
      ov(~U32, ~U32.show, F.u32_overflowing_add(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 19n:
      ov(~U32, ~U32.show, F.u32_overflowing_sub(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 20n:
      ov(~U32, ~U32.show, F.u32_overflowing_mul(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 21n:
      ov(~U32, ~U32.show, F.u32_overflowing_pow(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 22n:
      ov(~U32, ~U32.show, F.u32_overflowing_shl(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 23n:
      ov(~U32, ~U32.show, F.u32_overflowing_shr(X.u32_of(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 24n:
      Nat.show(F.u32_bit_count(X.u32_of(X.field(parts, 2n))))
    case 25n:
      bshow(F.u32_is_prime(X.u32_of(X.field(parts, 2n))))
    case 26n:
      opt(~U32, ~U32.show, F.u32_next_prime(X.u32_of(X.field(parts, 2n))))
    case 27n:
      X.join_u32(F.u32_to_bytes_le(X.u32_of(X.field(parts, 2n))))
    case 28n:
      X.join_u32(F.u32_to_bytes_be(X.u32_of(X.field(parts, 2n))))
    case 29n:
      opt(~U32, ~U32.show, F.u32_from_bytes_le(bytes(X.field(parts, 2n))))
    case 30n:
      opt(~U32, ~U32.show, F.u32_from_bytes_be(bytes(X.field(parts, 2n))))
    case _:
      "?"

def run_u64(code: Nat, +parts: List<&2, String>) -> String:
  match code:
    case 0n:
      opt(~W.U64, ~u64_show, F.u64_checked_add(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 1n:
      opt(~W.U64, ~u64_show, F.u64_checked_sub(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 2n:
      opt(~W.U64, ~u64_show, F.u64_checked_mul(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 3n:
      opt(~W.U64, ~u64_show, F.u64_checked_div(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 4n:
      opt(~W.U64, ~u64_show, F.u64_checked_rem(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 5n:
      opt(~W.U64, ~u64_show, F.u64_checked_pow(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 6n:
      opt(~W.U64, ~u64_show, F.u64_checked_shl(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 7n:
      opt(~W.U64, ~u64_show, F.u64_checked_shr(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 8n:
      u64_show(F.u64_wrapping_add(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 9n:
      u64_show(F.u64_wrapping_sub(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 10n:
      u64_show(F.u64_wrapping_mul(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 11n:
      u64_show(F.u64_wrapping_pow(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 12n:
      u64_show(F.u64_wrapping_shl(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 13n:
      u64_show(F.u64_wrapping_shr(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 14n:
      u64_show(F.u64_saturating_add(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 15n:
      u64_show(F.u64_saturating_sub(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 16n:
      u64_show(F.u64_saturating_mul(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 17n:
      u64_show(F.u64_saturating_pow(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 18n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_add(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 19n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_sub(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 20n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_mul(u64_read(X.field(parts, 2n)), u64_read(X.field(parts, 3n))))
    case 21n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_pow(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 22n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_shl(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 23n:
      ov(~W.U64, ~u64_show, F.u64_overflowing_shr(u64_read(X.field(parts, 2n)), X.u32_of(X.field(parts, 3n))))
    case 24n:
      Nat.show(F.u64_bit_count(u64_read(X.field(parts, 2n))))
    case 27n:
      X.join_u32(F.u64_to_bytes_le(u64_read(X.field(parts, 2n))))
    case 28n:
      X.join_u32(F.u64_to_bytes_be(u64_read(X.field(parts, 2n))))
    case 29n:
      opt(~W.U64, ~u64_show, F.u64_from_bytes_le(bytes(X.field(parts, 2n))))
    case 30n:
      opt(~W.U64, ~u64_show, F.u64_from_bytes_be(bytes(X.field(parts, 2n))))
    case _:
      "?"

def eg_show(r: NB.EGcd) -> String:
  match r:
    case NB.EG{g, x, y, n}:
      Nat.show(g) ++ "," ++ Nat.show(x) ++ "," ++ Nat.show(y) ++ "," ++ bshow(n)

def run_nat(code: Nat, +parts: List<&2, String>) -> String:
  match code:
    case 24n:
      Nat.show(NB.bit_count(X.nat_field(parts, 2n)))
    case 25n:
      bshow(NB.is_prime(X.nat_field(parts, 2n)))
    case 31n:
      eg_show(NB.egcd(X.nat_field(parts, 2n), X.nat_field(parts, 3n)))
    case _:
      "?"

def case_pick(t: Nat, +parts: List<&2, String>) -> String:
  match t:
    case 1n:
      run_u32(op_code(X.field(parts, 1n)), parts)
    case 2n:
      run_u64(op_code(X.field(parts, 1n)), parts)
    case 3n:
      run_nat(op_code(X.field(parts, 1n)), parts)
    case _:
      "?"

def ty_code(+ty: String) -> Nat:
  pick_i(String.eq(ty, "nat"), 3n, pick_i(String.eq(ty, "u64"), 2n, pick_i(String.eq(ty, "u32"), 1n, 0n)))

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
    X.print_lines(all(X.program_args(args)))
