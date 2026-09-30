import Base
import ../../src/math/hash.bend as H
import ../../src/math/pow2.bend as P2
import ../support/text.bend as X
import ./lib.bend as L

# Backend-differential driver (tools/backend_diff.py): the Base primitives
# every library module is compiled down to, in the shapes that have been
# miscompiled before (bendlang/bend#1142: a U32 local used more than once and
# then converted to Nat). Every argv token "code:a:b" prints one line.
#
#   0:x:y     U32 arithmetic, bits, shifts, comparisons
#   1:x:y     U32 -> Nat conversions of reused locals, and back
#   2:a:b     Nat add / sub / compare / min / max        (a + b < 2^48)
#   3:a:b     Nat mul                                    (a * b < 2^48)
#   4:a:b     Nat div / mod / divmod
#   5:a:b     Nat.pow, U32.pow                           (a ^ b < 2^48)
#   6:text    Nat.read, U32.read
#   7:a:b     F32 arithmetic, rounding, comparisons (operands: decimal text)
#   8:a       F32.show
#   9:a:b     F32 library functions (exp, log, sin, pow, ...)
#   10:s:t    String functions
#   11:d:i:v  Array of 2^d slots: set / get / swap / size / to_list
#   12:n:k    List functions on n elements, recursion of depth n
#   13:x      U32.to_f32, F32.from_nat
#   14:a      F32.to_u32, F32.to_nat
#   15:c.c.c  a String built from the code points c (any U32 is a Char in
#             Bend; the string itself is never printed)
#   16:h:c    src/math/hash.bend (mix, fold, bucket) and src/math/pow2.bend

def cmp(c: Cmp) -> String:
  match c:
    case LT{}:
      "<"
    case EQ{}:
      "="
    case GT{}:
      ">"

def f32(s: String) -> F32:
  Maybe.default(&2, F32, F32.read(s), 0.0)

def fb(x: F32) -> String:
  U32.show(F32.bits(x))

def mnat(r: Maybe<&2, Nat>) -> String:
  match r:
    case None{}:
      "none"
    case Some{n}:
      Nat.show(n)

def mu32(r: Maybe<&2, U32>) -> String:
  match r:
    case None{}:
      "none"
    case Some{n}:
      U32.show(n)

def mchar(r: Maybe<&2, Char>) -> String:
  match r:
    case None{}:
      "none"
    case Some{Chr{c}}:
      U32.show(c)

def u32_ops(+x: U32, +y: U32) -> String:
  String.join([U32.show(U32.add(x, y)), U32.show(U32.sub(x, y)), U32.show(U32.mul(x, y)), U32.show(U32.div(x, y)), U32.show(U32.mod(x, y)), U32.show(U32.and(x, y)), U32.show(U32.or(x, y)), U32.show(U32.xor(x, y)), U32.show(U32.not(x)), U32.show(U32.inc(x)), U32.show(U32.shl(x)), U32.show(U32.shr(x)), U32.show(U32.min(x, y)), U32.show(U32.max(x, y)), cmp(U32.cmp(x, y)), L.bool(U32.is_lt(x, y)), L.bool(U32.is_le(x, y)), L.bool(U32.is_eq(x, y)), L.bool(U32.is_ne(x, y)), L.bool(U32.is_gt(x, y)), L.bool(U32.is_ge(x, y)), L.bool(U32.is_zero(y)), L.bool(U32.is_even(x)), Nat.show(U32.log2(x)), U32.show(U32.shln(x, U32.to_nat(U32.and(y, 63)))), U32.show(U32.shrn(x, U32.to_nat(U32.and(y, 63)))), U32.show(U32.pow(x, U32.to_nat(U32.and(y, 31)))), U32.show(U32.clamp(x, U32.min(y, U32.not(y)), U32.max(y, U32.not(y)))), U32.show((x * x + y * 3 - x / 7 : U32)), U32.show((x .&. y .|. x .^. y : U32))], " ")

def succ(+x: U32) -> Nat:
  1n+U32.to_nat(x)

def twice(+x: U32) -> Nat:
  Nat.add(U32.to_nat(x), U32.to_nat(x))

def wide(+x: U32, +y: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(U32.shrn(x, 16n)), U32.to_nat(y)), Nat.mul(U32.to_nat(U32.and(x, 65535)), U32.to_nat(U32.shrn(y, 16n))))

def nat_shapes(+x: U32, +y: U32) -> String:
  String.join([Nat.show(U32.to_nat(x)), Nat.show(succ(x)), Nat.show(Nat.add(U32.to_nat(x), 1n)), Nat.show((1n + U32.to_nat(x) : Nat)), Nat.show(twice(x)), Nat.show(Nat.add(U32.to_nat(x), U32.to_nat(y))), Nat.show(Nat.mul(U32.to_nat(x), 65536n)), Nat.show(Nat.mul(U32.to_nat(x), 65535n)), Nat.show(Nat.sub(U32.to_nat(x), U32.to_nat(y))), Nat.show(Nat.sub(U32.to_nat(y), U32.to_nat(x))), Nat.show(wide(x, y)), Nat.show(Nat.div(U32.to_nat(x), U32.to_nat(y))), Nat.show(Nat.mod(U32.to_nat(x), U32.to_nat(y))), Nat.show(Nat.div(Nat.mul(U32.to_nat(x), 65536n), 1n+U32.to_nat(y))), U32.show(U32.from_nat(U32.to_nat(x))), U32.show(U32.from_nat(succ(x))), U32.show(U32.from_nat(Nat.add(U32.to_nat(x), U32.to_nat(y)))), U32.show(U32.from_nat(Nat.mul(U32.to_nat(x), 65535n))), U32.show(U32.from_nat(twice(x))), cmp(Nat.cmp(succ(x), U32.to_nat(y))), L.bool(Nat.is_lt(U32.to_nat(x), succ(y))), Nat.show(Nat.max(succ(x), twice(y))), Nat.show(Nat.min(succ(x), twice(y)))], " ")

def nat_add(+a: Nat, +b: Nat) -> String:
  String.join([Nat.show(Nat.add(a, b)), Nat.show(Nat.sub(a, b)), Nat.show(Nat.sub(b, a)), cmp(Nat.cmp(a, b)), Nat.show(Nat.min(a, b)), Nat.show(Nat.max(a, b)), L.bool(Nat.is_lt(a, b)), L.bool(Nat.is_le(a, b)), L.bool(Nat.is_eq(a, b)), L.bool(Nat.is_ne(a, b)), L.bool(Nat.is_gt(a, b)), L.bool(Nat.is_ge(a, b)), U32.show(U32.from_nat(a)), U32.show(U32.from_nat(Nat.add(a, b))), Nat.show((a + b - a : Nat)), Nat.show(Nat.sub(Nat.add(a, b), b))], " ")

def nat_mul(+a: Nat, +b: Nat) -> String:
  String.join([Nat.show(Nat.mul(a, b)), Nat.show(Nat.mul(b, a)), U32.show(U32.from_nat(Nat.mul(a, b))), Nat.show(Nat.div(Nat.mul(a, b), 1n+b)), U32.show(U32.mul(U32.from_nat(a), U32.from_nat(b)))], " ")

def qr(r: Nat & Nat) -> String:
  (q, m) = r
  Nat.show(q) ++ "," ++ Nat.show(m)

def nat_div(+a: Nat, +b: Nat) -> String:
  String.join([Nat.show(Nat.div(a, b)), Nat.show(Nat.mod(a, b)), qr(Nat.divmod(a, b)), Nat.show(Nat.div(b, a)), Nat.show(Nat.mod(b, a)), Nat.show((a / b + a % b : Nat))], " ")

def nat_pow(+a: Nat, +b: Nat) -> String:
  String.join([Nat.show(Nat.pow(a, b)), U32.show(U32.pow(U32.from_nat(a), b))], " ")

def reads(+s: String) -> String:
  String.join([mnat(Nat.read(s)), mu32(U32.read(s))], " ")

def f32_ops(+a: F32, +b: F32) -> String:
  String.join([fb(a), fb(b), fb(F32.add(a, b)), fb(F32.sub(a, b)), fb(F32.mul(a, b)), fb(F32.div(a, b)), fb(F32.neg(a)), fb(F32.abs(a)), fb(F32.sqrt(a)), fb(F32.floor(a)), fb(F32.ceil(a)), fb(F32.trunc(a)), fb(F32.round(a)), fb(F32.min(a, b)), fb(F32.max(a, b)), fb(F32.square(a)), L.bool(F32.is_eq(a, b)), L.bool(F32.is_ne(a, b)), L.bool(F32.is_lt(a, b)), L.bool(F32.is_le(a, b)), L.bool(F32.is_gt(a, b)), L.bool(F32.is_ge(a, b)), fb((a * b + a - b / a : F32))], " ")

def f32_lib(+a: F32, +b: F32) -> String:
  String.join([fb(F32.mod(a, b)), fb(F32.pow(a, b)), fb(F32.atan2(a, b)), fb(F32.exp(a)), fb(F32.log(a)), fb(F32.log2(a)), fb(F32.log10(a)), fb(F32.sin(a)), fb(F32.cos(a)), fb(F32.tan(a)), fb(F32.asin(a)), fb(F32.acos(a)), fb(F32.atan(a)), fb(F32.sinh(a)), fb(F32.cosh(a)), fb(F32.tanh(a)), fb(F32.hypot(a, b)), fb(F32.lerp(a, b, 0.25))], " ")

def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, codes(t)}

def strings(+s: String, +t: String) -> String:
  String.join([Nat.show(String.length(s)), X.join_u32(codes(s)), String.reverse(s), String.to_upper(s), String.to_lower(s), L.bool(String.eq(s, t)), cmp(String.order(s, t)), L.bool(String.is_lt(s, t)), L.bool(String.starts_with(s, t)), L.bool(String.ends_with(s, t)), L.bool(String.contains(s, t)), String.take(s, 2n), String.drop(s, 2n), mchar(String.get(s, 1n)), String.join(String.split(s, 'a'), "|"), String.repeat(t, 3n), String.trim(s), s ++ t], " ")

def cps(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Chr{X.u32_of(h)}, cps(t)}

def chars(+s: String) -> String:
  String.join([Nat.show(String.length(s)), X.join_u32(codes(s)), L.bool(String.eq(s, s)), cmp(String.order(s, "a")), X.join_u32(codes(String.reverse(s)))], " ")

def mathx(+h: U32, +c: U32) -> String:
  String.join([U32.show(H.mix(h, c)), U32.show(H.fold(h, c)), U32.show(H.bucket(h, c)), Nat.show(P2.pow2t(U32.to_nat(U32.mod(c, 48))))], " ")

def share(xs: List<&1, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{h, share(t)}

def arr5(+g: U32, +g2: U32, +n: U32, r: Array<U32> & U32) -> String:
  (a, old) = r
  String.join([U32.show(g), U32.show(g2), U32.show(n), U32.show(old), X.join_u32(share(Array.to_list(~U32, a)))], " ")

def arr4(+i: U32, +g: U32, +g2: U32, r: Array<U32> & U32) -> String:
  (a, +n) = r
  arr5(g, g2, n, Array.swap(U32, a, U32.sub(i, 1), 9))

def arr3(+i: U32, +g: U32, r: Array<U32> & U32) -> String:
  (a, +g2) = r
  arr4(i, g, g2, Array.size(U32, a))

def arr2(+i: U32, r: Array<U32> & U32) -> String:
  (a, +g) = r
  arr3(i, g, Array.get(U32, a, U32.add(i, 1)))

def arrays(+d: Nat, +i: U32, +v: U32) -> String:
  arr2(i, Array.get(U32, Array.set(U32, Array.new(U32, d, 7), i, v), i))

def sum(xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum(t, Nat.add(acc, h))

def deep(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+deep(p)

def lists(+n: Nat, +k: Nat) -> String:
  String.join([Nat.show(sum(List.range(n), 0n)), Nat.show(List.length(&2, Nat, List.range(n))), mnat(List.head(&2, Nat, List.reverse(&2, Nat, List.range(n)))), mnat(List.last(&2, Nat, List.range(n))), mnat(List.get(&2, Nat, List.range(n), k)), Nat.show(List.length(&2, U32, List.replicate(U32, n, 5))), Nat.show(sum(List.take(&2, Nat, List.range(n), k), 0n)), Nat.show(sum(List.drop(&2, Nat, List.range(n), k), 0n)), Nat.show(sum(List.append(&2, Nat, List.range(k), List.range(n)), 0n)), Nat.show(deep(n))], " ")

def run(code: Nat, +p: List<&2, String>) -> String:
  match code:
    case 0n:
      u32_ops(X.u32_field(p, 1n), X.u32_field(p, 2n))
    case 1n:
      nat_shapes(X.u32_field(p, 1n), X.u32_field(p, 2n))
    case 2n:
      nat_add(X.nat_field(p, 1n), X.nat_field(p, 2n))
    case 3n:
      nat_mul(X.nat_field(p, 1n), X.nat_field(p, 2n))
    case 4n:
      nat_div(X.nat_field(p, 1n), X.nat_field(p, 2n))
    case 5n:
      nat_pow(X.nat_field(p, 1n), X.nat_field(p, 2n))
    case 6n:
      reads(X.field(p, 1n))
    case 7n:
      f32_ops(f32(X.field(p, 1n)), f32(X.field(p, 2n)))
    case 8n:
      F32.show(f32(X.field(p, 1n)))
    case 9n:
      f32_lib(f32(X.field(p, 1n)), f32(X.field(p, 2n)))
    case 10n:
      strings(X.field(p, 1n), X.field(p, 2n))
    case 11n:
      arrays(X.nat_field(p, 1n), X.u32_field(p, 2n), X.u32_field(p, 3n))
    case 12n:
      lists(X.nat_field(p, 1n), X.nat_field(p, 2n))
    case 13n:
      fb(U32.to_f32(X.u32_field(p, 1n))) ++ " " ++ fb(F32.from_nat(X.nat_field(p, 1n)))
    case 14n:
      U32.show(F32.to_u32(f32(X.field(p, 1n)))) ++ " " ++ Nat.show(F32.to_nat(f32(X.field(p, 1n))))
    case 15n:
      chars(cps(String.split(X.field(p, 1n), '.')))
    case 16n:
      mathx(X.u32_field(p, 1n), X.u32_field(p, 2n))
    case 17n+x:
      "?"

def line(s: String) -> String:
  +p = X.fields(s)
  run(X.nat_field(p, 0n), p)

def all(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{line(h), all(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(all(X.program_args(args)))
