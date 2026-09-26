import Base
import ../../src/math/num.bend as N
import ../../src/math/generic.bend as G
import ../../src/math/instances.bend as I
import ../../src/math/u64.bend as W
import ../../src/math/w64.bend as X
import ../../src/math/f64.bend as F

# The templated math per type: COUNT calls of TYPED_OP on arguments drawn
# from the MINSTD generator (as benchmarks/bend/math.bend), each result folded
# into the checksum (an error result folds as 0; a u64 as its value mod
# 2^31 - 1, a float as its bit pattern). benchmarks/native/typed.c does the
# same with uint32_t, uint64_t, float and double. One loop, instantiated per
# operation through a template.

def next(+r: Nat) -> Nat:
  Nat.mod(Nat.mul(r, 48271n), 2147483647n)

def fold(+c: Nat, +v: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mul(c, 31n), Nat.mod(v, 2147483647n)), 2147483647n)

def loop(~f: Nat -> Nat -> Nat, k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop(~f, p, next(next(r)), fold(c, f(next(r), next(next(r)))))

def two32() -> Nat:
  Nat.add(4294967295n, 1n)

def ok(-T: Data, +z: T, r: Result<&2, &2, N.NumError, T>) -> T:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      z

def okn(r: Result<&2, &2, N.NumError, Nat>) -> Nat:
  ok(Nat, 0n, r)

# ---- u32 ----

def u(+n: Nat) -> U32:
  U32.from_nat(n)

def v32(+x: U32) -> Nat:
  U32.to_nat(x)

def u32_gcd(+x: Nat, +y: Nat) -> Nat:
  v32(G.gcd(~U32, ~I.u32_op, ~I.u32_is, u(x), u(y)))

def u32_isqrt(+x: Nat, +y: Nat) -> Nat:
  v32(G.isqrt(~U32, ~I.u32_op, ~I.u32_is, u(Nat.add(Nat.mul(x, 2n), Nat.mod(y, 2n)))))

def u32_comb(+x: Nat, +y: Nat) -> Nat:
  v32(ok(U32, 0, G.comb(~U32, ~I.u32_op, ~I.u32_is, u(Nat.mod(x, 41n)), u(Nat.mod(y, 42n)))))

def u32_factorial(+x: Nat, +y: Nat) -> Nat:
  v32(ok(U32, 0, G.factorial(~U32, ~I.u32_op, ~I.u32_is, u(Nat.mod(x, 14n)))))

def u32_pow_mod(+x: Nat, +y: Nat) -> Nat:
  v32(ok(U32, 0, G.pow_mod(~U32, ~I.u32_op, ~I.u32_is, u(x), u(y), u(Nat.add(1n, Nat.mod(Nat.add(x, y), 4294967295n))))))

# ---- u64: a = x 2^32 + y, b = y 2^32 + x ----

def w(+hi: Nat, +lo: Nat) -> W.U64:
  W.U64{U32.from_nat(lo), U32.from_nat(hi)}

def v64(+a: W.U64) -> Nat:
  Nat.add(Nat.mul(Nat.mod(U32.to_nat(X.hi(a)), 2147483647n), 2n), U32.to_nat(X.lo(a)))

def u64_gcd(+x: Nat, +y: Nat) -> Nat:
  v64(G.gcd(~W.U64, ~I.u64_op, ~I.u64_is, w(x, y), w(y, x)))

def u64_isqrt(+x: Nat, +y: Nat) -> Nat:
  v64(G.isqrt(~W.U64, ~I.u64_op, ~I.u64_is, w(Nat.mul(x, 2n), y)))

def u64_comb(+x: Nat, +y: Nat) -> Nat:
  v64(ok(W.U64, W.U64{0, 0}, G.comb(~W.U64, ~I.u64_op, ~I.u64_is, w(0n, Nat.mod(x, 68n)), w(0n, Nat.mod(y, 69n)))))

def u64_factorial(+x: Nat, +y: Nat) -> Nat:
  v64(ok(W.U64, W.U64{0, 0}, G.factorial(~W.U64, ~I.u64_op, ~I.u64_is, w(0n, Nat.mod(x, 22n)))))

def u64_pow_mod(+x: Nat, +y: Nat) -> Nat:
  v64(ok(W.U64, W.U64{0, 0}, G.pow_mod(~W.U64, ~I.u64_op, ~I.u64_is, w(x, y), w(0n, y), w(y, Nat.add(Nat.mul(Nat.div(x, 2n), 2n), 1n)))))

# ---- f32: v = (x mod 1000) / 7 ----

def fv(+x: Nat) -> F32:
  F32.div(F32.from_nat(Nat.mod(x, 1000n)), 7.0)

def vf(+a: F32) -> Nat:
  U32.to_nat(F32.bits(a))

def f32_pow(+x: Nat, +y: Nat) -> Nat:
  vf(ok(F32, 0.0, G.pow(~F32, ~I.f32_op, ~I.f32_is, fv(x), Nat.mod(y, 16n))))

def f32_clamp(+x: Nat, +y: Nat) -> Nat:
  vf(ok(F32, 0.0, G.clamp(~F32, ~I.f32_op, ~I.f32_is, fv(x), fv(y), F32.add(fv(y), 50.0))))

# ---- f64: a in [1, 2) and b in [2, 4) from their bits ----

def da(+x: Nat, +y: Nat) -> F.F64:
  F.of_bits(U32.from_nat(Nat.add(1072693248n, Nat.mod(x, 1048576n))), U32.from_nat(y))

def db(+x: Nat, +y: Nat) -> F.F64:
  F.of_bits(U32.from_nat(Nat.add(1073741824n, Nat.mod(y, 1048576n))), U32.from_nat(x))

def vd(+a: F.F64) -> Nat:
  Nat.add(Nat.mul(Nat.mod(U32.to_nat(F.word_hi(a)), 2147483647n), 2n), U32.to_nat(F.word_lo(a)))

def f64_add(+x: Nat, +y: Nat) -> Nat:
  vd(F.add(da(x, y), db(x, y)))

def f64_mul(+x: Nat, +y: Nat) -> Nat:
  vd(F.mul(da(x, y), db(x, y)))

def f64_div(+x: Nat, +y: Nat) -> Nat:
  vd(F.div(da(x, y), db(x, y)))

def f64_sqrt(+x: Nat, +y: Nat) -> Nat:
  vd(F.sqrt(db(x, y)))

def f64_pow(+x: Nat, +y: Nat) -> Nat:
  vd(ok(F.F64, F.zero(False{}), G.pow(~F.F64, ~F.f64_op, ~F.f64_is, da(x, y), Nat.mod(y, 16n))))

def f64_loop(+x: Nat, +y: Nat) -> Nat:
  vd(da(x, y))

# ---- dispatch ----

def names() -> List<&2, String>:
  Con{"u32_gcd", Con{"u32_isqrt", Con{"u32_comb", Con{"u32_factorial", Con{"u32_pow_mod", Con{"u64_gcd", Con{"u64_isqrt", Con{"u64_comb", Con{"u64_factorial", Con{"u64_pow_mod", Con{"f32_pow", Con{"f32_clamp", Con{"f64_add", Con{"f64_mul", Con{"f64_div", Con{"f64_sqrt", Con{"f64_pow", Con{"loop", Nil{}}}}}}}}}}}}}}}}}}}

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

def run(code: Nat, +k: Nat) -> Nat:
  match code:
    case 0n:
      loop(~(x => y => u32_gcd(x, y)), k, 12345n, 0n)
    case 1n:
      loop(~(x => y => u32_isqrt(x, y)), k, 12345n, 0n)
    case 2n:
      loop(~(x => y => u32_comb(x, y)), k, 12345n, 0n)
    case 3n:
      loop(~(x => y => u32_factorial(x, y)), k, 12345n, 0n)
    case 4n:
      loop(~(x => y => u32_pow_mod(x, y)), k, 12345n, 0n)
    case 5n:
      loop(~(x => y => u64_gcd(x, y)), k, 12345n, 0n)
    case 6n:
      loop(~(x => y => u64_isqrt(x, y)), k, 12345n, 0n)
    case 7n:
      loop(~(x => y => u64_comb(x, y)), k, 12345n, 0n)
    case 8n:
      loop(~(x => y => u64_factorial(x, y)), k, 12345n, 0n)
    case 9n:
      loop(~(x => y => u64_pow_mod(x, y)), k, 12345n, 0n)
    case 10n:
      loop(~(x => y => f32_pow(x, y)), k, 12345n, 0n)
    case 11n:
      loop(~(x => y => f32_clamp(x, y)), k, 12345n, 0n)
    case 12n:
      loop(~(x => y => f64_add(x, y)), k, 12345n, 0n)
    case 13n:
      loop(~(x => y => f64_mul(x, y)), k, 12345n, 0n)
    case 14n:
      loop(~(x => y => f64_div(x, y)), k, 12345n, 0n)
    case 15n:
      loop(~(x => y => f64_sqrt(x, y)), k, 12345n, 0n)
    case 16n:
      loop(~(x => y => f64_pow(x, y)), k, 12345n, 0n)
    case 17n:
      loop(~(x => y => f64_loop(x, y)), k, 12345n, 0n)
    case _:
      0n

def number(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      n

def main() -> IO(Unit):
  do IO<Unit>:
    ot : String <- IO.try(String, IO.get_env("TYPED_OP"))
    nt : String <- IO.try(String, IO.get_env("TYPED_COUNT"))
    +count : Nat = number(Nat.read(nt))
    +code : Nat = index_go(names(), ot, 0n, 99n)
    start : Nat <- IO.now()
    +result : Nat = run(code, count)
    stop : Nat <- IO.now()
    IO.print("BENCH_MS=" ++ Nat.show(Nat.sub(stop, start)))
    IO.print(Nat.show(result))
