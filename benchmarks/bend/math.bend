import Base
import ../../src/math/natural.bend as M

# src/math/natural.bend throughput: COUNT calls of MATH_OP on arguments from
# the MINSTD generator (r := 48271 r mod (2^31 - 1), two draws per call),
# every result folded into a checksum c := (31 c + result) mod (2^31 - 1).
# Prints BENCH_MS=<ms> and the checksum; benchmarks/native/math.c does the
# same in C. The `loop` op times the generator and the fold alone.

def ok(r: Result<&2, &2, M.MathError, Nat>) -> Nat:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      0n

def qr(r: Result<&2, &2, M.MathError, M.QuotRem>) -> Nat:
  match r:
    case Done{M.QR{q, m}}:
      Nat.add(q, m)
    case Fail{e}:
      0n

def next(+r: Nat) -> Nat:
  Nat.mod(Nat.mul(r, 48271n), 2147483647n)

def fold(+c: Nat, +v: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mul(c, 31n), Nat.mod(v, 2147483647n)), 2147483647n)

def step_loop(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, Nat.add(x, y))

def loop_loop(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_loop(p, next(next(r)), step_loop(c, next(r), next(next(r))))

def step_gcd(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.gcd(x, y))

def loop_gcd(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_gcd(p, next(next(r)), step_gcd(c, next(r), next(next(r))))

def step_lcm(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.lcm(Nat.mod(x, 1048576n), Nat.mod(y, 1048576n)))

def loop_lcm(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_lcm(p, next(next(r)), step_lcm(c, next(r), next(next(r))))

def step_isqrt(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.isqrt(x))

def loop_isqrt(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_isqrt(p, next(next(r)), step_isqrt(c, next(r), next(next(r))))

def step_iroot3(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, ok(M.iroot(x, 3n)))

def loop_iroot3(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_iroot3(p, next(next(r)), step_iroot3(c, next(r), next(next(r))))

def step_ilog10(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, ok(M.ilog(1n+x, 10n)))

def loop_ilog10(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_ilog10(p, next(next(r)), step_ilog10(c, next(r), next(next(r))))

def step_bit_length(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.bit_length(x))

def loop_bit_length(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_bit_length(p, next(next(r)), step_bit_length(c, next(r), next(next(r))))

def step_factorial(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.factorial(Nat.mod(x, 13n)))

def loop_factorial(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_factorial(p, next(next(r)), step_factorial(c, next(r), next(next(r))))

def step_perm(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.perm(Nat.mod(x, 16n), Nat.mod(y, 17n)))

def loop_perm(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_perm(p, next(next(r)), step_perm(c, next(r), next(next(r))))

def step_comb(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, M.comb(Nat.mod(x, 41n), Nat.mod(y, 42n)))

def loop_comb(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_comb(p, next(next(r)), step_comb(c, next(r), next(next(r))))

def step_pow_mod(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, ok(M.pow_mod(Nat.mod(x, 1048576n), Nat.mod(y, 1048576n), 1n+Nat.mod(Nat.add(x, y), 16777215n))))

def loop_pow_mod(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_pow_mod(p, next(next(r)), step_pow_mod(c, next(r), next(next(r))))

def step_mod_inverse(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, ok(M.mod_inverse(Nat.mod(x, 16777216n), 16777213n)))

def loop_mod_inverse(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_mod_inverse(p, next(next(r)), step_mod_inverse(c, next(r), next(next(r))))

def step_divmod(+c: Nat, +x: Nat, +y: Nat) -> Nat:
  fold(c, qr(M.divmod(x, 1n+Nat.mod(y, 1048576n))))

def loop_divmod(k: Nat, +r: Nat, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      loop_divmod(p, next(next(r)), step_divmod(c, next(r), next(next(r))))

def number(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{}:
      0n
    case Some{n}:
      n

def names() -> List<&2, String>:
  Con{"loop", Con{"gcd", Con{"lcm", Con{"isqrt", Con{"iroot3", Con{"ilog10", Con{"bit_length", Con{"factorial", Con{"perm", Con{"comb", Con{"pow_mod", Con{"mod_inverse", Con{"divmod", Nil{}}}}}}}}}}}}}}

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

def run(code: Nat, +count: Nat) -> Nat:
  match code:
    case 0n:
      loop_loop(count, 12345n, 0n)
    case 1n:
      loop_gcd(count, 12345n, 0n)
    case 2n:
      loop_lcm(count, 12345n, 0n)
    case 3n:
      loop_isqrt(count, 12345n, 0n)
    case 4n:
      loop_iroot3(count, 12345n, 0n)
    case 5n:
      loop_ilog10(count, 12345n, 0n)
    case 6n:
      loop_bit_length(count, 12345n, 0n)
    case 7n:
      loop_factorial(count, 12345n, 0n)
    case 8n:
      loop_perm(count, 12345n, 0n)
    case 9n:
      loop_comb(count, 12345n, 0n)
    case 10n:
      loop_pow_mod(count, 12345n, 0n)
    case 11n:
      loop_mod_inverse(count, 12345n, 0n)
    case 12n:
      loop_divmod(count, 12345n, 0n)
    case 13n+z:
      0n

def main() -> IO(Unit):
  do IO<Unit>:
    ot : String <- IO.try(String, IO.get_env("MATH_OP"))
    nt : String <- IO.try(String, IO.get_env("MATH_COUNT"))
    +count : Nat = number(Nat.read(nt))
    +code : Nat = index_go(names(), ot, 0n, 99n)
    start : Nat <- IO.now()
    +result : Nat = run(code, count)
    stop : Nat <- IO.now()
    IO.print("BENCH_MS=" ++ Nat.show(Nat.sub(stop, start)))
    IO.print(Nat.show(result))
