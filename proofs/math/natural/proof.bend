import Base
import ../../../src/math/natural.bend as M
import ../../../spec/lib/common.bend as SC
import ../../../spec/math/natural.bend as S
import ./arith.bend as R
import ./gcd.bend as G
import ./lcm.bend as LC
import ./fact.bend as F
import ./bits.bend as B
import ./roots.bend as RT
import ./sqrtn.bend as SQ
import ./logs.bend as LG
import ./modpow.bend as MP
import ./inverse.bend as IV
import ./lists.bend as LS
import ./misc.bend as MS


# src/math/natural.bend against its specification spec/math/natural.bend:
# one definition per contract clause, under the clause's name, typed by the
# clause. Divisibility is dvd(d, a): the quotient and the equation. The
# reference proofs each module mirrors are cited in its file (Lean 4
# Mathlib, the Why3 gallery, HACL*); none assumes a hole or an axiom.

# the value of a successful result, 0 on an error
def res_val(r: Result<&2, &2, M.MathError, Nat>) -> Nat:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      0n

# a result that is Done twice holds one value
def done_eq(+t: Result<&2, &2, M.MathError, Nat>, +a: Nat, +b: Nat, +ha: {t == Done{a} : Result<&2, &2, M.MathError, Nat>}, +hb: {t == Done{b} : Result<&2, &2, M.MathError, Nat>}) -> {a == b : Nat}:
  Equal.cong(Result<&2, &2, M.MathError, Nat>, Nat, res_val, Done{a}, Done{b}, Equal.trans(Result<&2, &2, M.MathError, Nat>, Done{a}, t, Done{b}, Equal.sym(Result<&2, &2, M.MathError, Nat>, t, Done{a}, ha), hb))

# ---- gcd, lcm ----

def divides_left(+a: Nat, +b: Nat) -> S.Gcd.divides_left(a, b):
  (G.wl(G.ws(b, a, b)), G.gcd_dvd_left(a, b))

def divides_right(+a: Nat, +b: Nat) -> S.Gcd.divides_right(a, b):
  (G.wr(G.ws(b, a, b)), G.gcd_dvd_right(a, b))

def greatest(+a: Nat, +b: Nat, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {b == Nat.mul(kb, d) : Nat}) -> S.Gcd.greatest(a, b, d, ka, kb, ea, eb):
  (G.dw(b, a, b, ka, kb), G.dvd_gcd(a, b, d, ka, kb, ea, eb))

def mul_left(+c: Nat, +a: Nat, +b: Nat) -> S.Gcd.mul_left(c, a, b):
  LC.gcd_mul_left(c, a, b)

def lcm_divides_left(+a: Nat, +b: Nat) -> S.Lcm.divides_left(a, b):
  (LC.lcm_wl(a, b), LC.dvd_lcm_left(a, b))

def lcm_divides_right(+a: Nat, +b: Nat) -> S.Lcm.divides_right(a, b):
  (LC.lcm_wr(a, b), LC.dvd_lcm_right(a, b))

def least(+a: Nat, +b: Nat, +m: Nat, +x: Nat, +y: Nat, +ex: {m == Nat.mul(x, a) : Nat}, +ey: {m == Nat.mul(y, b) : Nat}) -> S.Lcm.least(a, b, m, x, y, ex, ey):
  (LC.lcm_dw(a, b, m, x, y), LC.lcm_dvd(a, b, m, x, y, ex, ey))

def gcd_mul_lcm(+a: Nat, +b: Nat) -> S.Lcm.gcd_mul_lcm(a, b):
  LC.gcd_mul_lcm(a, b)

# ---- lists ----

def gcd_all_divides(+xs: List<&2, Nat>, +i: Nat) -> S.GcdAll.divides(xs, i):
  (LS.gw_nth(xs, 0n, i), LS.gcd_all_dvd(xs, i))

def gcd_all_greatest(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: S.dvd_with(d, xs, ks)) -> S.GcdAll.greatest(d, xs, ks, h):
  (LS.gw_dvd(xs, ks, 0n, 0n), LS.dvd_gcd_all(d, xs, ks, h))

def lcm_all_divides(+xs: List<&2, Nat>, +i: Nat) -> S.LcmAll.divides(xs, i):
  (LS.lw_nth(xs, 1n, i), LS.dvd_lcm_all(xs, i))

def lcm_all_least(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: S.mul_with(m, xs, ks)) -> S.LcmAll.least(m, xs, ks, h):
  (LS.lw_mul(m, xs, ks, 1n, m), LS.lcm_all_dvd(m, xs, ks, h))

def sum_value(+xs: List<&2, Nat>) -> S.Sum.value(xs):
  LS.sum_ok(xs)

def prod_value(+xs: List<&2, Nat>) -> S.Prod.value(xs):
  LS.prod_ok(xs)

# ---- factorial, perm, comb ----

def factorial_value(+n: Nat) -> S.Factorial.value(n):
  F.factorial_ok(n)

def perm_value(+n: Nat, +k: Nat) -> S.Perm.value(n, k):
  F.perm_ok(n, k)

def perm_self(+n: Nat) -> S.Perm.self(n):
  Equal.trans(Nat, M.perm(n, n), S.desc(n, n), S.factorial(n), F.perm_ok(n, n), F.desc_self(n))

def comb_value(+n: Nat, +k: Nat) -> S.Comb.value(n, k):
  F.comb_ok(n, k)

def pascal(+m: Nat, +j: Nat) -> S.Comb.pascal(m, j):
  %Equal.sym(Nat, M.comb(m, j), S.choose(m, j), F.comb_ok(m, j)) : {M.comb(1n+m, 1n+j) == Nat.add(_, M.comb(m, 1n+j)) : Nat}
  %Equal.sym(Nat, M.comb(m, 1n+j), S.choose(m, 1n+j), F.comb_ok(m, 1n+j)) : {M.comb(1n+m, 1n+j) == Nat.add(S.choose(m, j), _) : Nat}
  F.comb_ok(1n+m, 1n+j)

def factorials(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> S.Comb.factorials(n, k, h):
  %Equal.sym(Nat, M.comb(n, k), S.choose(n, k), F.comb_ok(n, k)) : {Nat.mul(_, Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))) == S.factorial(n) : Nat}
  F.choose_mul_facts(n, k, h)

def comb_zero(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, k) == True{} : Bool}) -> S.Comb.zero(n, k, h):
  Equal.trans(Nat, M.comb(n, k), S.choose(n, k), 0n, F.comb_ok(n, k), F.choose_eq_zero(n, k, h))

# ---- roots, logarithms, bits ----

def isqrt_le(+n: Nat) -> S.Isqrt.le(n):
  SQ.isqrt_le(n)

def isqrt_lt_succ(+n: Nat) -> S.Isqrt.lt_succ(n):
  SQ.lt_succ_isqrt(n)

def iroot_done(+n: Nat, +kp: Nat) -> S.Iroot.done(n, kp):
  (M.iroot_k(n, 1n+kp), RT.iroot_done(n, kp))

def iroot_value(+n: Nat, +kp: Nat, +r: Nat, +h: {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> {M.iroot_k(n, 1n+kp) == r : Nat}:
  done_eq(M.iroot(n, 1n+kp), M.iroot_k(n, 1n+kp), r, RT.iroot_done(n, kp), h)

def iroot_le(+n: Nat, +kp: Nat, +r: Nat, +h: {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> S.Iroot.le(n, kp, r, h):
  %iroot_value(n, kp, r, h) : {Nat.is_le(Nat.pow(_, 1n+kp), n) == True{} : Bool}
  RT.iroot_le(n, kp)

def iroot_lt_succ(+n: Nat, +kp: Nat, +r: Nat, +h: {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> S.Iroot.lt_succ(n, kp, r, h):
  %iroot_value(n, kp, r, h) : {Nat.is_lt(n, Nat.pow(1n+_, 1n+kp)) == True{} : Bool}
  RT.lt_succ_iroot(n, kp)

def zero_degree(+n: Nat) -> S.Iroot.zero_degree(n):
  RT.iroot_zero(n)

def ilog_done(+np: Nat, +bq: Nat) -> S.Ilog.done(np, bq):
  (LG.ilog_value(np, bq), LG.ilog_done(np, bq))

def ilog_value(+np: Nat, +bq: Nat, +r: Nat, +h: {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> {LG.ilog_value(np, bq) == r : Nat}:
  done_eq(M.ilog(1n+np, 2n+bq), LG.ilog_value(np, bq), r, LG.ilog_done(np, bq), h)

def pow_le(+np: Nat, +bq: Nat, +r: Nat, +h: {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> S.Ilog.pow_le(np, bq, r, h):
  %ilog_value(np, bq, r, h) : {Nat.is_le(Nat.pow(2n+bq, _), 1n+np) == True{} : Bool}
  LG.pow_ilog_le(np, bq)

def lt_pow_succ(+np: Nat, +bq: Nat, +r: Nat, +h: {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> S.Ilog.lt_pow_succ(np, bq, r, h):
  %ilog_value(np, bq, r, h) : {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+_)) == True{} : Bool}
  LG.lt_pow_succ_ilog(np, bq)

def ilog_zero(+b: Nat) -> S.Ilog.zero(b):
  LG.ilog_zero(b)

def small_base(+n: Nat, +b: Nat, +hb: {Nat.is_lt(b, 2n) == True{} : Bool}) -> S.Ilog.small_base(n, b, hb):
  LG.ilog_small_base(n, b, hb)

def bit_length_lt(+n: Nat) -> S.BitLength.lt(n):
  B.bit_length_lt(n)

def bit_length_le(+np: Nat) -> S.BitLength.le(np):
  B.bit_length_le(np)

# ---- modular arithmetic ----

def pow_mod_value(+b: Nat, +e: Nat, +mp: Nat) -> S.PowMod.value(b, e, mp):
  MP.pow_mod_ok(b, e, mp)

def pow_mod_zero_modulus(+b: Nat, +e: Nat) -> S.PowMod.zero_modulus(b, e):
  MP.pow_mod_zero(b, e)

def inverse(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> S.ModInverse.inverse(a, mp, x, h):
  Pair.fst({Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat}, {Nat.is_lt(x, 1n+mp) == True{} : Bool}, IV.inverse_done(a, mp, x, h))

def reduced(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> S.ModInverse.reduced(a, mp, x, h):
  Pair.snd({Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat}, {Nat.is_lt(x, 1n+mp) == True{} : Bool}, IV.inverse_done(a, mp, x, h))

# the shared factor g >= 2 and its two quotients, as dvd pairs
def factor_parts(+a: Nat, +mp: Nat, +g: Nat, +ka: Nat, +km: Nat, p: {Nat.is_le(2n, g) == True{} : Bool} & ({a == Nat.mul(ka, g) : Nat} & {1n+mp == Nat.mul(km, g) : Nat})) -> {Nat.is_le(2n, g) == True{} : Bool} & (S.dvd(g, a) & S.dvd(g, 1n+mp)):
  (hg, rest) = p
  (ea, em) = rest
  (hg, ((ka, ea), (km, em)))

def not_coprime(+a: Nat, +mp: Nat, +h: {M.mod_inverse(a, 1n+mp) == Fail{M.NotInvertible{}} : Result<&2, &2, M.MathError, Nat>}) -> S.ModInverse.not_coprime(a, mp, h):
  (IV.bg(IV.inv_bz(a, mp)), factor_parts(a, mp, IV.bg(IV.inv_bz(a, mp)), IV.inv_ka(a, mp), IV.inv_km(a, mp), IV.inverse_fail(a, mp, h)))

def inverse_zero_modulus(+a: Nat) -> S.ModInverse.zero_modulus(a):
  IV.inverse_zero(a)

# ---- divmod and clamp ----

def divmod_value(+a: Nat, +bp: Nat) -> S.DivMod.value(a, bp):
  MS.divmod_done(a, bp)

def euclid(+a: Nat, +bp: Nat) -> S.DivMod.euclid(a, bp):
  MS.divmod_eq(a, bp)

def rem_lt(+a: Nat, +bp: Nat) -> S.DivMod.rem_lt(a, bp):
  MS.divmod_lt(a, bp)

def zero_divisor(+a: Nat) -> S.DivMod.zero_divisor(a):
  MS.divmod_zero(a)

def clamp_value(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> S.Clamp.value(x, lo, hi, h):
  MS.clamp_done(x, lo, hi, h)

def clamp_ge(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> S.Clamp.ge(x, lo, hi, h):
  MS.clamp_ge(x, lo, hi, h)

def clamp_le(+x: Nat, +lo: Nat, +hi: Nat) -> S.Clamp.le(x, lo, hi):
  MS.clamp_le(x, lo, hi)

def clamp_id(+x: Nat, +lo: Nat, +hi: Nat, +h1: {Nat.is_le(lo, x) == True{} : Bool}, +h2: {Nat.is_le(x, hi) == True{} : Bool}) -> S.Clamp.id(x, lo, hi, h1, h2):
  MS.clamp_id(x, lo, hi, h1, h2)

def domain(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(hi, lo) == True{} : Bool}) -> S.Clamp.domain(x, lo, hi, h):
  MS.clamp_domain(x, lo, hi, h)
