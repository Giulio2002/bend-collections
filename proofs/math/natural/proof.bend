import Base
import ../../../src/math/natural.bend as M
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
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

# Gate for src/math/natural.bend: every public function against its
# specification. Divisibility is stated with explicit quotients (a == k d),
# so each "d divides a" names its k. Reference proofs whose statements
# these mirror are cited in each file (Lean 4 Mathlib, the Why3 gallery,
# HACL*); none assumes a hole or an axiom.

# ---- gcd, lcm (Mathlib Nat.gcd_dvd_left/right, Nat.dvd_gcd, Nat.gcd_mul_left,
# Nat.dvd_lcm_left/right, Nat.gcd_mul_lcm, Nat.lcm_dvd) ----

def gcd_dvd_left(+a: Nat, +b: Nat) -> {a == Nat.mul(G.wl(G.ws(b, a, b)), M.gcd(a, b)) : Nat}:
  G.gcd_dvd_left(a, b)

def gcd_dvd_right(+a: Nat, +b: Nat) -> {b == Nat.mul(G.wr(G.ws(b, a, b)), M.gcd(a, b)) : Nat}:
  G.gcd_dvd_right(a, b)

def dvd_gcd(+a: Nat, +b: Nat, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {b == Nat.mul(kb, d) : Nat}) -> {M.gcd(a, b) == Nat.mul(G.dw(b, a, b, ka, kb), d) : Nat}:
  G.dvd_gcd(a, b, d, ka, kb, ea, eb)

def gcd_mul_left(+c: Nat, +a: Nat, +b: Nat) -> {M.gcd(Nat.mul(c, a), Nat.mul(c, b)) == Nat.mul(c, M.gcd(a, b)) : Nat}:
  LC.gcd_mul_left(c, a, b)

def dvd_lcm_left(+a: Nat, +b: Nat) -> {M.lcm(a, b) == Nat.mul(LC.lcm_wl(a, b), a) : Nat}:
  LC.dvd_lcm_left(a, b)

def dvd_lcm_right(+a: Nat, +b: Nat) -> {M.lcm(a, b) == Nat.mul(LC.lcm_wr(a, b), b) : Nat}:
  LC.dvd_lcm_right(a, b)

def gcd_mul_lcm(+a: Nat, +b: Nat) -> {Nat.mul(M.gcd(a, b), M.lcm(a, b)) == Nat.mul(a, b) : Nat}:
  LC.gcd_mul_lcm(a, b)

def lcm_dvd(+a: Nat, +b: Nat, +m: Nat, +x: Nat, +y: Nat, +ex: {m == Nat.mul(x, a) : Nat}, +ey: {m == Nat.mul(y, b) : Nat}) -> {m == Nat.mul(LC.lcm_dw(a, b, m, x, y), M.lcm(a, b)) : Nat}:
  LC.lcm_dvd(a, b, m, x, y, ex, ey)

# ---- lists (Mathlib List.sum, List.prod, Finset.gcd_dvd, Finset.dvd_gcd,
# Finset.dvd_lcm, Finset.lcm_dvd) ----

def sum(+xs: List<&2, Nat>) -> {M.sum(xs) == S.lsum(xs) : Nat}:
  LS.sum_ok(xs)

def prod(+xs: List<&2, Nat>) -> {M.prod(xs) == S.lprod(xs) : Nat}:
  LS.prod_ok(xs)

def gcd_all_dvd(+xs: List<&2, Nat>, +i: Nat) -> {LS.nth0(xs, i, 0n) == Nat.mul(LS.gw_nth(xs, 0n, i), M.gcd_all(xs)) : Nat}:
  LS.gcd_all_dvd(xs, i)

def dvd_gcd_all(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: LS.dvd_with(d, xs, ks)) -> {M.gcd_all(xs) == Nat.mul(LS.gw_dvd(xs, ks, 0n, 0n), d) : Nat}:
  LS.dvd_gcd_all(d, xs, ks, h)

def dvd_lcm_all(+xs: List<&2, Nat>, +i: Nat) -> {M.lcm_all(xs) == Nat.mul(LS.lw_nth(xs, 1n, i), LS.nth0(xs, i, 1n)) : Nat}:
  LS.dvd_lcm_all(xs, i)

def lcm_all_dvd(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: LS.mul_with(m, xs, ks)) -> {m == Nat.mul(LS.lw_mul(m, xs, ks, 1n, m), M.lcm_all(xs)) : Nat}:
  LS.lcm_all_dvd(m, xs, ks, h)

# ---- factorial, perm, comb (Mathlib Nat.factorial, Nat.descFactorial,
# Nat.choose, Nat.choose_symm_diff, Nat.choose_mul_factorial_mul_factorial) ----

def factorial(+n: Nat) -> {M.factorial(n) == S.factorial(n) : Nat}:
  F.factorial_ok(n)

def perm(+n: Nat, +k: Nat) -> {M.perm(n, k) == S.desc(n, k) : Nat}:
  F.perm_ok(n, k)

def perm_self(+n: Nat) -> {M.perm(n, n) == S.factorial(n) : Nat}:
  Equal.trans(Nat, M.perm(n, n), S.desc(n, n), S.factorial(n), F.perm_ok(n, n), F.desc_self(n))

def comb(+n: Nat, +k: Nat) -> {M.comb(n, k) == S.choose(n, k) : Nat}:
  F.comb_ok(n, k)

def comb_factorials(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.mul(M.comb(n, k), Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))) == S.factorial(n) : Nat}:
  %Equal.sym(Nat, M.comb(n, k), S.choose(n, k), F.comb_ok(n, k)) : {Nat.mul(_, Nat.mul(S.factorial(k), S.factorial(Nat.sub(n, k)))) == S.factorial(n) : Nat}
  F.choose_mul_facts(n, k, h)

def comb_zero(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, k) == True{} : Bool}) -> {M.comb(n, k) == 0n : Nat}:
  Equal.trans(Nat, M.comb(n, k), S.choose(n, k), 0n, F.comb_ok(n, k), F.choose_eq_zero(n, k, h))

# ---- roots, logarithms, bits (Mathlib Nat.sqrt_le', Nat.lt_succ_sqrt',
# Nat.pow_log_le_self, Nat.lt_pow_succ_log_self, Nat.lt_size_self, Nat.size_le) ----

def isqrt_le(+n: Nat) -> {Nat.is_le(Nat.pow(M.isqrt(n), 2n), n) == True{} : Bool}:
  SQ.isqrt_le(n)

def lt_succ_isqrt(+n: Nat) -> {Nat.is_lt(n, Nat.pow(1n+M.isqrt(n), 2n)) == True{} : Bool}:
  SQ.lt_succ_isqrt(n)

def iroot_done(+n: Nat, +kp: Nat) -> {M.iroot(n, 1n+kp) == Done{M.iroot_k(n, 1n+kp)} : Result<&2, &2, M.MathError, Nat>}:
  RT.iroot_done(n, kp)

def iroot_le(+n: Nat, +kp: Nat) -> {Nat.is_le(Nat.pow(M.iroot_k(n, 1n+kp), 1n+kp), n) == True{} : Bool}:
  RT.iroot_le(n, kp)

def lt_succ_iroot(+n: Nat, +kp: Nat) -> {Nat.is_lt(n, Nat.pow(1n+M.iroot_k(n, 1n+kp), 1n+kp)) == True{} : Bool}:
  RT.lt_succ_iroot(n, kp)

def iroot_zero(+n: Nat) -> {M.iroot(n, 0n) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  RT.iroot_zero(n)

def ilog_done(+np: Nat, +bq: Nat) -> {M.ilog(1n+np, 2n+bq) == Done{LG.ilog_value(np, bq)} : Result<&2, &2, M.MathError, Nat>}:
  LG.ilog_done(np, bq)

def pow_ilog_le(+np: Nat, +bq: Nat) -> {Nat.is_le(Nat.pow(2n+bq, LG.ilog_value(np, bq)), 1n+np) == True{} : Bool}:
  LG.pow_ilog_le(np, bq)

def lt_pow_succ_ilog(+np: Nat, +bq: Nat) -> {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+LG.ilog_value(np, bq))) == True{} : Bool}:
  LG.lt_pow_succ_ilog(np, bq)

def ilog_zero(+b: Nat) -> {M.ilog(0n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  LG.ilog_zero(b)

def ilog_small_base(+n: Nat, +b: Nat, +hb: {Nat.is_lt(b, 2n) == True{} : Bool}) -> {M.ilog(n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  LG.ilog_small_base(n, b, hb)

def bit_length_lt(+n: Nat) -> {Nat.is_lt(n, SC.pow2(M.bit_length(n))) == True{} : Bool}:
  B.bit_length_lt(n)

def bit_length_le(+np: Nat) -> {Nat.is_le(SC.pow2(M.bit_length(1n+np)), Nat.double(1n+np)) == True{} : Bool}:
  B.bit_length_le(np)

# ---- modular arithmetic (Mathlib Nat.pow_mod; HACL* Lib.Exponentiation;
# Mathlib Nat.gcdA / ZMod.mul_inv_of_unit / Nat.Coprime) ----

def pow_mod(+b: Nat, +e: Nat, +mp: Nat) -> {M.pow_mod(b, e, 1n+mp) == Done{Nat.mod(Nat.pow(b, e), 1n+mp)} : Result<&2, &2, M.MathError, Nat>}:
  MP.pow_mod_ok(b, e, mp)

def pow_mod_zero(+b: Nat, +e: Nat) -> {M.pow_mod(b, e, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}:
  MP.pow_mod_zero(b, e)

def inverse_done(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat} & {Nat.is_lt(x, 1n+mp) == True{} : Bool}:
  IV.inverse_done(a, mp, x, h)

def inverse_fail(+a: Nat, +mp: Nat, +h: {M.mod_inverse(a, 1n+mp) == Fail{M.NotInvertible{}} : Result<&2, &2, M.MathError, Nat>}) -> {Nat.is_le(2n, IV.bg(IV.inv_bz(a, mp))) == True{} : Bool} & ({a == Nat.mul(IV.inv_ka(a, mp), IV.bg(IV.inv_bz(a, mp))) : Nat} & {1n+mp == Nat.mul(IV.inv_km(a, mp), IV.bg(IV.inv_bz(a, mp))) : Nat}):
  IV.inverse_fail(a, mp, h)

def inverse_zero(+a: Nat) -> {M.mod_inverse(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}:
  IV.inverse_zero(a)

# ---- divmod and clamp ----

def divmod(+a: Nat, +bp: Nat) -> {M.divmod(a, 1n+bp) == Done{M.QR{Nat.div(a, 1n+bp), Nat.mod(a, 1n+bp)}} : Result<&2, &2, M.MathError, M.QuotRem>}:
  MS.divmod_done(a, bp)

def divmod_eq(+a: Nat, +bp: Nat) -> {a == Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) : Nat}:
  MS.divmod_eq(a, bp)

def divmod_lt(+a: Nat, +bp: Nat) -> {Nat.is_lt(Nat.mod(a, 1n+bp), 1n+bp) == True{} : Bool}:
  MS.divmod_lt(a, bp)

def divmod_zero(+a: Nat) -> {M.divmod(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, M.QuotRem>}:
  MS.divmod_zero(a)

def clamp(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {M.clamp(x, lo, hi) == Done{Nat.min(Nat.max(x, lo), hi)} : Result<&2, &2, M.MathError, Nat>}:
  MS.clamp_done(x, lo, hi, h)

def clamp_ge(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.is_le(lo, Nat.min(Nat.max(x, lo), hi)) == True{} : Bool}:
  MS.clamp_ge(x, lo, hi, h)

def clamp_le(+x: Nat, +lo: Nat, +hi: Nat) -> {Nat.is_le(Nat.min(Nat.max(x, lo), hi), hi) == True{} : Bool}:
  MS.clamp_le(x, lo, hi)

def clamp_id(+x: Nat, +lo: Nat, +hi: Nat, +h1: {Nat.is_le(lo, x) == True{} : Bool}, +h2: {Nat.is_le(x, hi) == True{} : Bool}) -> {Nat.min(Nat.max(x, lo), hi) == x : Nat}:
  MS.clamp_id(x, lo, hi, h1, h2)

def clamp_domain(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(hi, lo) == True{} : Bool}) -> {M.clamp(x, lo, hi) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  MS.clamp_domain(x, lo, hi, h)
