import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/natural.bend as S
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/proof.bend as NP
import ../natural/lcm.bend as LC
import ../natural/gcd.bend as GD
import ../natural/arith.bend as NR
import ../natural/bits.bend as BT
import ./natfuel.bend as NF
import ../../lib/u32half.bend as UH
import ../natural/roots.bend as RT
import ../../lib/two_list.bend as TL
import ../natural/fact.bend as FA
import ../../lib/arith.bend as AR
import ../natural/misc.bend as MS

# gcd identities for the binary gcd (Stein; Knuth TAOCP vol. 2, 4.5.2,
# Algorithm B), each derived the way Mathlib does: two pairs with the same
# common divisors have the same gcd (Nat.gcd_eq_iff / Nat.dvd_antisymm).
#
#   gcd_eq       same common divisors -> same gcd
#   gcd_comm     gcd(a, b) = gcd(b, a)                  Nat.gcd_comm
#   gcd_sub      a <= b: gcd(a, b) = gcd(a, b - a)      Nat.gcd_sub_self_right
#   gcd_rec      b > 0: gcd(a, b) = gcd(b, a mod b)     Nat.gcd_rec
#   gcd_odd2     a odd: gcd(a, 2 m) = gcd(a, m)         Nat.Coprime.gcd_mul_left_cancel

def dvd2(+d: Nat, +u: Nat, +v: Nat) -> Type:
  S.dvd(d, u) & S.dvd(d, v)

# every common divisor of (x, y), given by its quotients, divides u and v
def Transfer(+x: Nat, +y: Nat, +u: Nat, +v: Nat) -> Type:
  @+d: Nat -> @+kx: Nat -> @+ky: Nat -> @+ex: {x == Nat.mul(kx, d) : Nat} -> @+ey: {y == Nat.mul(ky, d) : Nat} -> dvd2(d, u, v)

def into3(+g: Nat, +u: Nat, +v: Nat, du: S.dvd(g, u), dv: S.dvd(g, v)) -> S.dvd(g, M.gcd(u, v)):
  (ku, eu) = du
  (kv, ev) = dv
  NP.greatest(u, v, g, ku, kv, eu, ev)

def into2(+g: Nat, +u: Nat, +v: Nat, p: dvd2(g, u, v)) -> S.dvd(g, M.gcd(u, v)):
  (du, dv) = p
  into3(g, u, v, du, dv)

def into1(+x: Nat, +y: Nat, +u: Nat, +v: Nat, t: Transfer(x, y, u, v), dl: S.dvd(M.gcd(x, y), x), dr: S.dvd(M.gcd(x, y), y)) -> S.dvd(M.gcd(x, y), M.gcd(u, v)):
  (kx, ex) = dl
  (ky, ey) = dr
  into2(M.gcd(x, y), u, v, t(M.gcd(x, y), kx, ky, ex, ey))

def into(+x: Nat, +y: Nat, +u: Nat, +v: Nat, t: Transfer(x, y, u, v)) -> S.dvd(M.gcd(x, y), M.gcd(u, v)):
  into1(x, y, u, v, t, NP.divides_left(x, y), NP.divides_right(x, y))

def gcd_eq2(+x: Nat, +y: Nat, +u: Nat, +v: Nat, a: S.dvd(M.gcd(x, y), M.gcd(u, v)), b: S.dvd(M.gcd(u, v), M.gcd(x, y))) -> {M.gcd(x, y) == M.gcd(u, v) : Nat}:
  (k12, e12) = a
  (k21, e21) = b
  LC.dvd_antisymm(M.gcd(x, y), M.gcd(u, v), k21, k12, e21, e12)

def gcd_eq(+x: Nat, +y: Nat, +u: Nat, +v: Nat, t1: Transfer(x, y, u, v), t2: Transfer(u, v, x, y)) -> {M.gcd(x, y) == M.gcd(u, v) : Nat}:
  gcd_eq2(x, y, u, v, into(x, y, u, v, t1), into(u, v, x, y, t2))

def swap_t(+x: Nat, +y: Nat) -> Transfer(x, y, y, x):
  d => kx => ky => ex => ey => ((ky, ey), (kx, ex))

def gcd_comm(+a: Nat, +b: Nat) -> {M.gcd(a, b) == M.gcd(b, a) : Nat}:
  gcd_eq(a, b, b, a, swap_t(a, b), swap_t(b, a))

# ---- gcd(a, b) = gcd(a, b - a) for a <= b ----

def sub_t1_at(+a: Nat, +b: Nat, +d: Nat, +kx: Nat, +ky: Nat, +ex: {a == Nat.mul(kx, d) : Nat}, +ey: {b == Nat.mul(ky, d) : Nat}) -> dvd2(d, a, Nat.sub(b, a)):
  +e1 = Equal.cong(Nat, Nat, t => Nat.sub(t, a), b, Nat.mul(ky, d), ey)
  +e2 = Equal.cong(Nat, Nat, t => Nat.sub(Nat.mul(ky, d), t), a, Nat.mul(kx, d), ex)
  +e3 = Equal.sym(Nat, Nat.mul(Nat.sub(ky, kx), d), Nat.sub(Nat.mul(ky, d), Nat.mul(kx, d)), NR.mul_sub(ky, kx, d))
  ((kx, ex), (Nat.sub(ky, kx), Equal.trans(Nat, Nat.sub(b, a), Nat.sub(Nat.mul(ky, d), a), Nat.mul(Nat.sub(ky, kx), d), e1, Equal.trans(Nat, Nat.sub(Nat.mul(ky, d), a), Nat.sub(Nat.mul(ky, d), Nat.mul(kx, d)), Nat.mul(Nat.sub(ky, kx), d), e2, e3))))

def sub_t2_at(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}, +d: Nat, +kx: Nat, +kz: Nat, +ex: {a == Nat.mul(kx, d) : Nat}, +ez: {Nat.sub(b, a) == Nat.mul(kz, d) : Nat}) -> dvd2(d, a, b):
  +eb = Equal.trans(Nat, b, Nat.add(a, Nat.sub(b, a)), Nat.mul(Nat.add(kx, kz), d), Equal.sym(Nat, Nat.add(a, Nat.sub(b, a)), b, N.sub_add(b, a, h)), Equal.trans(Nat, Nat.add(a, Nat.sub(b, a)), Nat.add(Nat.mul(kx, d), Nat.mul(kz, d)), Nat.mul(Nat.add(kx, kz), d), Equal.trans(Nat, Nat.add(a, Nat.sub(b, a)), Nat.add(Nat.mul(kx, d), Nat.sub(b, a)), Nat.add(Nat.mul(kx, d), Nat.mul(kz, d)), Equal.cong(Nat, Nat, t => Nat.add(t, Nat.sub(b, a)), a, Nat.mul(kx, d), ex), Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(kx, d), t), Nat.sub(b, a), Nat.mul(kz, d), ez)), Equal.sym(Nat, Nat.mul(Nat.add(kx, kz), d), Nat.add(Nat.mul(kx, d), Nat.mul(kz, d)), NA.mul_add_right(kx, kz, d))))
  ((kx, ex), (Nat.add(kx, kz), eb))

def gcd_sub(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {M.gcd(a, b) == M.gcd(a, Nat.sub(b, a)) : Nat}:
  gcd_eq(a, b, a, Nat.sub(b, a), d => kx => ky => ex => ey => sub_t1_at(a, b, d, kx, ky, ex, ey), d => kx => kz => ex => ez => sub_t2_at(a, b, h, d, kx, kz, ex, ez))

# ---- Euclid's step: gcd(a, b) = gcd(b, a mod b) for b > 0 ----

def rec_t2_at(+a: Nat, +bp: Nat, +d: Nat, +kn: Nat, +kr: Nat, +en: {1n+bp == Nat.mul(kn, d) : Nat}, +er: {Nat.mod(a, 1n+bp) == Nat.mul(kr, d) : Nat}) -> dvd2(d, a, 1n+bp):
  ((Nat.add(Nat.mul(Nat.div(a, 1n+bp), kn), kr), GD.dvd_of_mod(bp, a, d, kn, kr, en, er)), (kn, en))

def gcd_rec(+a: Nat, +bp: Nat) -> {M.gcd(a, 1n+bp) == M.gcd(1n+bp, Nat.mod(a, 1n+bp)) : Nat}:
  gcd_eq(a, 1n+bp, 1n+bp, Nat.mod(a, 1n+bp), d => ka => kb => ea => eb => ((kb, eb), (Nat.sub(ka, Nat.mul(Nat.div(a, 1n+bp), kb)), GD.dvd_mod(bp, a, d, ka, kb, ea, eb))), d => kn => kr => en => er => rec_t2_at(a, bp, d, kn, kr, en, er))

# ---- parity ----

def odd(+n: Nat) -> Bool:
  Nat.is_eq(Nat.mod(n, 2n), 1n)

# 2q * d = 2 (q d)
def dmul(+q: Nat, +d: Nat) -> {Nat.mul(Nat.double(q), d) == Nat.double(Nat.mul(q, d)) : Nat}:
  +e1 = Equal.cong(Nat, Nat, t => Nat.mul(t, d), Nat.double(q), Nat.mul(2n, q), NA.double_mul(q))
  Equal.trans(Nat, Nat.mul(Nat.double(q), d), Nat.mul(Nat.mul(2n, q), d), Nat.double(Nat.mul(q, d)), e1, Equal.trans(Nat, Nat.mul(Nat.mul(2n, q), d), Nat.mul(2n, Nat.mul(q, d)), Nat.double(Nat.mul(q, d)), NA.mul_assoc(2n, q, d), Equal.sym(Nat, Nat.double(Nat.mul(q, d)), Nat.mul(2n, Nat.mul(q, d)), NA.double_mul(Nat.mul(q, d)))))

def even_form(+n: Nat, +h: {Nat.mod(n, 2n) == 0n : Nat}) -> {n == Nat.double(Nat.div(n, 2n)) : Nat}:
  +e = Equal.cong(Nat, Nat, t => Nat.add(Nat.double(Nat.div(n, 2n)), t), Nat.mod(n, 2n), 0n, h)
  Equal.trans(Nat, n, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), Nat.double(Nat.div(n, 2n)), BT.half_eq(n), Equal.trans(Nat, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), Nat.add(Nat.double(Nat.div(n, 2n)), 0n), Nat.double(Nat.div(n, 2n)), e, N.add_zero(Nat.double(Nat.div(n, 2n)))))

def odd_form(+n: Nat, +h: {Nat.mod(n, 2n) == 1n : Nat}) -> {n == 1n+Nat.double(Nat.div(n, 2n)) : Nat}:
  +e = Equal.cong(Nat, Nat, t => Nat.add(Nat.double(Nat.div(n, 2n)), t), Nat.mod(n, 2n), 1n, h)
  Equal.trans(Nat, n, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), 1n+Nat.double(Nat.div(n, 2n)), BT.half_eq(n), Equal.trans(Nat, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), Nat.add(Nat.double(Nat.div(n, 2n)), 1n), 1n+Nat.double(Nat.div(n, 2n)), e, N.add_comm(Nat.double(Nat.div(n, 2n)), 1n)))

def odd_eq(+n: Nat, +h: {odd(n) == True{} : Bool}) -> {Nat.mod(n, 2n) == 1n : Nat}:
  N.eq_from_is_eq(Nat.mod(n, 2n), 1n, h)

# n mod 2 is 0 or 1
def mod2_big(+n: Nat, +x: Nat, +hr: {Nat.mod(n, 2n) == 2n+x : Nat}) -> Empty:
  +c = Equal.cong(Nat, Bool, t => Nat.is_lt(t, 2n), Nat.mod(n, 2n), 2n+x, hr)
  N.lt_zero_absurd(x, Equal.trans(Bool, Nat.is_lt(2n+x, 2n), Nat.is_lt(Nat.mod(n, 2n), 2n), True{}, Equal.sym(Bool, Nat.is_lt(Nat.mod(n, 2n), 2n), Nat.is_lt(2n+x, 2n), c), BT.half_rem(n)))

# a divisor of an odd number is odd
def odd_dvd_r(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +d: Nat, +ka: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +r: Nat, +hr: {Nat.mod(d, 2n) == r : Nat}) -> {Nat.mod(d, 2n) == 1n : Nat}:
  match r:
    case 0n:
      +ed = even_form(d, hr)
      +e1 = Equal.trans(Nat, a, Nat.mul(ka, d), Nat.mul(ka, Nat.double(Nat.div(d, 2n))), ea, Equal.cong(Nat, Nat, t => Nat.mul(ka, t), d, Nat.double(Nat.div(d, 2n)), ed))
      +e2 = Equal.trans(Nat, Nat.mul(ka, Nat.double(Nat.div(d, 2n))), Nat.mul(Nat.double(Nat.div(d, 2n)), ka), Nat.double(Nat.mul(Nat.div(d, 2n), ka)), NA.mul_comm(ka, Nat.double(Nat.div(d, 2n))), dmul(Nat.div(d, 2n), ka))
      +e3 = Equal.trans(Nat, Nat.double(Nat.mul(Nat.div(d, 2n), ka)), a, 1n+Nat.double(Nat.div(a, 2n)), Equal.sym(Nat, a, Nat.double(Nat.mul(Nat.div(d, 2n), ka)), Equal.trans(Nat, a, Nat.mul(ka, Nat.double(Nat.div(d, 2n))), Nat.double(Nat.mul(Nat.div(d, 2n), ka)), e1, e2)), odd_form(a, ha))
      Empty.absurd({Nat.mod(d, 2n) == 1n : Nat}, N.even_odd(Nat.mul(Nat.div(d, 2n), ka), Nat.div(a, 2n), e3))
    case 1n:
      hr
    case 2n+x:
      Empty.absurd({Nat.mod(d, 2n) == 1n : Nat}, mod2_big(d, x, hr))

# an odd d dividing 2 m divides m
def odd2_m(+m: Nat, +d: Nat, +hd: {Nat.mod(d, 2n) == 1n : Nat}, +kb: Nat, +eb: {Nat.double(m) == Nat.mul(kb, d) : Nat}, +r: Nat, +hr: {Nat.mod(kb, 2n) == r : Nat}) -> S.dvd(d, m):
  match r:
    case 0n:
      +q = Nat.div(kb, 2n)
      +ek = even_form(kb, hr)
      +e1 = Equal.trans(Nat, Nat.double(m), Nat.mul(kb, d), Nat.double(Nat.mul(q, d)), eb, Equal.trans(Nat, Nat.mul(kb, d), Nat.mul(Nat.double(q), d), Nat.double(Nat.mul(q, d)), Equal.cong(Nat, Nat, t => Nat.mul(t, d), kb, Nat.double(q), ek), dmul(q, d)))
      (q, N.double_inj(m, Nat.mul(q, d), e1))
    case 1n:
      +q = Nat.div(kb, 2n)
      +p = Nat.div(d, 2n)
      +ek = odd_form(kb, hr)
      +ed = odd_form(d, hd)
      +e1 = Equal.trans(Nat, Nat.double(m), Nat.mul(kb, d), Nat.mul(1n+Nat.double(q), d), eb, Equal.cong(Nat, Nat, t => Nat.mul(t, d), kb, 1n+Nat.double(q), ek))
      +e2 = Equal.cong(Nat, Nat, t => Nat.add(d, t), Nat.mul(Nat.double(q), d), Nat.double(Nat.mul(q, d)), dmul(q, d))
      +e3 = Equal.cong(Nat, Nat, t => Nat.add(t, Nat.double(Nat.mul(q, d))), d, 1n+Nat.double(p), ed)
      +e4 = N.add_double(p, Nat.mul(q, d))
      +e5 = Equal.trans(Nat, Nat.double(m), Nat.add(d, Nat.double(Nat.mul(q, d))), 1n+Nat.double(Nat.add(p, Nat.mul(q, d))), Equal.trans(Nat, Nat.double(m), Nat.mul(1n+Nat.double(q), d), Nat.add(d, Nat.double(Nat.mul(q, d))), e1, e2), Equal.trans(Nat, Nat.add(d, Nat.double(Nat.mul(q, d))), 1n+Nat.add(Nat.double(p), Nat.double(Nat.mul(q, d))), 1n+Nat.double(Nat.add(p, Nat.mul(q, d))), e3, N.succ_cong(Nat.add(Nat.double(p), Nat.double(Nat.mul(q, d))), Nat.double(Nat.add(p, Nat.mul(q, d))), e4)))
      Empty.absurd(S.dvd(d, m), N.even_odd(m, Nat.add(p, Nat.mul(q, d)), e5))
    case 2n+x:
      Empty.absurd(S.dvd(d, m), mod2_big(kb, x, hr))

def odd2_t1_at(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +m: Nat, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {Nat.double(m) == Nat.mul(kb, d) : Nat}) -> dvd2(d, a, m):
  ((ka, ea), odd2_m(m, d, odd_dvd_r(a, ha, d, ka, ea, Nat.mod(d, 2n), {==}), kb, eb, Nat.mod(kb, 2n), {==}))

def odd2_t2_at(+a: Nat, +m: Nat, +d: Nat, +ka: Nat, +km: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +em: {m == Nat.mul(km, d) : Nat}) -> dvd2(d, a, Nat.double(m)):
  ((ka, ea), (Nat.double(km), Equal.trans(Nat, Nat.double(m), Nat.double(Nat.mul(km, d)), Nat.mul(Nat.double(km), d), Equal.cong(Nat, Nat, t => Nat.double(t), m, Nat.mul(km, d), em), Equal.sym(Nat, Nat.mul(Nat.double(km), d), Nat.double(Nat.mul(km, d)), dmul(km, d)))))

# a odd: gcd(a, 2 m) = gcd(a, m)
def gcd_odd2(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +m: Nat) -> {M.gcd(a, Nat.double(m)) == M.gcd(a, m) : Nat}:
  gcd_eq(a, Nat.double(m), a, m, d => ka => kb => ea => eb => odd2_t1_at(a, ha, m, d, ka, kb, ea, eb), d => ka => km => ea => em => odd2_t2_at(a, m, d, ka, km, ea, em))

# ---- the binary gcd on Nat: the values the generic code computes ----
#
# src/math/generic.bend's gcd_bin on the values of an instance (halve, test
# odd, subtract, compare, double); u64bgcd.bend shows the U64 instance
# computes exactly these, and nbin_gcd below that they are M.gcd.

def iz(+n: Nat) -> Bool:
  Nat.is_eq(n, 0n)

def nstrip_go(fuel: Nat, +x: Nat, o: Bool) -> Nat:
  match fuel o:
    case 0n _:
      x
    case 1n+f True{}:
      x
    case 1n+f False{}:
      nstrip_go(f, Nat.div(x, 2n), odd(Nat.div(x, 2n)))

def nstrip(+x: Nat) -> Nat:
  nstrip_go(140n, x, odd(x))

def nba(+a: Nat, +s: Nat, less: Bool) -> Nat:
  match less:
    case True{}:
      s
    case False{}:
      a

def nbd(+a: Nat, +s: Nat, less: Bool) -> Nat:
  match less:
    case True{}:
      Nat.sub(a, s)
    case False{}:
      Nat.sub(s, a)

# the U64 loop's Small test on the values (both below 2^48, a at least
# 2^16): the loop then returns gcd(a, d) at once
def nsm(+a: Nat, +d: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_lt(C.high(32n, a), U32.to_nat(65536)), Nat.is_lt(C.high(32n, d), U32.to_nat(65536))), Bool.or(Bool.not(Nat.is_eq(C.high(32n, a), 0n)), Nat.is_lt(U32.to_nat(65535), C.low(32n, a))))

def nbloop(fuel: Nat, +a: Nat, +d: Nat, dz: Bool, sm: Bool) -> Nat:
  match fuel dz sm:
    case 0n _ _:
      a
    case 1n+f True{} _:
      a
    case 1n+f False{} True{}:
      M.gcd(a, d)
    case 1n+f False{} False{}:
      nbloop(f, nba(a, nstrip(d), Nat.is_lt(nstrip(d), a)), nbd(a, nstrip(d), Nat.is_lt(nstrip(d), a)), iz(nbd(a, nstrip(d), Nat.is_lt(nstrip(d), a))), nsm(nba(a, nstrip(d), Nat.is_lt(nstrip(d), a)), nbd(a, nstrip(d), Nat.is_lt(nstrip(d), a))))

def ndbl(c: Nat, +x: Nat) -> Nat:
  match c:
    case 0n:
      x
    case 1n+k:
      ndbl(k, Nat.add(x, x))

def nev2(+a: Nat, +b: Nat) -> Bool:
  Bool.not(Bool.or(odd(a), odd(b)))

def ntw(fuel: Nat, +a: Nat, +b: Nat, +c: Nat, both: Bool) -> Nat:
  match fuel both:
    case 0n _:
      ndbl(c, nbloop(140n, nstrip(a), b, iz(b), nsm(nstrip(a), b)))
    case 1n+f False{}:
      ndbl(c, nbloop(140n, nstrip(a), b, iz(b), nsm(nstrip(a), b)))
    case 1n+f True{}:
      ntw(f, Nat.div(a, 2n), Nat.div(b, 2n), 1n+c, nev2(Nat.div(a, 2n), Nat.div(b, 2n)))

def nbg_b(+a: Nat, +b: Nat, bz: Bool) -> Nat:
  match bz:
    case True{}:
      a
    case False{}:
      ntw(140n, a, b, 0n, nev2(a, b))

def nbg_a(+a: Nat, +b: Nat, az: Bool) -> Nat:
  match az:
    case True{}:
      b
    case False{}:
      nbg_b(a, b, iz(b))

def nrb(+a: Nat, +b: Nat, bz: Bool) -> Nat:
  match bz:
    case True{}:
      a
    case False{}:
      nbg_a(b, Nat.mod(a, b), iz(b))

def nbin(+a: Nat, +b: Nat) -> Nat:
  nrb(a, b, iz(b))

# ---- stripping factors of two ----

# not odd is even
def not_odd_r(+n: Nat, +h: {odd(n) == False{} : Bool}, +r: Nat, +hr: {Nat.mod(n, 2n) == r : Nat}) -> {Nat.mod(n, 2n) == 0n : Nat}:
  match r:
    case 0n:
      hr
    case 1n:
      +e = Equal.cong(Nat, Bool, t => Nat.is_eq(t, 1n), Nat.mod(n, 2n), 1n, hr)
      Empty.absurd({Nat.mod(n, 2n) == 0n : Nat}, NF.true_ne_false(Equal.trans(Bool, True{}, odd(n), False{}, Equal.sym(Bool, odd(n), True{}, e), h)))
    case 2n+x:
      Empty.absurd({Nat.mod(n, 2n) == 0n : Nat}, mod2_big(n, x, hr))

def not_odd(+n: Nat, +h: {odd(n) == False{} : Bool}) -> {Nat.mod(n, 2n) == 0n : Nat}:
  not_odd_r(n, h, Nat.mod(n, 2n), {==})

# a odd: gcd(a, strip(x)) = gcd(a, x), whatever the fuel
def strip_gcd(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, f: Nat, +x: Nat, +o: Bool, +ho: {odd(x) == o : Bool}) -> {M.gcd(a, nstrip_go(f, x, o)) == M.gcd(a, x) : Nat}:
  match f o:
    case 0n _:
      {==}
    case 1n+g True{}:
      {==}
    case 1n+g False{}:
      +ev = even_form(x, not_odd(x, ho))
      +ih = strip_gcd(a, ha, g, Nat.div(x, 2n), odd(Nat.div(x, 2n)), {==})
      +e1 = Equal.cong(Nat, Nat, t => M.gcd(a, t), x, Nat.double(Nat.div(x, 2n)), ev)
      Equal.trans(Nat, M.gcd(a, nstrip_go(g, Nat.div(x, 2n), odd(Nat.div(x, 2n)))), M.gcd(a, Nat.div(x, 2n)), M.gcd(a, x), ih, Equal.sym(Nat, M.gcd(a, x), M.gcd(a, Nat.div(x, 2n)), Equal.trans(Nat, M.gcd(a, x), M.gcd(a, Nat.double(Nat.div(x, 2n))), M.gcd(a, Nat.div(x, 2n)), e1, gcd_odd2(a, ha, Nat.div(x, 2n)))))

def pos_absurd1(+x: Nat, +hx: {Nat.is_lt(0n, x) == True{} : Bool}, +hb: {Nat.is_lt(x, 1n) == True{} : Bool}) -> Empty:
  NF.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(0n, x), False{}, Equal.sym(Bool, Nat.is_lt(0n, x), True{}, hx), N.le_not_lt(0n, x, N.lt_succ_le(x, 0n, hb))))

def dlt_inv_b(+u: Nat, +v: Nat, +e: {Nat.is_lt(Nat.double(u), Nat.double(v)) == True{} : Bool}, +bv: Bool, +hb: {Nat.is_lt(u, v) == bv : Bool}) -> {Nat.is_lt(u, v) == True{} : Bool}:
  match bv:
    case True{}:
      hb
    case False{}:
      +c = N.le_not_lt(Nat.double(u), Nat.double(v), N.double_le(v, u, N.not_lt_le(u, v, hb)))
      Empty.absurd({Nat.is_lt(u, v) == True{} : Bool}, NF.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(Nat.double(u), Nat.double(v)), False{}, Equal.sym(Bool, Nat.is_lt(Nat.double(u), Nat.double(v)), True{}, e), c)))

# 2u < 2v gives u < v
def double_lt_inv(+u: Nat, +v: Nat, +e: {Nat.is_lt(Nat.double(u), Nat.double(v)) == True{} : Bool}) -> {Nat.is_lt(u, v) == True{} : Bool}:
  dlt_inv_b(u, v, e, Nat.is_lt(u, v), {==})

def div2_le(+x: Nat) -> {Nat.is_le(Nat.div(x, 2n), x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+n:
      N.le_trans(Nat.div(1n+n, 2n), n, 1n+n, TL.half_le(n), N.le_succ(n))

# an even positive x = 2 (x / 2) has x / 2 > 0
def half_pos(+x: Nat, +hx: {Nat.is_lt(0n, x) == True{} : Bool}, +ev: {x == Nat.double(Nat.div(x, 2n)) : Nat}, +h: Nat, +hh: {Nat.div(x, 2n) == h : Nat}) -> {Nat.is_lt(0n, Nat.div(x, 2n)) == True{} : Bool}:
  match h:
    case 0n:
      +e0 = Equal.trans(Nat, x, Nat.double(Nat.div(x, 2n)), 0n, ev, Equal.cong(Nat, Nat, t => Nat.double(t), Nat.div(x, 2n), 0n, hh))
      Empty.absurd({Nat.is_lt(0n, Nat.div(x, 2n)) == True{} : Bool}, NF.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(0n, x), False{}, Equal.sym(Bool, Nat.is_lt(0n, x), True{}, hx), Equal.cong(Nat, Bool, t => Nat.is_lt(0n, t), x, 0n, e0))))
    case 1n+hp:
      %Equal.sym(Nat, Nat.div(x, 2n), 1n+hp, hh) : {Nat.is_lt(0n, _) == True{} : Bool}
      {==}

# with fuel f and x < 2^f, stripping reaches an odd number
def strip_odd(f: Nat, +x: Nat, +hx: {Nat.is_lt(0n, x) == True{} : Bool}, +hb: {Nat.is_lt(x, C.pow2(f)) == True{} : Bool}, +o: Bool, +ho: {odd(x) == o : Bool}) -> {odd(nstrip_go(f, x, o)) == True{} : Bool}:
  match f o:
    case 0n _:
      Empty.absurd({odd(nstrip_go(0n, x, o)) == True{} : Bool}, pos_absurd1(x, hx, hb))
    case 1n+g True{}:
      ho
    case 1n+ +g False{}:
      +ev = even_form(x, not_odd(x, ho))
      +hb2 = double_lt_inv(Nat.div(x, 2n), C.pow2(g), Equal.trans(Bool, Nat.is_lt(Nat.double(Nat.div(x, 2n)), Nat.double(C.pow2(g))), Nat.is_lt(x, Nat.double(C.pow2(g))), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.double(C.pow2(g))), Nat.double(Nat.div(x, 2n)), x, Equal.sym(Nat, x, Nat.double(Nat.div(x, 2n)), ev)), hb))
      strip_odd(g, Nat.div(x, 2n), half_pos(x, hx, ev, Nat.div(x, 2n), {==}), hb2, odd(Nat.div(x, 2n)), {==})

# stripping never grows
def strip_le(f: Nat, +x: Nat, +o: Bool) -> {Nat.is_le(nstrip_go(f, x, o), x) == True{} : Bool}:
  match f o:
    case 0n _:
      N.le_refl(x)
    case 1n+g True{}:
      N.le_refl(x)
    case 1n+ +g False{}:
      N.le_trans(nstrip_go(g, Nat.div(x, 2n), odd(Nat.div(x, 2n))), Nat.div(x, 2n), x, strip_le(g, Nat.div(x, 2n), odd(Nat.div(x, 2n))), div2_le(x))

# ---- the subtraction loop ----

def mod2_double(+k: Nat) -> {Nat.mod(Nat.double(k), 2n) == 0n : Nat}:
  +x = Nat.double(k)
  +e1 = Equal.trans(Nat, x, Nat.add(Nat.double(Nat.div(x, 2n)), Nat.mod(x, 2n)), Nat.add(x, Nat.mod(x, 2n)), BT.half_eq(x), Equal.cong(Nat, Nat, t => Nat.add(Nat.double(t), Nat.mod(x, 2n)), Nat.div(x, 2n), k, N.div2_double(k)))
  +e2 = Equal.cong(Nat, Nat, t => Nat.sub(t, x), Nat.add(x, Nat.mod(x, 2n)), x, Equal.sym(Nat, x, Nat.add(x, Nat.mod(x, 2n)), e1))
  Equal.trans(Nat, Nat.mod(x, 2n), Nat.sub(Nat.add(x, Nat.mod(x, 2n)), x), 0n, Equal.sym(Nat, Nat.sub(Nat.add(x, Nat.mod(x, 2n)), x), Nat.mod(x, 2n), N.add_sub_cancel(x, Nat.mod(x, 2n))), Equal.trans(Nat, Nat.sub(Nat.add(x, Nat.mod(x, 2n)), x), Nat.sub(x, x), 0n, e2, N.sub_self(x)))

def odd_true(+n: Nat, +h: {Nat.mod(n, 2n) == 1n : Nat}) -> {odd(n) == True{} : Bool}:
  Equal.cong(Nat, Bool, t => Nat.is_eq(t, 1n), Nat.mod(n, 2n), 1n, h)

def odd_pos(+n: Nat, +h: {Nat.mod(n, 2n) == 1n : Nat}) -> {Nat.is_lt(0n, n) == True{} : Bool}:
  %Equal.sym(Nat, n, 1n+Nat.double(Nat.div(n, 2n)), odd_form(n, h)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def double_sub(+p: Nat, +q: Nat) -> {Nat.sub(Nat.double(p), Nat.double(q)) == Nat.double(Nat.sub(p, q)) : Nat}:
  +e1 = Equal.trans(Nat, Nat.sub(Nat.double(p), Nat.double(q)), Nat.sub(Nat.mul(2n, p), Nat.double(q)), Nat.sub(Nat.mul(2n, p), Nat.mul(2n, q)), Equal.cong(Nat, Nat, t => Nat.sub(t, Nat.double(q)), Nat.double(p), Nat.mul(2n, p), NA.double_mul(p)), Equal.cong(Nat, Nat, t => Nat.sub(Nat.mul(2n, p), t), Nat.double(q), Nat.mul(2n, q), NA.double_mul(q)))
  Equal.trans(Nat, Nat.sub(Nat.double(p), Nat.double(q)), Nat.sub(Nat.mul(2n, p), Nat.mul(2n, q)), Nat.double(Nat.sub(p, q)), e1, Equal.trans(Nat, Nat.sub(Nat.mul(2n, p), Nat.mul(2n, q)), Nat.mul(2n, Nat.sub(p, q)), Nat.double(Nat.sub(p, q)), Equal.sym(Nat, Nat.mul(2n, Nat.sub(p, q)), Nat.sub(Nat.mul(2n, p), Nat.mul(2n, q)), FA.mul_sub_left(2n, p, q)), Equal.sym(Nat, Nat.double(Nat.sub(p, q)), Nat.mul(2n, Nat.sub(p, q)), NA.double_mul(Nat.sub(p, q)))))

# odd a - odd s is even
def odd_sub(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +s: Nat, +hs: {Nat.mod(s, 2n) == 1n : Nat}) -> {Nat.sub(a, s) == Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(s, 2n))) : Nat}:
  %Equal.sym(Nat, a, 1n+Nat.double(Nat.div(a, 2n)), odd_form(a, ha)) : {Nat.sub(_, s) == Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(s, 2n))) : Nat}
  %Equal.sym(Nat, s, 1n+Nat.double(Nat.div(s, 2n)), odd_form(s, hs)) : {Nat.sub(1n+Nat.double(Nat.div(a, 2n)), _) == Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(s, 2n))) : Nat}
  double_sub(Nat.div(a, 2n), Nat.div(s, 2n))

def mul_pos(+a: Nat, +ha: {Nat.is_lt(0n, a) == True{} : Bool}, +d: Nat, +hd: {Nat.is_lt(0n, d) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.mul(a, d)) == True{} : Bool}:
  N.lt_le_trans(0n, d, Nat.mul(a, d), hd, %NA.mul_comm(d, a) : {Nat.is_le(d, _) == True{} : Bool}
    RT.le_mul_pos(d, a, ha))

def bl_zero(f: Nat, +a: Nat) -> {nbloop(f, a, 0n, True{}, nsm(a, 0n)) == M.gcd(a, 0n) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a (1 + kp) < 2^g from a (2 + 2 kp) < 2^(1 + g)
def half_bound(+a: Nat, +kp: Nat, +g: Nat, +hb: {Nat.is_lt(Nat.mul(a, Nat.double(1n+kp)), C.pow2(1n+g)) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, 1n+kp), C.pow2(g)) == True{} : Bool}:
  +e = Equal.trans(Nat, Nat.mul(a, Nat.double(1n+kp)), Nat.mul(Nat.double(1n+kp), a), Nat.double(Nat.mul(1n+kp, a)), NA.mul_comm(a, Nat.double(1n+kp)), dmul(1n+kp, a))
  double_lt_inv(Nat.mul(a, 1n+kp), C.pow2(g), Equal.trans(Bool, Nat.is_lt(Nat.double(Nat.mul(a, 1n+kp)), Nat.double(C.pow2(g))), Nat.is_lt(Nat.mul(a, Nat.double(1n+kp)), Nat.double(C.pow2(g))), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.double(C.pow2(g))), Nat.double(Nat.mul(a, 1n+kp)), Nat.mul(a, Nat.double(1n+kp)), Equal.sym(Nat, Nat.mul(a, Nat.double(1n+kp)), Nat.double(Nat.mul(a, 1n+kp)), Equal.trans(Nat, Nat.mul(a, Nat.double(1n+kp)), Nat.double(Nat.mul(1n+kp, a)), Nat.double(Nat.mul(a, 1n+kp)), e, Equal.cong(Nat, Nat, t => Nat.double(t), Nat.mul(1n+kp, a), Nat.mul(a, 1n+kp), NA.mul_comm(1n+kp, a))))), hb))

# strip(2 (1 + kp)) <= 1 + kp
def strip_even(+kp: Nat) -> {Nat.is_le(nstrip(Nat.double(1n+kp)), 1n+kp) == True{} : Bool}:
  +eo = Equal.cong(Nat, Bool, t => Nat.is_eq(t, 1n), Nat.mod(Nat.double(1n+kp), 2n), 0n, mod2_double(1n+kp))
  %Equal.sym(Nat, nstrip_go(140n, Nat.double(1n+kp), odd(Nat.double(1n+kp))), nstrip_go(140n, Nat.double(1n+kp), False{}), Equal.cong(Bool, Nat, t => nstrip_go(140n, Nat.double(1n+kp), t), odd(Nat.double(1n+kp)), False{}, eo)) : {Nat.is_le(_, 1n+kp) == True{} : Bool}
  %Equal.sym(Nat, Nat.div(Nat.double(1n+kp), 2n), 1n+kp, N.div2_double(1n+kp)) : {Nat.is_le(nstrip_go(139n, _, odd(_)), 1n+kp) == True{} : Bool}
  strip_le(139n, 1n+kp, odd(1n+kp))

def bl_case(+g: Nat, +a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +kp: Nat, +hbg: {Nat.is_lt(Nat.mul(a, 1n+kp), C.pow2(g)) == True{} : Bool}, ih: @+a2: Nat -> @+ha2: {Nat.mod(a2, 2n) == 1n : Nat} -> @+k2: Nat -> @+hb2: {Nat.is_lt(Nat.mul(a2, Nat.double(k2)), C.pow2(g)) == True{} : Bool} -> {nbloop(g, a2, Nat.double(k2), iz(Nat.double(k2)), nsm(a2, Nat.double(k2))) == M.gcd(a2, Nat.double(k2)) : Nat}, +hs: {Nat.mod(nstrip(Nat.double(1n+kp)), 2n) == 1n : Nat}, +hsle: {Nat.is_le(nstrip(Nat.double(1n+kp)), 1n+kp) == True{} : Bool}, +hga: {M.gcd(a, Nat.double(1n+kp)) == M.gcd(a, nstrip(Nat.double(1n+kp))) : Nat}, +hsa: {Nat.is_le(Nat.mul(a, nstrip(Nat.double(1n+kp))), Nat.mul(a, 1n+kp)) == True{} : Bool}, +lb: Bool, +hl: {Nat.is_lt(nstrip(Nat.double(1n+kp)), a) == lb : Bool}) -> {nbloop(g, nba(a, nstrip(Nat.double(1n+kp)), lb), nbd(a, nstrip(Nat.double(1n+kp)), lb), iz(nbd(a, nstrip(Nat.double(1n+kp)), lb)), nsm(nba(a, nstrip(Nat.double(1n+kp)), lb), nbd(a, nstrip(Nat.double(1n+kp)), lb))) == M.gcd(a, Nat.double(1n+kp)) : Nat}:
  match lb:
    case True{}:
      +sle = N.lt_le(nstrip(Nat.double(1n+kp)), a, hl)
      +le1 = N.le_trans(Nat.mul(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), Nat.mul(nstrip(Nat.double(1n+kp)), a), Nat.mul(a, 1n+kp), NF.mul_le_r(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp))), a, UH.sub_le(a, nstrip(Nat.double(1n+kp)))), N.le_trans(Nat.mul(nstrip(Nat.double(1n+kp)), a), Nat.mul(a, nstrip(Nat.double(1n+kp))), Nat.mul(a, 1n+kp), N.eq_le(Nat.mul(nstrip(Nat.double(1n+kp)), a), Nat.mul(a, nstrip(Nat.double(1n+kp))), NA.mul_comm(nstrip(Nat.double(1n+kp)), a)), hsa))
      +hDs = Equal.sym(Nat, Nat.sub(a, nstrip(Nat.double(1n+kp))), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n))), odd_sub(a, ha, nstrip(Nat.double(1n+kp)), hs))
      +hb2 = Equal.trans(Bool, Nat.is_lt(Nat.mul(nstrip(Nat.double(1n+kp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n)))), C.pow2(g)), Nat.is_lt(Nat.mul(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), C.pow2(g)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.mul(nstrip(Nat.double(1n+kp)), t), C.pow2(g)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n))), Nat.sub(a, nstrip(Nat.double(1n+kp))), hDs), N.le_lt_trans(Nat.mul(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), Nat.mul(a, 1n+kp), C.pow2(g), le1, hbg))
      +r = ih(nstrip(Nat.double(1n+kp)), hs, Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n)), hb2)
      %hDs : {nbloop(g, nstrip(Nat.double(1n+kp)), _, iz(_), nsm(nstrip(Nat.double(1n+kp)), _)) == M.gcd(a, Nat.double(1n+kp)) : Nat}
      Equal.trans(Nat, nbloop(g, nstrip(Nat.double(1n+kp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n))), iz(Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n)))), nsm(nstrip(Nat.double(1n+kp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n))))), M.gcd(nstrip(Nat.double(1n+kp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n)))), M.gcd(a, Nat.double(1n+kp)), r, Equal.trans(Nat, M.gcd(nstrip(Nat.double(1n+kp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n)))), M.gcd(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), M.gcd(a, Nat.double(1n+kp)), Equal.cong(Nat, Nat, t => M.gcd(nstrip(Nat.double(1n+kp)), t), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(Nat.double(1n+kp)), 2n))), Nat.sub(a, nstrip(Nat.double(1n+kp))), hDs), Equal.trans(Nat, M.gcd(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), M.gcd(nstrip(Nat.double(1n+kp)), a), M.gcd(a, Nat.double(1n+kp)), Equal.sym(Nat, M.gcd(nstrip(Nat.double(1n+kp)), a), M.gcd(nstrip(Nat.double(1n+kp)), Nat.sub(a, nstrip(Nat.double(1n+kp)))), gcd_sub(nstrip(Nat.double(1n+kp)), a, sle)), Equal.trans(Nat, M.gcd(nstrip(Nat.double(1n+kp)), a), M.gcd(a, nstrip(Nat.double(1n+kp))), M.gcd(a, Nat.double(1n+kp)), gcd_comm(nstrip(Nat.double(1n+kp)), a), Equal.sym(Nat, M.gcd(a, Nat.double(1n+kp)), M.gcd(a, nstrip(Nat.double(1n+kp))), hga)))))
    case False{}:
      +ale = N.not_lt_le(nstrip(Nat.double(1n+kp)), a, hl)
      +le1 = N.le_trans(Nat.mul(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), Nat.mul(a, nstrip(Nat.double(1n+kp))), Nat.mul(a, 1n+kp), NF.mul_le_r(a, Nat.sub(nstrip(Nat.double(1n+kp)), a), nstrip(Nat.double(1n+kp)), UH.sub_le(nstrip(Nat.double(1n+kp)), a)), hsa)
      +hDs = Equal.sym(Nat, Nat.sub(nstrip(Nat.double(1n+kp)), a), Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n))), odd_sub(nstrip(Nat.double(1n+kp)), hs, a, ha))
      +hb2 = Equal.trans(Bool, Nat.is_lt(Nat.mul(a, Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n)))), C.pow2(g)), Nat.is_lt(Nat.mul(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), C.pow2(g)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.mul(a, t), C.pow2(g)), Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n))), Nat.sub(nstrip(Nat.double(1n+kp)), a), hDs), N.le_lt_trans(Nat.mul(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), Nat.mul(a, 1n+kp), C.pow2(g), le1, hbg))
      +r = ih(a, ha, Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n)), hb2)
      %hDs : {nbloop(g, a, _, iz(_), nsm(a, _)) == M.gcd(a, Nat.double(1n+kp)) : Nat}
      Equal.trans(Nat, nbloop(g, a, Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n))), iz(Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n)))), nsm(a, Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n))))), M.gcd(a, Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n)))), M.gcd(a, Nat.double(1n+kp)), r, Equal.trans(Nat, M.gcd(a, Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n)))), M.gcd(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), M.gcd(a, Nat.double(1n+kp)), Equal.cong(Nat, Nat, t => M.gcd(a, t), Nat.double(Nat.sub(Nat.div(nstrip(Nat.double(1n+kp)), 2n), Nat.div(a, 2n))), Nat.sub(nstrip(Nat.double(1n+kp)), a), hDs), Equal.trans(Nat, M.gcd(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), M.gcd(a, nstrip(Nat.double(1n+kp))), M.gcd(a, Nat.double(1n+kp)), Equal.sym(Nat, M.gcd(a, nstrip(Nat.double(1n+kp))), M.gcd(a, Nat.sub(nstrip(Nat.double(1n+kp)), a)), gcd_sub(a, nstrip(Nat.double(1n+kp)), ale)), Equal.sym(Nat, M.gcd(a, Nat.double(1n+kp)), M.gcd(a, nstrip(Nat.double(1n+kp))), hga))))

# one step of the loop, from the induction hypothesis for fuel g
def bl_step(+g: Nat, +a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +kp: Nat, +hbg: {Nat.is_lt(Nat.mul(a, 1n+kp), C.pow2(g)) == True{} : Bool}, +hf1: {Nat.is_le(1n+g, 140n) == True{} : Bool}, ih: @+a2: Nat -> @+ha2: {Nat.mod(a2, 2n) == 1n : Nat} -> @+k2: Nat -> @+hb2: {Nat.is_lt(Nat.mul(a2, Nat.double(k2)), C.pow2(g)) == True{} : Bool} -> {nbloop(g, a2, Nat.double(k2), iz(Nat.double(k2)), nsm(a2, Nat.double(k2))) == M.gcd(a2, Nat.double(k2)) : Nat}, +lb: Bool, +hl: {Nat.is_lt(nstrip(Nat.double(1n+kp)), a) == lb : Bool}) -> {nbloop(g, nba(a, nstrip(Nat.double(1n+kp)), lb), nbd(a, nstrip(Nat.double(1n+kp)), lb), iz(nbd(a, nstrip(Nat.double(1n+kp)), lb)), nsm(nba(a, nstrip(Nat.double(1n+kp)), lb), nbd(a, nstrip(Nat.double(1n+kp)), lb))) == M.gcd(a, Nat.double(1n+kp)) : Nat}:
  +apos = odd_pos(a, ha)
  +k1 = N.le_trans(1n+kp, Nat.mul(1n+kp, a), Nat.mul(a, 1n+kp), RT.le_mul_pos(1n+kp, a, apos), N.eq_le(Nat.mul(1n+kp, a), Nat.mul(a, 1n+kp), NA.mul_comm(1n+kp, a)))
  +k2 = N.lt_le_trans(Nat.double(1n+kp), Nat.double(C.pow2(g)), C.pow2(140n), N.double_lt(1n+kp, C.pow2(g), N.le_lt_trans(1n+kp, Nat.mul(a, 1n+kp), C.pow2(g), k1, hbg)), N.pow2_mono(1n+g, 140n, hf1))
  +hs = odd_eq(nstrip(Nat.double(1n+kp)), strip_odd(140n, Nat.double(1n+kp), {==}, k2, odd(Nat.double(1n+kp)), {==}))
  +hsle = strip_even(kp)
  +hga = Equal.sym(Nat, M.gcd(a, nstrip(Nat.double(1n+kp))), M.gcd(a, Nat.double(1n+kp)), strip_gcd(a, ha, 140n, Nat.double(1n+kp), odd(Nat.double(1n+kp)), {==}))
  +hsa = NF.mul_le_r(a, nstrip(Nat.double(1n+kp)), 1n+kp, hsle)
  bl_case(g, a, ha, kp, hbg, ih, hs, hsle, hga, hsa, lb, hl)

# a small pair ends the loop with its gcd; otherwise it steps
def bl_sm(+g: Nat, +a: Nat, +kp: Nat, sm: Bool, +hn: {nbloop(g, nba(a, nstrip(Nat.double(1n+kp)), Nat.is_lt(nstrip(Nat.double(1n+kp)), a)), nbd(a, nstrip(Nat.double(1n+kp)), Nat.is_lt(nstrip(Nat.double(1n+kp)), a)), iz(nbd(a, nstrip(Nat.double(1n+kp)), Nat.is_lt(nstrip(Nat.double(1n+kp)), a))), nsm(nba(a, nstrip(Nat.double(1n+kp)), Nat.is_lt(nstrip(Nat.double(1n+kp)), a)), nbd(a, nstrip(Nat.double(1n+kp)), Nat.is_lt(nstrip(Nat.double(1n+kp)), a)))) == M.gcd(a, Nat.double(1n+kp)) : Nat}) -> {nbloop(1n+g, a, Nat.double(1n+kp), iz(Nat.double(1n+kp)), sm) == M.gcd(a, Nat.double(1n+kp)) : Nat}:
  match sm:
    case True{}:
      {==}
    case False{}:
      hn

# the loop from (a odd, 2k) with a * 2k < 2^f and f <= 140 computes gcd(a, 2k)
def bl(f: Nat, +a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +k: Nat, +hb: {Nat.is_lt(Nat.mul(a, Nat.double(k)), C.pow2(f)) == True{} : Bool}, +hf: {Nat.is_le(f, 140n) == True{} : Bool}) -> {nbloop(f, a, Nat.double(k), iz(Nat.double(k)), nsm(a, Nat.double(k))) == M.gcd(a, Nat.double(k)) : Nat}:
  match f k:
    case f0 0n:
      bl_zero(f0, a)
    case 0n 1n+kp:
      Empty.absurd({nbloop(0n, a, Nat.double(1n+kp), iz(Nat.double(1n+kp)), nsm(a, Nat.double(1n+kp))) == M.gcd(a, Nat.double(1n+kp)) : Nat}, pos_absurd1(Nat.mul(a, Nat.double(1n+kp)), mul_pos(a, odd_pos(a, ha), Nat.double(1n+kp), {==}), hb))
    case 1n+ +g 1n+ +kp:
      +hg = N.le_trans(g, 1n+g, 140n, N.le_succ(g), hf)
      bl_sm(g, a, kp, nsm(a, Nat.double(1n+kp)), bl_step(g, a, ha, kp, half_bound(a, kp, g, hb), hf, a2 => ha2 => k2 => hb2 => bl(g, a2, ha2, k2, hb2, hg), Nat.is_lt(nstrip(Nat.double(1n+kp)), a), {==}))

def mul_lt_sq(+x: Nat, +y: Nat, +s: Nat, +hx: {Nat.is_lt(x, s) == True{} : Bool}, +hy: {Nat.is_lt(y, s) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), Nat.mul(s, s)) == True{} : Bool}:
  match s:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(x, y), 0n) == True{} : Bool}, N.lt_zero_absurd(x, hx))
    case 1n+ +sp:
      +a1 = AR.mul_le(x, sp, y, N.lt_succ_le(x, sp, hx))
      +a2 = NF.mul_le_r(sp, y, sp, N.lt_succ_le(y, sp, hy))
      +a3 = NF.mul_le_r(sp, sp, 1n+sp, N.le_succ(sp))
      +a4 = N.le_trans(Nat.mul(x, y), Nat.mul(sp, y), Nat.mul(sp, sp), a1, a2)
      +a5 = N.le_trans(Nat.mul(x, y), Nat.mul(sp, sp), Nat.mul(sp, 1n+sp), a4, a3)
      N.le_lt_trans(Nat.mul(x, y), Nat.mul(sp, 1n+sp), Nat.add(1n+sp, Nat.mul(sp, 1n+sp)), a5, N.lt_add_r2(0n, 1n+sp, Nat.mul(sp, 1n+sp), {==}))

# ---- the first step, from any b > 0 ----

def bf_case(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +bp: Nat, +hab: {Nat.is_lt(Nat.mul(a, 1n+bp), C.pow2(139n)) == True{} : Bool}, +hs: {Nat.mod(nstrip(1n+bp), 2n) == 1n : Nat}, +hga: {M.gcd(a, 1n+bp) == M.gcd(a, nstrip(1n+bp)) : Nat}, +hsa: {Nat.is_le(Nat.mul(a, nstrip(1n+bp)), Nat.mul(a, 1n+bp)) == True{} : Bool}, +lb: Bool, +hl: {Nat.is_lt(nstrip(1n+bp), a) == lb : Bool}) -> {nbloop(139n, nba(a, nstrip(1n+bp), lb), nbd(a, nstrip(1n+bp), lb), iz(nbd(a, nstrip(1n+bp), lb)), nsm(nba(a, nstrip(1n+bp), lb), nbd(a, nstrip(1n+bp), lb))) == M.gcd(a, 1n+bp) : Nat}:
  match lb:
    case True{}:
      +sle = N.lt_le(nstrip(1n+bp), a, hl)
      +le1 = N.le_trans(Nat.mul(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), Nat.mul(nstrip(1n+bp), a), Nat.mul(a, 1n+bp), NF.mul_le_r(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp)), a, UH.sub_le(a, nstrip(1n+bp))), N.le_trans(Nat.mul(nstrip(1n+bp), a), Nat.mul(a, nstrip(1n+bp)), Nat.mul(a, 1n+bp), N.eq_le(Nat.mul(nstrip(1n+bp), a), Nat.mul(a, nstrip(1n+bp)), NA.mul_comm(nstrip(1n+bp), a)), hsa))
      +hDs = Equal.sym(Nat, Nat.sub(a, nstrip(1n+bp)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n))), odd_sub(a, ha, nstrip(1n+bp), hs))
      +hb2 = Equal.trans(Bool, Nat.is_lt(Nat.mul(nstrip(1n+bp), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n)))), C.pow2(139n)), Nat.is_lt(Nat.mul(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), C.pow2(139n)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.mul(nstrip(1n+bp), t), C.pow2(139n)), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n))), Nat.sub(a, nstrip(1n+bp)), hDs), N.le_lt_trans(Nat.mul(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), Nat.mul(a, 1n+bp), C.pow2(139n), le1, hab))
      +r = bl(139n, nstrip(1n+bp), hs, Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n)), hb2, {==})
      %hDs : {nbloop(139n, nstrip(1n+bp), _, iz(_), nsm(nstrip(1n+bp), _)) == M.gcd(a, 1n+bp) : Nat}
      Equal.trans(Nat, nbloop(139n, nstrip(1n+bp), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n))), iz(Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n)))), nsm(nstrip(1n+bp), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n))))), M.gcd(nstrip(1n+bp), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n)))), M.gcd(a, 1n+bp), r, Equal.trans(Nat, M.gcd(nstrip(1n+bp), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n)))), M.gcd(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), M.gcd(a, 1n+bp), Equal.cong(Nat, Nat, t => M.gcd(nstrip(1n+bp), t), Nat.double(Nat.sub(Nat.div(a, 2n), Nat.div(nstrip(1n+bp), 2n))), Nat.sub(a, nstrip(1n+bp)), hDs), Equal.trans(Nat, M.gcd(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), M.gcd(nstrip(1n+bp), a), M.gcd(a, 1n+bp), Equal.sym(Nat, M.gcd(nstrip(1n+bp), a), M.gcd(nstrip(1n+bp), Nat.sub(a, nstrip(1n+bp))), gcd_sub(nstrip(1n+bp), a, sle)), Equal.trans(Nat, M.gcd(nstrip(1n+bp), a), M.gcd(a, nstrip(1n+bp)), M.gcd(a, 1n+bp), gcd_comm(nstrip(1n+bp), a), Equal.sym(Nat, M.gcd(a, 1n+bp), M.gcd(a, nstrip(1n+bp)), hga)))))
    case False{}:
      +ale = N.not_lt_le(nstrip(1n+bp), a, hl)
      +le1 = N.le_trans(Nat.mul(a, Nat.sub(nstrip(1n+bp), a)), Nat.mul(a, nstrip(1n+bp)), Nat.mul(a, 1n+bp), NF.mul_le_r(a, Nat.sub(nstrip(1n+bp), a), nstrip(1n+bp), UH.sub_le(nstrip(1n+bp), a)), hsa)
      +hDs = Equal.sym(Nat, Nat.sub(nstrip(1n+bp), a), Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n))), odd_sub(nstrip(1n+bp), hs, a, ha))
      +hb2 = Equal.trans(Bool, Nat.is_lt(Nat.mul(a, Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n)))), C.pow2(139n)), Nat.is_lt(Nat.mul(a, Nat.sub(nstrip(1n+bp), a)), C.pow2(139n)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.mul(a, t), C.pow2(139n)), Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n))), Nat.sub(nstrip(1n+bp), a), hDs), N.le_lt_trans(Nat.mul(a, Nat.sub(nstrip(1n+bp), a)), Nat.mul(a, 1n+bp), C.pow2(139n), le1, hab))
      +r = bl(139n, a, ha, Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n)), hb2, {==})
      %hDs : {nbloop(139n, a, _, iz(_), nsm(a, _)) == M.gcd(a, 1n+bp) : Nat}
      Equal.trans(Nat, nbloop(139n, a, Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n))), iz(Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n)))), nsm(a, Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n))))), M.gcd(a, Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n)))), M.gcd(a, 1n+bp), r, Equal.trans(Nat, M.gcd(a, Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n)))), M.gcd(a, Nat.sub(nstrip(1n+bp), a)), M.gcd(a, 1n+bp), Equal.cong(Nat, Nat, t => M.gcd(a, t), Nat.double(Nat.sub(Nat.div(nstrip(1n+bp), 2n), Nat.div(a, 2n))), Nat.sub(nstrip(1n+bp), a), hDs), Equal.trans(Nat, M.gcd(a, Nat.sub(nstrip(1n+bp), a)), M.gcd(a, nstrip(1n+bp)), M.gcd(a, 1n+bp), Equal.sym(Nat, M.gcd(a, nstrip(1n+bp)), M.gcd(a, Nat.sub(nstrip(1n+bp), a)), gcd_sub(a, nstrip(1n+bp), ale)), Equal.sym(Nat, M.gcd(a, 1n+bp), M.gcd(a, nstrip(1n+bp)), hga))))

def bf_sm(+a: Nat, +bp: Nat, sm: Bool, +hn: {nbloop(139n, nba(a, nstrip(1n+bp), Nat.is_lt(nstrip(1n+bp), a)), nbd(a, nstrip(1n+bp), Nat.is_lt(nstrip(1n+bp), a)), iz(nbd(a, nstrip(1n+bp), Nat.is_lt(nstrip(1n+bp), a))), nsm(nba(a, nstrip(1n+bp), Nat.is_lt(nstrip(1n+bp), a)), nbd(a, nstrip(1n+bp), Nat.is_lt(nstrip(1n+bp), a)))) == M.gcd(a, 1n+bp) : Nat}) -> {nbloop(140n, a, 1n+bp, iz(1n+bp), sm) == M.gcd(a, 1n+bp) : Nat}:
  match sm:
    case True{}:
      {==}
    case False{}:
      hn

# a odd, b > 0, a b < 2^139: the loop computes gcd(a, b)
def bfirst(+a: Nat, +ha: {Nat.mod(a, 2n) == 1n : Nat}, +bp: Nat, +hab: {Nat.is_lt(Nat.mul(a, 1n+bp), C.pow2(139n)) == True{} : Bool}) -> {nbloop(140n, a, 1n+bp, iz(1n+bp), nsm(a, 1n+bp)) == M.gcd(a, 1n+bp) : Nat}:
  +k1 = N.le_trans(1n+bp, Nat.mul(1n+bp, a), Nat.mul(a, 1n+bp), RT.le_mul_pos(1n+bp, a, odd_pos(a, ha)), N.eq_le(Nat.mul(1n+bp, a), Nat.mul(a, 1n+bp), NA.mul_comm(1n+bp, a)))
  +k2 = N.lt_le_trans(1n+bp, C.pow2(139n), C.pow2(140n), N.le_lt_trans(1n+bp, Nat.mul(a, 1n+bp), C.pow2(139n), k1, hab), N.pow2_mono(139n, 140n, {==}))
  +hs = odd_eq(nstrip(1n+bp), strip_odd(140n, 1n+bp, {==}, k2, odd(1n+bp), {==}))
  +hga = Equal.sym(Nat, M.gcd(a, nstrip(1n+bp)), M.gcd(a, 1n+bp), strip_gcd(a, ha, 140n, 1n+bp, odd(1n+bp), {==}))
  +hsa = NF.mul_le_r(a, nstrip(1n+bp), 1n+bp, strip_le(140n, 1n+bp, odd(1n+bp)))
  bf_sm(a, bp, nsm(a, 1n+bp), bf_case(a, ha, bp, hab, hs, hga, hsa, Nat.is_lt(nstrip(1n+bp), a), {==}))

# ---- halving while both are even ----

def ev_ta(+oa: Bool, +ob: Bool, +h: {Bool.not(Bool.or(oa, ob)) == True{} : Bool}) -> {oa == False{} : Bool}:
  match oa ob:
    case True{} y:
      Empty.absurd({True{} == False{} : Bool}, NF.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{} y:
      {==}

def ev_tb(+oa: Bool, +ob: Bool, +h: {Bool.not(Bool.or(oa, ob)) == True{} : Bool}) -> {ob == False{} : Bool}:
  match oa ob:
    case True{} y:
      Empty.absurd({y == False{} : Bool}, NF.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, NF.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{} False{}:
      {==}

def ev_fb(+oa: Bool, +ob: Bool, +h: {Bool.not(Bool.or(oa, ob)) == False{} : Bool}, +hoa: {oa == False{} : Bool}) -> {ob == True{} : Bool}:
  match oa ob:
    case True{} y:
      Empty.absurd({y == True{} : Bool}, NF.true_ne_false(hoa))
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, NF.true_ne_false(h))

def add_self(+x: Nat) -> {Nat.mul(2n, x) == Nat.add(x, x) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(x, t), Nat.add(x, 0n), x, N.add_zero(x))

# gcd(2a, 2b) = gcd(a, b) + gcd(a, b)
def gcd_twice(+a: Nat, +b: Nat, +ea: {a == Nat.double(Nat.div(a, 2n)) : Nat}, +eb: {b == Nat.double(Nat.div(b, 2n)) : Nat}) -> {M.gcd(a, b) == Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))) : Nat}:
  +e1 = Equal.trans(Nat, M.gcd(a, b), M.gcd(Nat.double(Nat.div(a, 2n)), b), M.gcd(Nat.double(Nat.div(a, 2n)), Nat.double(Nat.div(b, 2n))), Equal.cong(Nat, Nat, t => M.gcd(t, b), a, Nat.double(Nat.div(a, 2n)), ea), Equal.cong(Nat, Nat, t => M.gcd(Nat.double(Nat.div(a, 2n)), t), b, Nat.double(Nat.div(b, 2n)), eb))
  +e2 = Equal.trans(Nat, M.gcd(Nat.double(Nat.div(a, 2n)), Nat.double(Nat.div(b, 2n))), M.gcd(Nat.mul(2n, Nat.div(a, 2n)), Nat.double(Nat.div(b, 2n))), M.gcd(Nat.mul(2n, Nat.div(a, 2n)), Nat.mul(2n, Nat.div(b, 2n))), Equal.cong(Nat, Nat, t => M.gcd(t, Nat.double(Nat.div(b, 2n))), Nat.double(Nat.div(a, 2n)), Nat.mul(2n, Nat.div(a, 2n)), NA.double_mul(Nat.div(a, 2n))), Equal.cong(Nat, Nat, t => M.gcd(Nat.mul(2n, Nat.div(a, 2n)), t), Nat.double(Nat.div(b, 2n)), Nat.mul(2n, Nat.div(b, 2n)), NA.double_mul(Nat.div(b, 2n))))
  Equal.trans(Nat, M.gcd(a, b), M.gcd(Nat.double(Nat.div(a, 2n)), Nat.double(Nat.div(b, 2n))), Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), e1, Equal.trans(Nat, M.gcd(Nat.double(Nat.div(a, 2n)), Nat.double(Nat.div(b, 2n))), M.gcd(Nat.mul(2n, Nat.div(a, 2n)), Nat.mul(2n, Nat.div(b, 2n))), Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), e2, Equal.trans(Nat, M.gcd(Nat.mul(2n, Nat.div(a, 2n)), Nat.mul(2n, Nat.div(b, 2n))), Nat.mul(2n, M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), NP.mul_left(2n, Nat.div(a, 2n), Nat.div(b, 2n)), add_self(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))))))

# the exit: gcd(strip a, b) = gcd(a, b) when a or b is odd
def exit_gcd(+a: Nat, +b: Nat, +oa: Bool, +hoa: {odd(a) == oa : Bool}, +hev: {Bool.not(Bool.or(odd(a), odd(b))) == False{} : Bool}) -> {M.gcd(nstrip(a), b) == M.gcd(a, b) : Nat}:
  match oa:
    case True{}:
      Equal.cong(Nat, Nat, t => M.gcd(t, b), nstrip(a), a, Equal.cong(Bool, Nat, t => nstrip_go(140n, a, t), odd(a), True{}, hoa))
    case False{}:
      +hb = odd_eq(b, ev_fb(odd(a), odd(b), hev, hoa))
      Equal.trans(Nat, M.gcd(nstrip(a), b), M.gcd(b, nstrip(a)), M.gcd(a, b), gcd_comm(nstrip(a), b), Equal.trans(Nat, M.gcd(b, nstrip(a)), M.gcd(b, a), M.gcd(a, b), strip_gcd(b, hb, 140n, a, odd(a), {==}), gcd_comm(b, a)))

def tw_exit(+a: Nat, +b: Nat, +ha0: {Nat.is_lt(0n, a) == True{} : Bool}, +ha140: {Nat.is_lt(a, C.pow2(140n)) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), C.pow2(139n)) == True{} : Bool}, +hev: {nev2(a, b) == False{} : Bool}, +hb0: {Nat.is_lt(0n, b) == True{} : Bool}, +bv: Nat, +hbv: {b == bv : Nat}) -> {nbloop(140n, nstrip(a), b, iz(b), nsm(nstrip(a), b)) == M.gcd(a, b) : Nat}:
  match bv:
    case 0n:
      Empty.absurd({nbloop(140n, nstrip(a), b, iz(b), nsm(nstrip(a), b)) == M.gcd(a, b) : Nat}, NF.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(0n, b), False{}, Equal.sym(Bool, Nat.is_lt(0n, b), True{}, hb0), Equal.cong(Nat, Bool, t => Nat.is_lt(0n, t), b, 0n, hbv))))
    case 1n+bp:
      %Equal.sym(Nat, b, 1n+bp, hbv) : {nbloop(140n, nstrip(a), _, iz(_), nsm(nstrip(a), _)) == M.gcd(a, _) : Nat}
      +hs = odd_eq(nstrip(a), strip_odd(140n, a, ha0, ha140, odd(a), {==}))
      +hab2 = N.le_lt_trans(Nat.mul(nstrip(a), 1n+bp), Nat.mul(a, 1n+bp), C.pow2(139n), AR.mul_le(nstrip(a), a, 1n+bp, strip_le(140n, a, odd(a))), Equal.trans(Bool, Nat.is_lt(Nat.mul(a, 1n+bp), C.pow2(139n)), Nat.is_lt(Nat.mul(a, b), C.pow2(139n)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.mul(a, t), C.pow2(139n)), 1n+bp, b, Equal.sym(Nat, b, 1n+bp, hbv)), hab))
      +hev1 = Equal.trans(Bool, Bool.not(Bool.or(odd(a), odd(1n+bp))), Bool.not(Bool.or(odd(a), odd(b))), False{}, Equal.cong(Nat, Bool, t => Bool.not(Bool.or(odd(a), odd(t))), 1n+bp, b, Equal.sym(Nat, b, 1n+bp, hbv)), hev)
      Equal.trans(Nat, nbloop(140n, nstrip(a), 1n+bp, iz(1n+bp), nsm(nstrip(a), 1n+bp)), M.gcd(nstrip(a), 1n+bp), M.gcd(a, 1n+bp), bfirst(nstrip(a), hs, bp, hab2), exit_gcd(a, 1n+bp, odd(a), {==}, hev1))

def tw_case(+g: Nat, +a: Nat, +b: Nat, +c: Nat, +ha0: {Nat.is_lt(0n, a) == True{} : Bool}, +hb0: {Nat.is_lt(0n, b) == True{} : Bool}, +haf: {Nat.is_lt(a, C.pow2(1n+g)) == True{} : Bool}, +hf: {Nat.is_le(1n+g, 140n) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), C.pow2(139n)) == True{} : Bool}, ih: @+a2: Nat -> @+b2: Nat -> @+c2: Nat -> @+ha2: {Nat.is_lt(0n, a2) == True{} : Bool} -> @+hb2: {Nat.is_lt(0n, b2) == True{} : Bool} -> @+haf2: {Nat.is_lt(a2, C.pow2(g)) == True{} : Bool} -> @+hab2: {Nat.is_lt(Nat.mul(a2, b2), C.pow2(139n)) == True{} : Bool} -> {ntw(g, a2, b2, c2, nev2(a2, b2)) == ndbl(c2, M.gcd(a2, b2)) : Nat}, +ev: Bool, +hev: {nev2(a, b) == ev : Bool}) -> {ntw(1n+g, a, b, c, ev) == ndbl(c, M.gcd(a, b)) : Nat}:
  match ev:
    case True{}:
      +ea = even_form(a, not_odd(a, ev_ta(odd(a), odd(b), hev)))
      +eb = even_form(b, not_odd(b, ev_tb(odd(a), odd(b), hev)))
      +ha2 = half_pos(a, ha0, ea, Nat.div(a, 2n), {==})
      +hb2 = half_pos(b, hb0, eb, Nat.div(b, 2n), {==})
      +haf2 = double_lt_inv(Nat.div(a, 2n), C.pow2(g), Equal.trans(Bool, Nat.is_lt(Nat.double(Nat.div(a, 2n)), Nat.double(C.pow2(g))), Nat.is_lt(a, Nat.double(C.pow2(g))), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.double(C.pow2(g))), Nat.double(Nat.div(a, 2n)), a, Equal.sym(Nat, a, Nat.double(Nat.div(a, 2n)), ea)), haf))
      +hab2 = N.le_lt_trans(Nat.mul(Nat.div(a, 2n), Nat.div(b, 2n)), Nat.mul(a, b), C.pow2(139n), N.le_trans(Nat.mul(Nat.div(a, 2n), Nat.div(b, 2n)), Nat.mul(a, Nat.div(b, 2n)), Nat.mul(a, b), AR.mul_le(Nat.div(a, 2n), a, Nat.div(b, 2n), div2_le(a)), NF.mul_le_r(a, Nat.div(b, 2n), b, div2_le(b))), hab)
      +r = ih(Nat.div(a, 2n), Nat.div(b, 2n), 1n+c, ha2, hb2, haf2, hab2)
      Equal.trans(Nat, ntw(g, Nat.div(a, 2n), Nat.div(b, 2n), 1n+c, nev2(Nat.div(a, 2n), Nat.div(b, 2n))), ndbl(c, Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)))), ndbl(c, M.gcd(a, b)), r, Equal.cong(Nat, Nat, t => ndbl(c, t), Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), M.gcd(a, b), Equal.sym(Nat, M.gcd(a, b), Nat.add(M.gcd(Nat.div(a, 2n), Nat.div(b, 2n)), M.gcd(Nat.div(a, 2n), Nat.div(b, 2n))), gcd_twice(a, b, ea, eb))))
    case False{}:
      +ha140 = N.lt_le_trans(a, C.pow2(1n+g), C.pow2(140n), haf, N.pow2_mono(1n+g, 140n, hf))
      Equal.cong(Nat, Nat, t => ndbl(c, t), nbloop(140n, nstrip(a), b, iz(b), nsm(nstrip(a), b)), M.gcd(a, b), tw_exit(a, b, ha0, ha140, hab, hev, hb0, b, {==}))

# halving while both are even: ntw computes 2^c gcd(a, b) (as c doublings)
def tw(f: Nat, +a: Nat, +b: Nat, +c: Nat, +ha0: {Nat.is_lt(0n, a) == True{} : Bool}, +hb0: {Nat.is_lt(0n, b) == True{} : Bool}, +haf: {Nat.is_lt(a, C.pow2(f)) == True{} : Bool}, +hf: {Nat.is_le(f, 140n) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), C.pow2(139n)) == True{} : Bool}) -> {ntw(f, a, b, c, nev2(a, b)) == ndbl(c, M.gcd(a, b)) : Nat}:
  match f:
    case 0n:
      Empty.absurd({ntw(0n, a, b, c, nev2(a, b)) == ndbl(c, M.gcd(a, b)) : Nat}, pos_absurd1(a, ha0, haf))
    case 1n+ +g:
      +hg = N.le_trans(g, 1n+g, 140n, N.le_succ(g), hf)
      tw_case(g, a, b, c, ha0, hb0, haf, hf, hab, a2 => b2 => c2 => ha2 => hb2 => haf2 => hab2 => tw(g, a2, b2, c2, ha2, hb2, haf2, hg, hab2), nev2(a, b), {==})

# ---- the whole binary gcd ----

def top_r(+w: Nat, +hw: {Nat.is_le(Nat.add(w, w), 139n) == True{} : Bool}, +hw140: {Nat.is_le(w, 140n) == True{} : Bool}, +a: Nat, +bp: Nat, +hb: {Nat.is_lt(1n+bp, C.pow2(w)) == True{} : Bool}, +rv: Nat, +hr: {Nat.mod(a, 1n+bp) == rv : Nat}) -> {nbg_b(1n+bp, Nat.mod(a, 1n+bp), iz(Nat.mod(a, 1n+bp))) == M.gcd(a, 1n+bp) : Nat}:
  match rv:
    case 0n:
      +e1 = Equal.trans(Nat, M.gcd(a, 1n+bp), M.gcd(1n+bp, Nat.mod(a, 1n+bp)), M.gcd(1n+bp, 0n), gcd_rec(a, bp), Equal.cong(Nat, Nat, t => M.gcd(1n+bp, t), Nat.mod(a, 1n+bp), 0n, hr))
      %Equal.sym(Nat, Nat.mod(a, 1n+bp), 0n, hr) : {nbg_b(1n+bp, _, iz(_)) == M.gcd(a, 1n+bp) : Nat}
      Equal.sym(Nat, M.gcd(a, 1n+bp), 1n+bp, e1)
    case 1n+rp:
      +hrl = Equal.trans(Bool, Nat.is_lt(1n+rp, 1n+bp), Nat.is_lt(Nat.mod(a, 1n+bp), 1n+bp), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, 1n+bp), 1n+rp, Nat.mod(a, 1n+bp), Equal.sym(Nat, Nat.mod(a, 1n+bp), 1n+rp, hr)), MS.divmod_lt(a, bp))
      +hsq = mul_lt_sq(1n+bp, 1n+rp, C.pow2(w), hb, N.lt_trans(1n+rp, 1n+bp, C.pow2(w), hrl, hb))
      +hab = N.lt_le_trans(Nat.mul(1n+bp, 1n+rp), Nat.mul(C.pow2(w), C.pow2(w)), C.pow2(139n), hsq, N.le_trans(Nat.mul(C.pow2(w), C.pow2(w)), C.pow2(Nat.add(w, w)), C.pow2(139n), N.eq_le(Nat.mul(C.pow2(w), C.pow2(w)), C.pow2(Nat.add(w, w)), Equal.sym(Nat, C.pow2(Nat.add(w, w)), Nat.mul(C.pow2(w), C.pow2(w)), RT.pow2_add(w, w))), N.pow2_mono(Nat.add(w, w), 139n, hw)))
      +hb140 = N.lt_le_trans(1n+bp, C.pow2(w), C.pow2(140n), hb, N.pow2_mono(w, 140n, hw140))
      +t = tw(140n, 1n+bp, 1n+rp, 0n, {==}, {==}, hb140, {==}, hab)
      +e2 = Equal.trans(Nat, M.gcd(1n+bp, 1n+rp), M.gcd(1n+bp, Nat.mod(a, 1n+bp)), M.gcd(a, 1n+bp), Equal.cong(Nat, Nat, t => M.gcd(1n+bp, t), 1n+rp, Nat.mod(a, 1n+bp), Equal.sym(Nat, Nat.mod(a, 1n+bp), 1n+rp, hr)), Equal.sym(Nat, M.gcd(a, 1n+bp), M.gcd(1n+bp, Nat.mod(a, 1n+bp)), gcd_rec(a, bp)))
      %Equal.sym(Nat, Nat.mod(a, 1n+bp), 1n+rp, hr) : {nbg_b(1n+bp, _, iz(_)) == M.gcd(a, 1n+bp) : Nat}
      Equal.trans(Nat, ntw(140n, 1n+bp, 1n+rp, 0n, nev2(1n+bp, 1n+rp)), M.gcd(1n+bp, 1n+rp), M.gcd(a, 1n+bp), t, e2)

# the binary gcd of a, b < 2^w (w + w <= 139) is gcd(a, b)
def nbin_gcd(+w: Nat, +hw: {Nat.is_le(Nat.add(w, w), 139n) == True{} : Bool}, +hw140: {Nat.is_le(w, 140n) == True{} : Bool}, +a: Nat, +b: Nat, +hb: {Nat.is_lt(b, C.pow2(w)) == True{} : Bool}) -> {nbin(a, b) == M.gcd(a, b) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+ +bp:
      top_r(w, hw, hw140, a, bp, hb, Nat.mod(a, 1n+bp), {==})
