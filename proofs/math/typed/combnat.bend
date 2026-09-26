import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/natural.bend as S
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/arith.bend as AR2
import ../natural/bits.bend as BT
import ../natural/fact.bend as FA
import ../natural/gcd.bend as GC
import ../natural/lcm.bend as LC
import ./natfuel.bend as NF

# Binomial facts behind the generic comb loop (Lean 4 Mathlib
# Mathlib/Data/Nat/Choose/Basic and Central: Nat.choose_le_succ_of_lt_half_left,
# Nat.choose_le_choose, Nat.four_pow_le_two_mul_self_mul_centralBinom in its
# weaker 2^n <= C(2n, n) form; Mathlib/Data/Nat/GCD/Basic:
# Nat.Coprime.dvd_of_dvd_mul_left, Euclid's lemma, via Nat.gcd_mul_left).

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  NF.true_ne_false(h)

# ---- a c <= b c with c > 0 gives a <= b ----

def le_cancel_c(+a: Nat, +b: Nat, +cp: Nat, +h: {Nat.is_le(Nat.mul(a, 1n+cp), Nat.mul(b, 1n+cp)) == True{} : Bool}, +d: Bool, +hd: {Nat.is_lt(b, a) == d : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match d:
    case True{}:
      +x = Nat.mul(b, 1n+cp)
      +h1 = N.le_trans(Nat.add(1n+cp, x), Nat.mul(a, 1n+cp), x, AR2.mul_le(1n+b, a, 1n+cp, N.lt_succ_le_succ(b, a, hd)), h)
      +h2 = L.subst(Nat, z => {Nat.is_le(z, x) == True{} : Bool}, Nat.add(1n+cp, x), Nat.add(x, 1n+cp), N.add_comm(1n+cp, x), h1)
      Empty.absurd({Nat.is_le(a, b) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.add(x, 1n+cp), x), False{}, Equal.sym(Bool, Nat.is_le(Nat.add(x, 1n+cp), x), True{}, h2), BT.add_succ_nle(x, cp))))
    case False{}:
      N.not_lt_le(b, a, hd)

def le_cancel(+a: Nat, +b: Nat, +cp: Nat, +h: {Nat.is_le(Nat.mul(a, 1n+cp), Nat.mul(b, 1n+cp)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  le_cancel_c(a, b, cp, h, Nat.is_lt(b, a), {==})

# ---- C(n, i) grows up to n / 2 ----

# 1 + 2 i == i + (1 + i), so (1 + 2 i) - i == 1 + i
def sub_half(+i: Nat) -> {Nat.sub(1n+Nat.double(i), i) == 1n+i : Nat}:
  +e = Equal.trans(Nat, 1n+Nat.double(i), 1n+Nat.add(i, i), Nat.add(i, 1n+i), Equal.cong(Nat, Nat, t => 1n+t, Nat.double(i), Nat.add(i, i), NA.double_self(i)), Equal.sym(Nat, Nat.add(i, 1n+i), 1n+Nat.add(i, i), NA.add_succ(i, i)))
  Equal.trans(Nat, Nat.sub(1n+Nat.double(i), i), Nat.sub(Nat.add(i, 1n+i), i), 1n+i, Equal.cong(Nat, Nat, t => Nat.sub(t, i), 1n+Nat.double(i), Nat.add(i, 1n+i), e), N.add_sub_cancel(i, 1n+i))

# 1 + 2 i <= n gives C(n, i) <= C(n, 1 + i)
def cstep(+n: Nat, +i: Nat, +h: {Nat.is_le(1n+Nat.double(i), n) == True{} : Bool}) -> {Nat.is_le(S.choose(n, i), S.choose(n, 1n+i)) == True{} : Bool}:
  +c = S.choose(n, i)
  +c1 = S.choose(n, 1n+i)
  +hs = L.subst(Nat, z => {Nat.is_le(z, Nat.sub(n, i)) == True{} : Bool}, Nat.sub(1n+Nat.double(i), i), 1n+i, sub_half(i), NF.sub_mono_l(1n+Nat.double(i), n, i, h))
  +h1 = NF.mul_le_r(c, 1n+i, Nat.sub(n, i), hs)
  +h2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(c, 1n+i), z) == True{} : Bool}, Nat.mul(c, Nat.sub(n, i)), Nat.mul(c1, 1n+i), Equal.sym(Nat, Nat.mul(c1, 1n+i), Nat.mul(c, Nat.sub(n, i)), FA.choose_succ_right(n, i)), h1)
  le_cancel(c, c1, i, h2)

# 2 (i + d) <= n gives C(n, i) <= C(n, i + d)
def cmono_d(+n: Nat, +i: Nat, +d: Nat, +h: {Nat.is_le(Nat.double(Nat.add(i, d)), n) == True{} : Bool}) -> {Nat.is_le(S.choose(n, i), S.choose(n, Nat.add(i, d))) == True{} : Bool}:
  match d:
    case 0n:
      L.subst(Nat, z => {Nat.is_le(S.choose(n, i), S.choose(n, z)) == True{} : Bool}, i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i)), N.le_refl(S.choose(n, i)))
    case 1n+ +dp:
      +s = Nat.add(i, dp)
      +es = NA.add_succ(i, dp)
      +h1 = L.subst(Nat, z => {Nat.is_le(Nat.double(z), n) == True{} : Bool}, Nat.add(i, 1n+dp), 1n+s, es, h)
      +h2 = N.le_trans(1n+Nat.double(s), Nat.double(1n+s), n, N.le_trans(1n+Nat.double(s), 2n+Nat.double(s), Nat.double(1n+s), N.le_succ(1n+Nat.double(s)), L.subst(Nat, z => {Nat.is_le(2n+Nat.double(s), z) == True{} : Bool}, Nat.add(2n, Nat.double(s)), Nat.double(1n+s), Equal.sym(Nat, Nat.double(1n+s), Nat.add(2n, Nat.double(s)), N.double_succ(s)), N.le_refl(2n+Nat.double(s)))), h1)
      +h3 = N.le_trans(Nat.double(s), 1n+Nat.double(s), n, N.le_succ(Nat.double(s)), h2)
      +c = N.le_trans(S.choose(n, i), S.choose(n, s), S.choose(n, 1n+s), cmono_d(n, i, dp, h3), cstep(n, s, h2))
      L.subst(Nat, z => {Nat.is_le(S.choose(n, i), S.choose(n, z)) == True{} : Bool}, 1n+s, Nat.add(i, 1n+dp), Equal.sym(Nat, Nat.add(i, 1n+dp), 1n+s, es), c)

# i <= k, 2 k <= n give C(n, i) <= C(n, k)
def cmono(+n: Nat, +i: Nat, +k: Nat, +hi: {Nat.is_le(i, k) == True{} : Bool}, +hk: {Nat.is_le(Nat.double(k), n) == True{} : Bool}) -> {Nat.is_le(S.choose(n, i), S.choose(n, k)) == True{} : Bool}:
  +ek = N.sub_add(k, i, hi)
  +h1 = L.subst(Nat, z => {Nat.is_le(Nat.double(z), n) == True{} : Bool}, k, Nat.add(i, Nat.sub(k, i)), Equal.sym(Nat, Nat.add(i, Nat.sub(k, i)), k, ek), hk)
  L.subst(Nat, z => {Nat.is_le(S.choose(n, i), S.choose(n, z)) == True{} : Bool}, Nat.add(i, Nat.sub(k, i)), k, ek, cmono_d(n, i, Nat.sub(k, i), h1))

# ---- C(m, j) grows with m, and 2^i <= C(2 i, i) ----

def cn_mono(+m: Nat, +j: Nat) -> {Nat.is_le(S.choose(m, j), S.choose(1n+m, j)) == True{} : Bool}:
  match m j:
    case 0n 0n:
      {==}
    case 0n 1n+jp:
      N.zero_le(S.choose(1n, 1n+jp))
    case 1n+mp 0n:
      {==}
    case 1n+ +mp 1n+ +jp:
      +a = S.choose(1n+mp, jp)
      +b = S.choose(1n+mp, 1n+jp)
      L.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, Nat.add(b, a), Nat.add(a, b), N.add_comm(b, a), N.le_add_right(b, a))

def cn_mono_d(+m: Nat, +d: Nat, +j: Nat) -> {Nat.is_le(S.choose(m, j), S.choose(Nat.add(d, m), j)) == True{} : Bool}:
  match d:
    case 0n:
      N.le_refl(S.choose(m, j))
    case 1n+ +dp:
      N.le_trans(S.choose(m, j), S.choose(Nat.add(dp, m), j), S.choose(1n+Nat.add(dp, m), j), cn_mono_d(m, dp, j), cn_mono(Nat.add(dp, m), j))

def central(+i: Nat) -> {Nat.is_le(C.pow2(i), S.choose(Nat.double(i), i)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+ +ip:
      +m = {1n+Nat.double(ip) : Nat}
      +y = S.choose(m, ip)
      +hs = L.subst(Nat, z => {S.choose(m, z) == y : Nat}, Nat.sub(m, ip), 1n+ip, sub_half(ip), FA.choose_symm(m, ip, N.le_trans(ip, Nat.double(ip), m, N.double_self_le(ip), N.le_succ(Nat.double(ip)))))
      +e2 = Equal.trans(Nat, Nat.add(y, S.choose(m, 1n+ip)), Nat.add(y, y), Nat.double(y), Equal.cong(Nat, Nat, t => Nat.add(y, t), S.choose(m, 1n+ip), y, hs), Equal.sym(Nat, Nat.double(y), Nat.add(y, y), NA.double_self(y)))
      +h1 = N.double_le(C.pow2(ip), y, N.le_trans(C.pow2(ip), S.choose(Nat.double(ip), ip), y, central(ip), cn_mono(Nat.double(ip), ip)))
      +h2 = L.subst(Nat, z => {Nat.is_le(Nat.double(C.pow2(ip)), z) == True{} : Bool}, Nat.double(y), Nat.add(y, S.choose(m, 1n+ip)), Equal.sym(Nat, Nat.add(y, S.choose(m, 1n+ip)), Nat.double(y), e2), h1)
      L.subst(Nat, z => {Nat.is_le(Nat.double(C.pow2(ip)), S.choose(z, 1n+ip)) == True{} : Bool}, Nat.add(2n, Nat.double(ip)), Nat.double(1n+ip), Equal.sym(Nat, Nat.double(1n+ip), Nat.add(2n, Nat.double(ip)), N.double_succ(ip)), h2)

# K <= i, 2 i <= n give 2^K <= C(n, i)
def cbig(+K: Nat, +n: Nat, +i: Nat, +hK: {Nat.is_le(K, i) == True{} : Bool}, +h2: {Nat.is_le(Nat.double(i), n) == True{} : Bool}) -> {Nat.is_le(C.pow2(K), S.choose(n, i)) == True{} : Bool}:
  +d = Nat.sub(n, Nat.double(i))
  +en = Equal.trans(Nat, Nat.add(d, Nat.double(i)), Nat.add(Nat.double(i), d), n, N.add_comm(d, Nat.double(i)), N.sub_add(n, Nat.double(i), h2))
  +h3 = L.subst(Nat, z => {Nat.is_le(S.choose(Nat.double(i), i), S.choose(z, i)) == True{} : Bool}, Nat.add(d, Nat.double(i)), n, en, cn_mono_d(Nat.double(i), d, i))
  N.le_trans(C.pow2(K), C.pow2(i), S.choose(n, i), N.pow2_mono(K, i, hK), N.le_trans(C.pow2(i), S.choose(Nat.double(i), i), S.choose(n, i), central(i), h3))

# ---- the gcd-reduced step is exact (Euclid's lemma) ----

# g = gcd(c, j), c == wl g, j == wr g for j = 1 + jp
def gg(+c: Nat, +jp: Nat) -> Nat:
  M.gcd(c, 1n+jp)

def wl(+c: Nat, +jp: Nat) -> Nat:
  GC.wl(GC.ws(1n+jp, c, 1n+jp))

def wr(+c: Nat, +jp: Nat) -> Nat:
  GC.wr(GC.ws(1n+jp, c, 1n+jp))

def e_c(+c: Nat, +jp: Nat) -> {c == Nat.mul(wl(c, jp), gg(c, jp)) : Nat}:
  GC.gcd_dvd_left(c, 1n+jp)

def e_j(+c: Nat, +jp: Nat) -> {1n+jp == Nat.mul(wr(c, jp), gg(c, jp)) : Nat}:
  GC.gcd_dvd_right(c, 1n+jp)

def g_pos(+c: Nat, +jp: Nat) -> {Nat.is_lt(0n, gg(c, jp)) == True{} : Bool}:
  LC.gcd_pos(jp, wr(c, jp), gg(c, jp), e_j(c, jp))

def wr_pos(+c: Nat, +jp: Nat) -> {Nat.is_lt(0n, wr(c, jp)) == True{} : Bool}:
  LC.gcd_pos(jp, gg(c, jp), wr(c, jp), Equal.trans(Nat, 1n+jp, Nat.mul(wr(c, jp), gg(c, jp)), Nat.mul(gg(c, jp), wr(c, jp)), e_j(c, jp), NA.mul_comm(wr(c, jp), gg(c, jp))))

def div_c(+c: Nat, +jp: Nat) -> {Nat.div(c, gg(c, jp)) == wl(c, jp) : Nat}:
  LC.div_exact(c, wl(c, jp), gg(c, jp), g_pos(c, jp), e_c(c, jp))

def div_j(+c: Nat, +jp: Nat) -> {Nat.div(1n+jp, gg(c, jp)) == wr(c, jp) : Nat}:
  LC.div_exact(1n+jp, wr(c, jp), gg(c, jp), g_pos(c, jp), e_j(c, jp))

# gcd(wl, wr) == 1
def coprime(+c: Nat, +jp: Nat) -> {M.gcd(wl(c, jp), wr(c, jp)) == 1n : Nat}:
  +g = gg(c, jp)
  +a = wl(c, jp)
  +b = wr(c, jp)
  +ea = Equal.trans(Nat, Nat.mul(g, a), Nat.mul(a, g), c, NA.mul_comm(g, a), Equal.sym(Nat, c, Nat.mul(a, g), e_c(c, jp)))
  +eb = Equal.trans(Nat, Nat.mul(g, b), Nat.mul(b, g), 1n+jp, NA.mul_comm(g, b), Equal.sym(Nat, 1n+jp, Nat.mul(b, g), e_j(c, jp)))
  +e1 = Equal.trans(Nat, Nat.mul(g, M.gcd(a, b)), M.gcd(Nat.mul(g, a), Nat.mul(g, b)), g, Equal.sym(Nat, M.gcd(Nat.mul(g, a), Nat.mul(g, b)), Nat.mul(g, M.gcd(a, b)), LC.gcd_mul_left(g, a, b)), Equal.trans(Nat, M.gcd(Nat.mul(g, a), Nat.mul(g, b)), M.gcd(c, Nat.mul(g, b)), g, Equal.cong(Nat, Nat, t => M.gcd(t, Nat.mul(g, b)), Nat.mul(g, a), c, ea), Equal.cong(Nat, Nat, t => M.gcd(c, t), Nat.mul(g, b), 1n+jp, eb)))
  +e2 = Equal.trans(Nat, Nat.mul(M.gcd(a, b), g), Nat.mul(g, M.gcd(a, b)), Nat.mul(1n, g), NA.mul_comm(M.gcd(a, b), g), Equal.trans(Nat, Nat.mul(g, M.gcd(a, b)), g, Nat.mul(1n, g), e1, Equal.sym(Nat, Nat.mul(1n, g), g, LC.one_mul(g))))
  LC.cancel_pos(M.gcd(a, b), 1n, g, g_pos(c, jp), e2)

# with c' (1 + jp) == c t: wl t == c' wr
def cross(+c: Nat, +jp: Nat, +t: Nat, +c1: Nat, +e: {Nat.mul(c1, 1n+jp) == Nat.mul(c, t) : Nat}) -> {Nat.mul(wl(c, jp), t) == Nat.mul(c1, wr(c, jp)) : Nat}:
  +g = gg(c, jp)
  +a = wl(c, jp)
  +b = wr(c, jp)
  +l = Equal.trans(Nat, Nat.mul(Nat.mul(a, t), g), Nat.mul(a, Nat.mul(t, g)), Nat.mul(c, t), NA.mul_assoc(a, t, g), Equal.trans(Nat, Nat.mul(a, Nat.mul(t, g)), Nat.mul(a, Nat.mul(g, t)), Nat.mul(c, t), Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(t, g), Nat.mul(g, t), NA.mul_comm(t, g)), Equal.trans(Nat, Nat.mul(a, Nat.mul(g, t)), Nat.mul(Nat.mul(a, g), t), Nat.mul(c, t), Equal.sym(Nat, Nat.mul(Nat.mul(a, g), t), Nat.mul(a, Nat.mul(g, t)), NA.mul_assoc(a, g, t)), Equal.cong(Nat, Nat, z => Nat.mul(z, t), Nat.mul(a, g), c, Equal.sym(Nat, c, Nat.mul(a, g), e_c(c, jp))))))
  +r = Equal.trans(Nat, Nat.mul(Nat.mul(c1, b), g), Nat.mul(c1, Nat.mul(b, g)), Nat.mul(c1, 1n+jp), NA.mul_assoc(c1, b, g), Equal.cong(Nat, Nat, z => Nat.mul(c1, z), Nat.mul(b, g), 1n+jp, Equal.sym(Nat, 1n+jp, Nat.mul(b, g), e_j(c, jp))))
  LC.cancel_pos(Nat.mul(a, t), Nat.mul(c1, b), g, g_pos(c, jp), Equal.trans(Nat, Nat.mul(Nat.mul(a, t), g), Nat.mul(c, t), Nat.mul(Nat.mul(c1, b), g), l, Equal.sym(Nat, Nat.mul(Nat.mul(c1, b), g), Nat.mul(c, t), Equal.trans(Nat, Nat.mul(Nat.mul(c1, b), g), Nat.mul(c1, 1n+jp), Nat.mul(c, t), r, e))))

# the quotient t / wr
def sq(+c: Nat, +jp: Nat, +t: Nat, +c1: Nat) -> Nat:
  GC.dw(Nat.mul(t, wr(c, jp)), Nat.mul(t, wl(c, jp)), Nat.mul(t, wr(c, jp)), c1, t)

# Euclid: wr | wl t and gcd(wl, wr) == 1 give wr | t
def t_eq(+c: Nat, +jp: Nat, +t: Nat, +c1: Nat, +e: {Nat.mul(c1, 1n+jp) == Nat.mul(c, t) : Nat}) -> {t == Nat.mul(sq(c, jp, t, c1), wr(c, jp)) : Nat}:
  +a = wl(c, jp)
  +b = wr(c, jp)
  +ea = Equal.trans(Nat, Nat.mul(t, a), Nat.mul(a, t), Nat.mul(c1, b), NA.mul_comm(t, a), cross(c, jp, t, c1, e))
  +d = GC.dvd_gcd(Nat.mul(t, a), Nat.mul(t, b), b, c1, t, ea, {==})
  +g1 = Equal.trans(Nat, M.gcd(Nat.mul(t, a), Nat.mul(t, b)), Nat.mul(t, M.gcd(a, b)), t, LC.gcd_mul_left(t, a, b), Equal.trans(Nat, Nat.mul(t, M.gcd(a, b)), Nat.mul(t, 1n), t, Equal.cong(Nat, Nat, z => Nat.mul(t, z), M.gcd(a, b), 1n, coprime(c, jp)), NA.mul_one(t)))
  Equal.trans(Nat, t, M.gcd(Nat.mul(t, a), Nat.mul(t, b)), Nat.mul(sq(c, jp, t, c1), b), Equal.sym(Nat, M.gcd(Nat.mul(t, a), Nat.mul(t, b)), t, g1), d)

def div_t(+c: Nat, +jp: Nat, +t: Nat, +c1: Nat, +e: {Nat.mul(c1, 1n+jp) == Nat.mul(c, t) : Nat}) -> {Nat.div(t, wr(c, jp)) == sq(c, jp, t, c1) : Nat}:
  LC.div_exact(t, sq(c, jp, t, c1), wr(c, jp), wr_pos(c, jp), t_eq(c, jp, t, c1, e))

# (c / g) (t / (j / g)) == c'
def prod_eq(+c: Nat, +jp: Nat, +t: Nat, +c1: Nat, +e: {Nat.mul(c1, 1n+jp) == Nat.mul(c, t) : Nat}) -> {Nat.mul(wl(c, jp), sq(c, jp, t, c1)) == c1 : Nat}:
  +a = wl(c, jp)
  +b = wr(c, jp)
  +s = sq(c, jp, t, c1)
  +h1 = Equal.trans(Nat, Nat.mul(Nat.mul(a, s), b), Nat.mul(a, Nat.mul(s, b)), Nat.mul(c1, b), NA.mul_assoc(a, s, b), Equal.trans(Nat, Nat.mul(a, Nat.mul(s, b)), Nat.mul(a, t), Nat.mul(c1, b), Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(s, b), t, Equal.sym(Nat, t, Nat.mul(s, b), t_eq(c, jp, t, c1, e))), cross(c, jp, t, c1, e)))
  LC.cancel_pos(Nat.mul(a, s), c1, b, wr_pos(c, jp), h1)
