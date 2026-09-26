import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./u32.bend as U32P
import ../../lib/arith.bend as AR2
import ../natural/bits.bend as BT
import ../natural/inverse.bend as IV
import ../../lib/u32half.bend as UH
import ../../../spec/math/natural.bend as S
import ../natural/fact.bend as FA
import ../natural/roots.bend as RT
import ../natural/modpow.bend as MP

# Fuel for the loops of src/math/generic.bend: the generic functions run a
# fixed 140 steps where the proved Nat functions of natural.bend run as many
# steps as their argument; for values below 2^64 both reach the end of the
# loop, so they agree. The Euclid bound is Knuth's (TAOCP 4.5.3, the
# remainder at least halves every two steps: Lame's theorem in its simple
# form), as in Isabelle's HOL-Number_Theory and Why3's gcd examples.

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  U32P.true_ne_false(h)

# ---- Euclid ----

# the Nat loop reaches b == 0 within f steps
def ends(f: Nat, +a: Nat, +b: Nat) -> Bool:
  match f b:
    case 0n 0n:
      True{}
    case 0n 1n+bp:
      False{}
    case 1n+g 0n:
      True{}
    case 1n+g 1n+ +bp:
      ends(g, 1n+bp, Nat.mod(a, 1n+bp))

def ends_zero(+f: Nat, +a: Nat) -> {ends(f, a, 0n) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# two fuels that both reach the end give the same gcd
def gz(+f: Nat, +a: Nat) -> {M.gcd_go(f, a, 0n) == a : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def gcd_fuel(+f1: Nat, +f2: Nat, +a: Nat, +b: Nat, +h1: {ends(f1, a, b) == True{} : Bool}, +h2: {ends(f2, a, b) == True{} : Bool}) -> {M.gcd_go(f1, a, b) == M.gcd_go(f2, a, b) : Nat}:
  match f1 f2 b:
    case 0n _ 0n:
      Equal.sym(Nat, M.gcd_go(f2, a, 0n), a, gz(f2, a))
    case 0n _ 1n+bp:
      Empty.absurd({M.gcd_go(0n, a, 1n+bp) == M.gcd_go(f2, a, 1n+bp) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n+g1 _ 0n:
      Equal.sym(Nat, M.gcd_go(f2, a, 0n), a, gz(f2, a))
    case 1n+g1 0n 1n+bp:
      Empty.absurd({M.gcd_go(1n+g1, a, 1n+bp) == M.gcd_go(0n, a, 1n+bp) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))
    case 1n+ +g1 1n+ +g2 1n+ +bp:
      gcd_fuel(g1, g2, 1n+bp, Nat.mod(a, 1n+bp), h1, h2)

# b <= f is enough: b drops every step
def ends_self(+f: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(b, f) == True{} : Bool}) -> {ends(f, a, b) == True{} : Bool}:
  match f b:
    case _ 0n:
      ends_zero(f, a)
    case 0n 1n+bp:
      Empty.absurd({ends(0n, a, 1n+bp) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+ +g 1n+ +bp:
      ends_self(g, 1n+bp, Nat.mod(a, 1n+bp), N.lt_succ_le(Nat.mod(a, 1n+bp), g, N.lt_le_trans(Nat.mod(a, 1n+bp), 1n+bp, 1n+g, NR.dm_lt(bp, a), h)))

# b mod r + r <= b for 0 < r <= b (the quotient is at least 1)
def mod_le_sub(+b: Nat, +rp: Nat, +h: {Nat.is_le(1n+rp, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mod(b, 1n+rp), 1n+rp), b) == True{} : Bool}:
  +q = Nat.div(b, 1n+rp)
  +m = Nat.mod(b, 1n+rp)
  +e = NR.dm_eq(rp, b)
  +m1 = Equal.trans(Nat, Nat.mul(1n, 1n+rp), Nat.add(1n+rp, 0n), 1n+rp, {==}, N.add_zero(1n+rp))
  +hq = Equal.trans(Bool, Nat.is_le(1n, q), Nat.is_le(Nat.mul(1n, 1n+rp), b), True{}, NR.le_div(rp, 1n, b), L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, 1n+rp, Nat.mul(1n, 1n+rp), Equal.sym(Nat, Nat.mul(1n, 1n+rp), 1n+rp, m1), h))
  +le1 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(q, 1n+rp)) == True{} : Bool}, Nat.mul(1n, 1n+rp), 1n+rp, m1, AR2.mul_le(1n, q, 1n+rp, hq))
  +le2 = N.le_add_left(1n+rp, Nat.mul(q, 1n+rp), m, le1)
  +le3 = L.subst(Nat, z => {Nat.is_le(Nat.add(m, 1n+rp), z) == True{} : Bool}, Nat.add(m, Nat.mul(q, 1n+rp)), b, Equal.trans(Nat, Nat.add(m, Nat.mul(q, 1n+rp)), Nat.add(Nat.mul(q, 1n+rp), m), b, NA.add_comm(m, Nat.mul(q, 1n+rp)), Equal.sym(Nat, b, Nat.add(Nat.mul(q, 1n+rp), m), e)), le2)
  le3

# two remainders later the divisor has at least halved
def halve2(+b: Nat, +r1: Nat, +r2: Nat, +k: Nat, +hb: {Nat.is_lt(b, Nat.double(k)) == True{} : Bool}, +h21: {Nat.is_lt(r2, r1) == True{} : Bool}, +hs: {Nat.is_le(Nat.add(r2, r1), b) == True{} : Bool}) -> {Nat.is_lt(r2, k) == True{} : Bool}:
  +a1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(r2, r1)) == True{} : Bool}, Nat.add(r2, r2), Nat.double(r2), Equal.sym(Nat, Nat.double(r2), Nat.add(r2, r2), NA.double_self(r2)), N.lt_add_left(r2, r1, r2, h21))
  +a2 = N.lt_le_trans(Nat.double(r2), Nat.add(r2, r1), b, a1, hs)
  N.bit_double_lt(False{}, r2, k, N.lt_trans(Nat.double(r2), b, Nat.double(k), a2, hb))

# Knuth: b < 2^k and 2k + 1 <= f reach the end (r is a mod b, given)
def halve(+k: Nat, +f: Nat, +a: Nat, +b: Nat, +r: Nat, +hr: {Nat.mod(a, b) == r : Nat}, +hb: {Nat.is_lt(b, C.pow2(k)) == True{} : Bool}, +hf: {Nat.is_le(1n+Nat.double(k), f) == True{} : Bool}) -> {ends(f, a, b) == True{} : Bool}:
  match k f b r:
    case 0n _ 0n _:
      ends_zero(f, a)
    case 0n _ 1n+bp _:
      Empty.absurd({ends(f, a, 1n+bp) == True{} : Bool}, N.lt_zero_absurd(bp, hb))
    case 1n+j _ 0n _:
      ends_zero(f, a)
    case 1n+j 0n 1n+bp _:
      Empty.absurd({ends(0n, a, 1n+bp) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hf)))
    case 1n+j 1n 1n+bp _:
      Empty.absurd({ends(1n, a, 1n+bp) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hf)))
    case 1n+j 2n+ +h 1n+ +bp 0n:
      %Equal.sym(Nat, Nat.mod(a, 1n+bp), 0n, hr) : {ends(1n+h, 1n+bp, _) == True{} : Bool}
      ends_zero(1n+h, 1n+bp)
    case 1n+ +j 2n+ +h 1n+ +bp 1n+ +rp:
      %Equal.sym(Nat, Nat.mod(a, 1n+bp), 1n+rp, hr) : {ends(1n+h, 1n+bp, _) == True{} : Bool}
      +r2 = Nat.mod(1n+bp, 1n+rp)
      +h21 = NR.dm_lt(rp, 1n+bp)
      +hlt = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, Nat.mod(a, 1n+bp), 1n+rp, hr, NR.dm_lt(bp, a))
      +hs = mod_le_sub(1n+bp, rp, N.lt_le(1n+rp, 1n+bp, hlt))
      +hb2 = halve2(1n+bp, 1n+rp, r2, C.pow2(j), hb, h21, hs)
      halve(j, h, 1n+rp, r2, Nat.mod(1n+rp, r2), {==}, hb2, hf)

# 140 steps are enough for Euclid on values below 2^k, 2k + 1 <= 140
def gcd_140(+k: Nat, +a: Nat, +b: Nat, +hk: {Nat.is_le(1n+Nat.double(k), 140n) == True{} : Bool}, +hb: {Nat.is_lt(b, C.pow2(k)) == True{} : Bool}) -> {M.gcd_go(140n, a, b) == M.gcd(a, b) : Nat}:
  gcd_fuel(140n, b, a, b, halve(k, 140n, a, b, Nat.mod(a, b), {==}, hb, hk), ends_self(b, a, b, N.le_refl(b)))

# ---- halving loops (bit_length, pow_mod): n reaches 0 within f halvings ----

def bends(f: Nat, +n: Nat) -> Bool:
  match f n:
    case 0n 0n:
      True{}
    case 0n 1n+np:
      False{}
    case 1n+g 0n:
      True{}
    case 1n+g 1n+ +np:
      bends(g, Nat.div(1n+np, 2n))

def bends_zero(+f: Nat) -> {bends(f, 0n) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# div(n, 2) < p when n < 2p
def half_below(+n: Nat, +p: Nat, +h: {Nat.is_lt(n, Nat.double(p)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 2n), p) == True{} : Bool}:
  +e = BT.half_eq(n)
  +le = L.subst(Nat, z => {Nat.is_le(Nat.double(Nat.div(n, 2n)), z) == True{} : Bool}, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), n, Equal.sym(Nat, n, Nat.add(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)), e), N.le_add_right(Nat.double(Nat.div(n, 2n)), Nat.mod(n, 2n)))
  N.bit_double_lt(False{}, Nat.div(n, 2n), p, N.le_lt_trans(Nat.double(Nat.div(n, 2n)), n, Nat.double(p), le, h))

# n < 2^j and j <= f: f halvings reach 0
def bends_bound(+j: Nat, +f: Nat, +n: Nat, +hn: {Nat.is_lt(n, C.pow2(j)) == True{} : Bool}, +hf: {Nat.is_le(j, f) == True{} : Bool}) -> {bends(f, n) == True{} : Bool}:
  match j f n:
    case _ _ 0n:
      bends_zero(f)
    case 0n _ 1n+np:
      Empty.absurd({bends(f, 1n+np) == True{} : Bool}, N.lt_zero_absurd(np, hn))
    case 1n+i 0n 1n+np:
      Empty.absurd({bends(0n, 1n+np) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hf)))
    case 1n+ +i 1n+ +g 1n+ +np:
      bends_bound(i, g, Nat.div(1n+np, 2n), half_below(1n+np, C.pow2(i), hn), hf)

# n <= f is enough (n drops every step)
def bends_self(+f: Nat, +n: Nat, +h: {Nat.is_le(n, f) == True{} : Bool}) -> {bends(f, n) == True{} : Bool}:
  match f n:
    case _ 0n:
      bends_zero(f)
    case 0n 1n+np:
      Empty.absurd({bends(0n, 1n+np) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+ +g 1n+ +np:
      bends_self(g, Nat.div(1n+np, 2n), N.lt_succ_le(Nat.div(1n+np, 2n), g, N.lt_le_trans(Nat.div(1n+np, 2n), 1n+np, 1n+g, BT.half_lt(np), h)))

def bl_zero(+f: Nat, +k: Nat) -> {M.bit_length_go(f, 0n, k) == k : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def bl_fuel(+f1: Nat, +f2: Nat, +n: Nat, +k: Nat, +h1: {bends(f1, n) == True{} : Bool}, +h2: {bends(f2, n) == True{} : Bool}) -> {M.bit_length_go(f1, n, k) == M.bit_length_go(f2, n, k) : Nat}:
  match f1 f2 n:
    case _ _ 0n:
      Equal.trans(Nat, M.bit_length_go(f1, 0n, k), k, M.bit_length_go(f2, 0n, k), bl_zero(f1, k), Equal.sym(Nat, M.bit_length_go(f2, 0n, k), k, bl_zero(f2, k)))
    case 0n _ 1n+np:
      Empty.absurd({M.bit_length_go(0n, 1n+np, k) == M.bit_length_go(f2, 1n+np, k) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n+g1 0n 1n+np:
      Empty.absurd({M.bit_length_go(1n+g1, 1n+np, k) == M.bit_length_go(0n, 1n+np, k) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))
    case 1n+ +g1 1n+ +g2 1n+ +np:
      bl_fuel(g1, g2, Nat.div(1n+np, 2n), 1n+k, h1, h2)

# 140 steps suffice for bit_length below 2^j, j <= 140
def bl_140(+j: Nat, +n: Nat, +hj: {Nat.is_le(j, 140n) == True{} : Bool}, +hn: {Nat.is_lt(n, C.pow2(j)) == True{} : Bool}) -> {M.bit_length_go(140n, n, 0n) == M.bit_length(n) : Nat}:
  bl_fuel(140n, n, n, 0n, bends_bound(j, 140n, n, hn, hj), bends_self(n, n, N.le_refl(n)))

def pm_zero(+f: Nat, +m: Nat, +base: Nat, +acc: Nat) -> {M.pow_mod_go(f, m, 0n, base, acc) == acc : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def pm_fuel(+f1: Nat, +f2: Nat, +m: Nat, +e: Nat, +base: Nat, +acc: Nat, +h1: {bends(f1, e) == True{} : Bool}, +h2: {bends(f2, e) == True{} : Bool}) -> {M.pow_mod_go(f1, m, e, base, acc) == M.pow_mod_go(f2, m, e, base, acc) : Nat}:
  match f1 f2 e:
    case _ _ 0n:
      Equal.trans(Nat, M.pow_mod_go(f1, m, 0n, base, acc), acc, M.pow_mod_go(f2, m, 0n, base, acc), pm_zero(f1, m, base, acc), Equal.sym(Nat, M.pow_mod_go(f2, m, 0n, base, acc), acc, pm_zero(f2, m, base, acc)))
    case 0n _ 1n+ep:
      Empty.absurd({M.pow_mod_go(0n, m, 1n+ep, base, acc) == M.pow_mod_go(f2, m, 1n+ep, base, acc) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n+g1 0n 1n+ep:
      Empty.absurd({M.pow_mod_go(1n+g1, m, 1n+ep, base, acc) == M.pow_mod_go(0n, m, 1n+ep, base, acc) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))
    case 1n+ +g1 1n+ +g2 1n+ +ep:
      pm_fuel(g1, g2, m, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(base, base), m), M.pow_mod_odd(m, Nat.mod(1n+ep, 2n), base, acc), h1, h2)

def pm_140(+j: Nat, +m: Nat, +e: Nat, +base: Nat, +acc: Nat, +hj: {Nat.is_le(j, 140n) == True{} : Bool}, +he: {Nat.is_lt(e, C.pow2(j)) == True{} : Bool}) -> {M.pow_mod_go(140n, m, e, base, acc) == M.pow_mod_go(e, m, e, base, acc) : Nat}:
  pm_fuel(140n, e, m, e, base, acc, bends_bound(j, 140n, e, he, hj), bends_self(e, e, N.le_refl(e)))

# ---- extended Euclid (mod_inverse): the remainders follow gcd_go ----

def iv_zero(+f: Nat, +m: Nat, +r0: Nat, +s0: Nat, +s1: Nat) -> {M.inv_go(f, m, r0, s0, 0n, s1) == M.BZ{r0, s0} : M.Bezout}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def inv_fuel(+f1: Nat, +f2: Nat, +m: Nat, +r0: Nat, +s0: Nat, +r1: Nat, +s1: Nat, +h1: {ends(f1, r0, r1) == True{} : Bool}, +h2: {ends(f2, r0, r1) == True{} : Bool}) -> {M.inv_go(f1, m, r0, s0, r1, s1) == M.inv_go(f2, m, r0, s0, r1, s1) : M.Bezout}:
  match f1 f2 r1:
    case 0n _ 0n:
      Equal.sym(M.Bezout, M.inv_go(f2, m, r0, s0, 0n, s1), M.BZ{r0, s0}, iv_zero(f2, m, r0, s0, s1))
    case 0n _ 1n+rp:
      Empty.absurd({M.inv_go(0n, m, r0, s0, 1n+rp, s1) == M.inv_go(f2, m, r0, s0, 1n+rp, s1) : M.Bezout}, true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n+g1 _ 0n:
      Equal.sym(M.Bezout, M.inv_go(f2, m, r0, s0, 0n, s1), M.BZ{r0, s0}, iv_zero(f2, m, r0, s0, s1))
    case 1n+g1 0n 1n+rp:
      Empty.absurd({M.inv_go(1n+g1, m, r0, s0, 1n+rp, s1) == M.inv_go(0n, m, r0, s0, 1n+rp, s1) : M.Bezout}, true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))
    case 1n+ +g1 1n+ +g2 1n+ +rp:
      inv_fuel(g1, g2, m, 1n+rp, s1, Nat.mod(r0, 1n+rp), M.inv_step(m, Nat.div(r0, 1n+rp), s0, s1), h1, h2)

# fuel 140 against the reference fuel m, for m < 2^k, 2k+1 <= 140
def inv_140(+k: Nat, +mp: Nat, +a: Nat, +hk: {Nat.is_le(1n+Nat.double(k), 140n) == True{} : Bool}, +hm: {Nat.is_lt(1n+mp, C.pow2(k)) == True{} : Bool}) -> {M.inv_go(140n, 1n+mp, 1n+mp, 0n, Nat.mod(a, 1n+mp), 1n) == M.inv_go(1n+mp, 1n+mp, 1n+mp, 0n, Nat.mod(a, 1n+mp), 1n) : M.Bezout}:
  +hb = N.lt_trans(Nat.mod(a, 1n+mp), 1n+mp, C.pow2(k), NR.dm_lt(mp, a), hm)
  inv_fuel(140n, 1n+mp, 1n+mp, 1n+mp, 0n, Nat.mod(a, 1n+mp), 1n, halve(k, 140n, 1n+mp, Nat.mod(a, 1n+mp), Nat.mod(1n+mp, Nat.mod(a, 1n+mp)), {==}, hb, hk), ends_self(1n+mp, 1n+mp, Nat.mod(a, 1n+mp), N.lt_le(Nat.mod(a, 1n+mp), 1n+mp, NR.dm_lt(mp, a))))

# ---- s0 - x mod m, the two sides of submod ----

def mod_small(+mp: Nat, +d: Nat, +h: {Nat.is_lt(d, 1n+mp) == True{} : Bool}) -> {Nat.mod(d, 1n+mp) == d : Nat}:
  NR.mod_of(0n, mp, d, h)

def sm_lt(+mm: Nat, +s: Nat, +x: Nat, +h: {Nat.is_lt(s, x) == True{} : Bool}, +hx: {Nat.is_le(x, mm) == True{} : Bool}) -> {Nat.is_lt(Nat.add(s, Nat.sub(mm, x)), mm) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(s, Nat.sub(mm, x)), z) == True{} : Bool}, Nat.add(x, Nat.sub(mm, x)), mm, N.sub_add(mm, x, hx), N.lt_add_r2(s, x, Nat.sub(mm, x), h))

def sm_ge(+mp: Nat, +s: Nat, +x: Nat, +hxs: {Nat.is_le(x, s) == True{} : Bool}, +hs: {Nat.is_lt(s, 1n+mp) == True{} : Bool}) -> {Nat.mod(Nat.add(s, Nat.sub(1n+mp, x)), 1n+mp) == Nat.sub(s, x) : Nat}:
  +d = Nat.sub(s, x)
  +hxm = N.le_trans(x, s, 1n+mp, hxs, N.lt_le(s, 1n+mp, hs))
  +es = Equal.sym(Nat, Nat.add(d, x), s, Equal.trans(Nat, Nat.add(d, x), Nat.add(x, d), s, N.add_comm(d, x), N.sub_add(s, x, hxs)))
  +e1 = Equal.trans(Nat, Nat.add(s, Nat.sub(1n+mp, x)), Nat.add(Nat.add(d, x), Nat.sub(1n+mp, x)), Nat.add(d, 1n+mp), Equal.cong(Nat, Nat, t => Nat.add(t, Nat.sub(1n+mp, x)), s, Nat.add(d, x), es), Equal.trans(Nat, Nat.add(Nat.add(d, x), Nat.sub(1n+mp, x)), Nat.add(d, Nat.add(x, Nat.sub(1n+mp, x))), Nat.add(d, 1n+mp), N.add_assoc(d, x, Nat.sub(1n+mp, x)), Equal.cong(Nat, Nat, t => Nat.add(d, t), Nat.add(x, Nat.sub(1n+mp, x)), 1n+mp, N.sub_add(1n+mp, x, hxm))))
  +e2 = Equal.trans(Nat, Nat.mod(Nat.add(d, 1n+mp), 1n+mp), Nat.mod(Nat.add(d, Nat.mod(1n+mp, 1n+mp)), 1n+mp), Nat.mod(Nat.add(d, 0n), 1n+mp), Equal.sym(Nat, Nat.mod(Nat.add(d, Nat.mod(1n+mp, 1n+mp)), 1n+mp), Nat.mod(Nat.add(d, 1n+mp), 1n+mp), NR.mod_add_r(mp, d, 1n+mp)), Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(d, t), 1n+mp), Nat.mod(1n+mp, 1n+mp), 0n, IV.mod_self(mp)))
  +hd = N.le_lt_trans(d, s, 1n+mp, UH.sub_le(s, x), hs)
  Equal.trans(Nat, Nat.mod(Nat.add(s, Nat.sub(1n+mp, x)), 1n+mp), Nat.mod(Nat.add(d, 1n+mp), 1n+mp), d, Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), Nat.add(s, Nat.sub(1n+mp, x)), Nat.add(d, 1n+mp), e1), Equal.trans(Nat, Nat.mod(Nat.add(d, 1n+mp), 1n+mp), Nat.mod(Nat.add(d, 0n), 1n+mp), d, e2, Equal.trans(Nat, Nat.mod(Nat.add(d, 0n), 1n+mp), Nat.mod(d, 1n+mp), d, Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), Nat.add(d, 0n), d, N.add_zero(d)), mod_small(mp, d, hd))))

# ---- ilog: p at least doubles each round, so the loop stops within
# log2(n / b) + 1 rounds ----

def ilends(f: Nat, +q: Nat, +b: Nat, +p: Nat, +up: Bool) -> Bool:
  match f up:
    case 0n False{}:
      True{}
    case 0n True{}:
      False{}
    case 1n+g False{}:
      True{}
    case 1n+g True{}:
      ilends(g, q, b, Nat.mul(p, b), Nat.is_le(Nat.mul(p, b), q))

def il_false(+f: Nat, +q: Nat, +b: Nat, +p: Nat) -> {ilends(f, q, b, p, False{}) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def ilz(+f: Nat, +n: Nat, +b: Nat, +k: Nat, +p: Nat) -> {M.ilog_go(f, n, b, k, p, False{}) == k : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def il_fuel(+f1: Nat, +f2: Nat, +n: Nat, +b: Nat, +k: Nat, +p: Nat, +up: Bool, +h1: {ilends(f1, Nat.div(n, b), b, p, up) == True{} : Bool}, +h2: {ilends(f2, Nat.div(n, b), b, p, up) == True{} : Bool}) -> {M.ilog_go(f1, n, b, k, p, up) == M.ilog_go(f2, n, b, k, p, up) : Nat}:
  match f1 f2 up:
    case 0n _ False{}:
      Equal.sym(Nat, M.ilog_go(f2, n, b, k, p, False{}), k, ilz(f2, n, b, k, p))
    case 0n _ True{}:
      Empty.absurd({M.ilog_go(0n, n, b, k, p, True{}) == M.ilog_go(f2, n, b, k, p, True{}) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n+g1 _ False{}:
      Equal.sym(Nat, M.ilog_go(f2, n, b, k, p, False{}), k, ilz(f2, n, b, k, p))
    case 1n+g1 0n True{}:
      Empty.absurd({M.ilog_go(1n+g1, n, b, k, p, True{}) == M.ilog_go(0n, n, b, k, p, True{}) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h2)))
    case 1n+ +g1 1n+ +g2 True{}:
      il_fuel(g1, g2, n, b, 1n+k, Nat.mul(p, b), Nat.is_le(Nat.mul(p, b), Nat.div(n, b)), h1, h2)

def pow2_pos(+x: Nat) -> {Nat.is_le(1n, C.pow2(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      N.le_trans(1n, C.pow2(y), Nat.double(C.pow2(y)), pow2_pos(y), N.double_self_le(C.pow2(y)))

def lt_pow2(+x: Nat) -> {Nat.is_lt(x, C.pow2(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      N.lt_le_trans(1n+y, 1n+C.pow2(y), Nat.double(C.pow2(y)), lt_pow2(y), N.double_succ_le(C.pow2(y), pow2_pos(y)))

def dbl_le_mul(+p: Nat, +bq: Nat) -> {Nat.is_le(Nat.double(p), Nat.mul(p, 2n+bq)) == True{} : Bool}:
  +r = Nat.add(p, Nat.add(p, Nat.mul(p, bq)))
  +em = Equal.trans(Nat, Nat.mul(p, 2n+bq), Nat.add(p, Nat.mul(p, 1n+bq)), r, NA.mul_succ(p, 1n+bq), Equal.cong(Nat, Nat, t => Nat.add(p, t), Nat.mul(p, 1n+bq), Nat.add(p, Nat.mul(p, bq)), NA.mul_succ(p, bq)))
  +h0 = N.le_add_left(p, Nat.add(p, Nat.mul(p, bq)), p, N.le_add_right(p, Nat.mul(p, bq)))
  +h1 = L.subst(Nat, z => {Nat.is_le(z, r) == True{} : Bool}, Nat.add(p, p), Nat.double(p), Equal.sym(Nat, Nat.double(p), Nat.add(p, p), NA.double_self(p)), h0)
  L.subst(Nat, z => {Nat.is_le(Nat.double(p), z) == True{} : Bool}, r, Nat.mul(p, 2n+bq), Equal.sym(Nat, Nat.mul(p, 2n+bq), r, em), h1)

# q < 2^K, 2^s <= p, t + s == K: the loop from p stops within t rounds
def ilb(+t: Nat, +f: Nat, +c: Bool, +q: Nat, +bq: Nat, +s: Nat, +p: Nat, +K: Nat, +hK: {Nat.add(t, s) == K : Nat}, +hq: {Nat.is_lt(q, C.pow2(K)) == True{} : Bool}, +hs: {Nat.is_le(C.pow2(s), p) == True{} : Bool}, +ht: {Nat.is_le(t, f) == True{} : Bool}, +hc: {c == Nat.is_le(p, q) : Bool}) -> {ilends(f, q, 2n+bq, p, c) == True{} : Bool}:
  match t f c:
    case 0n _ True{}:
      +hqs = L.subst(Nat, z => {Nat.is_lt(q, C.pow2(z)) == True{} : Bool}, K, s, Equal.sym(Nat, s, K, hK), hq)
      Empty.absurd({ilends(f, q, 2n+bq, p, True{}) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(p, q), False{}, hc, N.lt_not_le(q, p, N.lt_le_trans(q, C.pow2(s), p, hqs, hs)))))
    case 0n _ False{}:
      il_false(f, q, 2n+bq, p)
    case 1n+tp _ False{}:
      il_false(f, q, 2n+bq, p)
    case 1n+tp 0n True{}:
      Empty.absurd({ilends(0n, q, 2n+bq, p, True{}) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, ht)))
    case 1n+ +tp 1n+ +g True{}:
      +hK2 = Equal.trans(Nat, Nat.add(tp, 1n+s), 1n+Nat.add(tp, s), K, NA.add_succ(tp, s), hK)
      +hs2 = N.le_trans(Nat.double(C.pow2(s)), Nat.double(p), Nat.mul(p, 2n+bq), N.double_le(C.pow2(s), p, hs), dbl_le_mul(p, bq))
      ilb(tp, g, Nat.is_le(Nat.mul(p, 2n+bq), q), q, bq, 1n+s, Nat.mul(p, 2n+bq), K, hK2, hq, hs2, ht, {==})

def il_140(+K: Nat, +n: Nat, +bq: Nat, +hK: {Nat.is_le(K, 140n) == True{} : Bool}, +hq: {Nat.is_lt(Nat.div(n, 2n+bq), C.pow2(K)) == True{} : Bool}) -> {M.ilog_go(140n, n, 2n+bq, 0n, 1n, Nat.is_le(1n, Nat.div(n, 2n+bq))) == M.ilog_go(n, n, 2n+bq, 0n, 1n, Nat.is_le(1n, Nat.div(n, 2n+bq))) : Nat}:
  +q = Nat.div(n, 2n+bq)
  il_fuel(140n, n, n, 2n+bq, 0n, 1n, Nat.is_le(1n, q), ilb(K, 140n, Nat.is_le(1n, q), q, bq, 0n, 1n, K, N.add_zero(K), hq, {==}, hK, {==}), ilb(n, n, Nat.is_le(1n, q), q, bq, 0n, 1n, n, N.add_zero(n), N.le_lt_trans(q, n, C.pow2(n), AR2.div_le(n, 2n+bq), lt_pow2(n)), {==}, N.le_refl(n), {==}))

# ---- factorial: monotone, and (1+k)! >= 2^k ----

def fstep(+y: Nat) -> {Nat.is_le(S.factorial(y), S.factorial(1n+y)) == True{} : Bool}:
  +f = S.factorial(y)
  +e = Equal.trans(Nat, Nat.mul(1n+y, f), Nat.mul(f, 1n+y), Nat.add(f, Nat.mul(f, y)), NA.mul_comm(1n+y, f), NA.mul_succ(f, y))
  L.subst(Nat, z => {Nat.is_le(f, z) == True{} : Bool}, Nat.add(f, Nat.mul(f, y)), Nat.mul(1n+y, f), Equal.sym(Nat, Nat.mul(1n+y, f), Nat.add(f, Nat.mul(f, y)), e), N.le_add_right(f, Nat.mul(f, y)))

def mul_le_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, b), Nat.mul(a, c)) == True{} : Bool}:
  +h1 = AR2.mul_le(b, c, a, h)
  +h2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(c, a)) == True{} : Bool}, Nat.mul(b, a), Nat.mul(a, b), NA.mul_comm(b, a), h1)
  L.subst(Nat, z => {Nat.is_le(Nat.mul(a, b), z) == True{} : Bool}, Nat.mul(c, a), Nat.mul(a, c), NA.mul_comm(c, a), h2)

def fmono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(S.factorial(a), S.factorial(b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +y:
      N.le_trans(S.factorial(0n), S.factorial(y), S.factorial(1n+y), fmono(0n, y, N.zero_le(y)), fstep(y))
    case 1n+x 0n:
      Empty.absurd({Nat.is_le(S.factorial(1n+x), S.factorial(0n)) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+ +x 1n+ +y:
      N.le_trans(Nat.mul(1n+x, S.factorial(x)), Nat.mul(1n+y, S.factorial(x)), Nat.mul(1n+y, S.factorial(y)), AR2.mul_le(1n+x, 1n+y, S.factorial(x), h), mul_le_r(1n+y, S.factorial(x), S.factorial(y), fmono(x, y, h)))

def pf_le(+k: Nat) -> {Nat.is_le(C.pow2(k), S.factorial(1n+k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      +f = S.factorial(1n+j)
      +h1 = N.le_trans(Nat.double(C.pow2(j)), Nat.double(f), Nat.mul(f, 2n+j), N.double_le(C.pow2(j), f, pf_le(j)), dbl_le_mul(f, j))
      L.subst(Nat, z => {Nat.is_le(Nat.double(C.pow2(j)), z) == True{} : Bool}, Nat.mul(f, 2n+j), Nat.mul(2n+j, f), NA.mul_comm(f, 2n+j), h1)

# 1 + k <= i gives 2^k <= i!
def fbig(+k: Nat, +i: Nat, +h: {Nat.is_le(1n+k, i) == True{} : Bool}) -> {Nat.is_le(C.pow2(k), S.factorial(i)) == True{} : Bool}:
  N.le_trans(C.pow2(k), S.factorial(1n+k), S.factorial(i), pf_le(k), fmono(1n+k, i, h))

# ---- descending factorial (perm) ----

def sub_mono_l(+m: Nat, +n: Nat, +j: Nat, +h: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(m, j), Nat.sub(n, j)) == True{} : Bool}:
  match m n j:
    case 0n _ _:
      L.subst(Nat, z => {Nat.is_le(z, Nat.sub(n, j)) == True{} : Bool}, 0n, Nat.sub(0n, j), Equal.sym(Nat, Nat.sub(0n, j), 0n, NR.zsub(j)), N.zero_le(Nat.sub(n, j)))
    case 1n+x 0n _:
      Empty.absurd({Nat.is_le(Nat.sub(1n+x, j), Nat.sub(0n, j)) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+x 1n+y 0n:
      h
    case 1n+ +x 1n+ +y 1n+ +jp:
      sub_mono_l(x, y, jp, h)

def dmono1(+m: Nat, +n: Nat, +j: Nat, +h: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.is_le(S.desc(m, j), S.desc(n, j)) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +jp:
      N.le_trans(Nat.mul(Nat.sub(m, jp), S.desc(m, jp)), Nat.mul(Nat.sub(n, jp), S.desc(m, jp)), Nat.mul(Nat.sub(n, jp), S.desc(n, jp)), AR2.mul_le(Nat.sub(m, jp), Nat.sub(n, jp), S.desc(m, jp), sub_mono_l(m, n, jp, h)), mul_le_r(Nat.sub(n, jp), S.desc(m, jp), S.desc(n, jp), dmono1(m, n, jp, h)))

def dstep(+n: Nat, +s: Nat, +h: {Nat.is_lt(s, n) == True{} : Bool}) -> {Nat.is_le(S.desc(n, s), S.desc(n, 1n+s)) == True{} : Bool}:
  +pos = L.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, 1n+Nat.sub(n, 1n+s), Nat.sub(n, s), Equal.sym(Nat, Nat.sub(n, s), 1n+Nat.sub(n, 1n+s), FA.sub_lt_succ(n, s, h)), {==})
  L.subst(Nat, z => {Nat.is_le(S.desc(n, s), z) == True{} : Bool}, Nat.mul(S.desc(n, s), Nat.sub(n, s)), Nat.mul(Nat.sub(n, s), S.desc(n, s)), NA.mul_comm(S.desc(n, s), Nat.sub(n, s)), RT.le_mul_pos(S.desc(n, s), Nat.sub(n, s), pos))

def dmono(+n: Nat, +j: Nat, +d: Nat, +h: {Nat.is_le(Nat.add(j, d), n) == True{} : Bool}) -> {Nat.is_le(S.desc(n, j), S.desc(n, Nat.add(j, d))) == True{} : Bool}:
  match d:
    case 0n:
      L.subst(Nat, z => {Nat.is_le(S.desc(n, j), S.desc(n, z)) == True{} : Bool}, j, Nat.add(j, 0n), Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)), N.le_refl(S.desc(n, j)))
    case 1n+ +dp:
      +s = Nat.add(j, dp)
      +es = NA.add_succ(j, dp)
      +h1 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+dp), 1n+s, es, h)
      +hs = N.lt_le_trans(s, 1n+s, n, N.lt_succ(s), h1)
      +c = N.le_trans(S.desc(n, j), S.desc(n, s), S.desc(n, 1n+s), dmono(n, j, dp, N.lt_le(s, n, hs)), dstep(n, s, hs))
      L.subst(Nat, z => {Nat.is_le(S.desc(n, j), S.desc(n, z)) == True{} : Bool}, 1n+s, Nat.add(j, 1n+dp), Equal.sym(Nat, Nat.add(j, 1n+dp), 1n+s, es), c)

def desc_zero(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, k) == True{} : Bool}) -> {S.desc(n, k) == 0n : Nat}:
  Equal.trans(Nat, S.desc(n, k), Nat.mul(S.choose(n, k), S.factorial(k)), 0n, Equal.sym(Nat, Nat.mul(S.choose(n, k), S.factorial(k)), S.desc(n, k), FA.choose_mul_factorial(n, k)), Equal.trans(Nat, Nat.mul(S.choose(n, k), S.factorial(k)), Nat.mul(0n, S.factorial(k)), 0n, Equal.cong(Nat, Nat, t => Nat.mul(t, S.factorial(k)), S.choose(n, k), 0n, FA.choose_eq_zero(n, k, h)), Equal.trans(Nat, Nat.mul(0n, S.factorial(k)), Nat.mul(S.factorial(k), 0n), 0n, NA.mul_comm(0n, S.factorial(k)), NA.mul_zero(S.factorial(k)))))

# 1 + k <= j <= n gives 2^k <= n.desc(j)
def dbig(+k: Nat, +n: Nat, +j: Nat, +hj: {Nat.is_le(1n+k, j) == True{} : Bool}, +hjn: {Nat.is_le(j, n) == True{} : Bool}) -> {Nat.is_le(C.pow2(k), S.desc(n, j)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, S.desc(n, j)) == True{} : Bool}, S.desc(j, j), S.factorial(j), FA.desc_self(j), dmono1(j, n, j, hjn))
  N.le_trans(C.pow2(k), S.factorial(j), S.desc(n, j), fbig(k, j, hj), h1)

# ---- pow: one square-and-multiply round keeps acc * base^e ----

def msn(bit: Bool, +na: Nat, +nb: Nat) -> Nat:
  match bit:
    case True{}:
      Nat.mul(na, nb)
    case False{}:
      na

def sqn(more: Bool, +nb: Nat) -> Nat:
  match more:
    case True{}:
      Nat.mul(nb, nb)
    case False{}:
      nb

def pw_bit(+r: Nat, +na: Nat, +nb: Nat, +p2: Nat, +hr: {Nat.is_lt(r, 2n) == True{} : Bool}) -> {Nat.mul(msn(Nat.is_eq(r, 1n), na, nb), p2) == Nat.mul(na, Nat.mul(p2, Nat.pow(nb, r))) : Nat}:
  match r:
    case 0n:
      Equal.cong(Nat, Nat, t => Nat.mul(na, t), p2, Nat.mul(p2, 1n), Equal.sym(Nat, Nat.mul(p2, 1n), p2, NA.mul_one(p2)))
    case 1n:
      Equal.trans(Nat, Nat.mul(Nat.mul(na, nb), p2), Nat.mul(na, Nat.mul(nb, p2)), Nat.mul(na, Nat.mul(p2, Nat.mul(nb, 1n))), NA.mul_assoc(na, nb, p2), Equal.cong(Nat, Nat, t => Nat.mul(na, t), Nat.mul(nb, p2), Nat.mul(p2, Nat.mul(nb, 1n)), Equal.trans(Nat, Nat.mul(nb, p2), Nat.mul(p2, nb), Nat.mul(p2, Nat.mul(nb, 1n)), NA.mul_comm(nb, p2), Equal.cong(Nat, Nat, t => Nat.mul(p2, t), nb, Nat.mul(nb, 1n), Equal.sym(Nat, Nat.mul(nb, 1n), nb, NA.mul_one(nb))))))
    case 2n+q:
      Empty.absurd({Nat.mul(msn(Nat.is_eq(2n+q, 1n), na, nb), p2) == Nat.mul(na, Nat.mul(p2, Nat.pow(nb, 2n+q))) : Nat}, N.lt_zero_absurd(q, hr))

def powstep(+j: Nat, +na: Nat, +nb: Nat) -> {Nat.mul(msn(Nat.is_eq(Nat.mod(1n+j, 2n), 1n), na, nb), Nat.pow(sqn(Nat.is_lt(1n, 1n+j), nb), Nat.div(1n+j, 2n))) == Nat.mul(na, Nat.pow(nb, 1n+j)) : Nat}:
  match j:
    case 0n:
      Equal.trans(Nat, Nat.mul(Nat.mul(na, nb), 1n), Nat.mul(na, nb), Nat.mul(na, Nat.mul(nb, 1n)), NA.mul_one(Nat.mul(na, nb)), Equal.cong(Nat, Nat, t => Nat.mul(na, t), nb, Nat.mul(nb, 1n), Equal.sym(Nat, Nat.mul(nb, 1n), nb, NA.mul_one(nb))))
    case 1n+ +jp:
      +q = Nat.div(2n+jp, 2n)
      +r = Nat.mod(2n+jp, 2n)
      +p2 = Nat.pow(Nat.mul(nb, nb), q)
      +e1 = pw_bit(r, na, nb, p2, NR.dm_lt(1n, 2n+jp))
      +ed = Equal.trans(Nat, Nat.pow(nb, Nat.double(q)), p2, p2, MP.pow_double(nb, q), {==})
      +em = Equal.trans(Nat, Nat.mul(q, 2n), Nat.mul(2n, q), Nat.double(q), NA.mul_comm(q, 2n), Equal.sym(Nat, Nat.double(q), Nat.mul(2n, q), NA.double_mul(q)))
      +en = Equal.trans(Nat, 2n+jp, Nat.add(Nat.mul(q, 2n), r), Nat.add(Nat.double(q), r), NR.dm_eq(1n, 2n+jp), Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.mul(q, 2n), Nat.double(q), em))
      +ep = Equal.trans(Nat, Nat.pow(nb, 2n+jp), Nat.pow(nb, Nat.add(Nat.double(q), r)), Nat.mul(p2, Nat.pow(nb, r)), Equal.cong(Nat, Nat, t => Nat.pow(nb, t), 2n+jp, Nat.add(Nat.double(q), r), en), Equal.trans(Nat, Nat.pow(nb, Nat.add(Nat.double(q), r)), Nat.mul(Nat.pow(nb, Nat.double(q)), Nat.pow(nb, r)), Nat.mul(p2, Nat.pow(nb, r)), NR.pow_add(nb, Nat.double(q), r), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.pow(nb, r)), Nat.pow(nb, Nat.double(q)), p2, ed)))
      Equal.trans(Nat, Nat.mul(msn(Nat.is_eq(r, 1n), na, nb), p2), Nat.mul(na, Nat.mul(p2, Nat.pow(nb, r))), Nat.mul(na, Nat.pow(nb, 2n+jp)), e1, Equal.cong(Nat, Nat, t => Nat.mul(na, t), Nat.mul(p2, Nat.pow(nb, r)), Nat.pow(nb, 2n+jp), Equal.sym(Nat, Nat.pow(nb, 2n+jp), Nat.mul(p2, Nat.pow(nb, r)), ep)))

def half_le(+j: Nat) -> {Nat.is_le(Nat.div(1n+j, 2n), j) == True{} : Bool}:
  +h = N.le_lt_trans(j, Nat.double(j), 1n+Nat.double(j), N.double_self_le(j), N.lt_succ(Nat.double(j)))
  N.lt_succ_le(Nat.div(1n+j, 2n), j, half_below(1n+j, 1n+j, h))

def plus1(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, NA.add_succ(x, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(x, 0n), x, N.add_zero(x)))

# ---- iroot: powers are monotone, the bisection width halves ----

def pow_mono(+x: Nat, +y: Nat, +k: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.pow(x, k), Nat.pow(y, k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      N.le_trans(Nat.mul(x, Nat.pow(x, j)), Nat.mul(y, Nat.pow(x, j)), Nat.mul(y, Nat.pow(y, j)), AR2.mul_le(x, y, Nat.pow(x, j), h), mul_le_r(y, Nat.pow(x, j), Nat.pow(y, j), pow_mono(x, y, j, h)))

def lt_add_cancel(+d: Nat, +x: Nat, +y: Nat) -> {Nat.is_lt(Nat.add(d, x), Nat.add(d, y)) == Nat.is_lt(x, y) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      lt_add_cancel(e, x, y)

def dle_c(+q: Nat, +p: Nat, +h: {Nat.is_le(Nat.double(q), Nat.double(p)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(p, q) == c : Bool}) -> {Nat.is_le(q, p) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_le(q, p) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(Nat.double(p), Nat.double(q)), False{}, Equal.sym(Bool, Nat.is_lt(Nat.double(p), Nat.double(q)), True{}, N.double_lt(p, q, hc)), N.le_not_lt(Nat.double(p), Nat.double(q), h))))
    case False{}:
      N.not_lt_le(p, q, hc)

# 2 q <= 2 p gives q <= p
def dle(+q: Nat, +p: Nat, +h: {Nat.is_le(Nat.double(q), Nat.double(p)) == True{} : Bool}) -> {Nat.is_le(q, p) == True{} : Bool}:
  dle_c(q, p, h, Nat.is_lt(p, q), {==})

# w <= 2 p gives w / 2 <= p
def w_lo(+w: Nat, +p: Nat, +hw: {Nat.is_le(w, Nat.double(p)) == True{} : Bool}) -> {Nat.is_le(Nat.div(w, 2n), p) == True{} : Bool}:
  +q = Nat.div(w, 2n)
  +e = BT.half_eq(w)
  +h1 = L.subst(Nat, z => {Nat.is_le(Nat.double(q), z) == True{} : Bool}, Nat.add(Nat.double(q), Nat.mod(w, 2n)), w, Equal.sym(Nat, w, Nat.add(Nat.double(q), Nat.mod(w, 2n)), e), N.le_add_right(Nat.double(q), Nat.mod(w, 2n)))
  dle(q, p, N.le_trans(Nat.double(q), w, Nat.double(p), h1, hw))

def w_r(+q: Nat, +r: Nat, +p: Nat, +hr: {Nat.is_lt(r, 2n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(Nat.double(q), r), Nat.double(p)) == True{} : Bool}) -> {Nat.is_le(Nat.add(q, r), p) == True{} : Bool}:
  match r:
    case 0n:
      +h0 = L.subst(Nat, z => {Nat.is_le(z, Nat.double(p)) == True{} : Bool}, Nat.add(Nat.double(q), 0n), Nat.double(q), N.add_zero(Nat.double(q)), hw)
      L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, q, Nat.add(q, 0n), Equal.sym(Nat, Nat.add(q, 0n), q, N.add_zero(q)), dle(q, p, h0))
    case 1n:
      +h0 = L.subst(Nat, z => {Nat.is_le(z, Nat.double(p)) == True{} : Bool}, Nat.add(Nat.double(q), 1n), 1n+Nat.double(q), plus1(Nat.double(q)), hw)
      +hq = N.bit_double_lt(False{}, q, p, N.succ_le_lt(Nat.double(q), Nat.double(p), h0))
      L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, 1n+q, Nat.add(q, 1n), Equal.sym(Nat, Nat.add(q, 1n), 1n+q, plus1(q)), N.lt_succ_le_succ(q, p, hq))
    case 2n+s:
      Empty.absurd({Nat.is_le(Nat.add(q, 2n+s), p) == True{} : Bool}, N.lt_zero_absurd(s, hr))

# w <= 2 p gives w - w / 2 <= p
def w_hi(+w: Nat, +p: Nat, +hw: {Nat.is_le(w, Nat.double(p)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(w, Nat.div(w, 2n)), p) == True{} : Bool}:
  +q = Nat.div(w, 2n)
  +r = Nat.mod(w, 2n)
  +e = BT.half_eq(w)
  +e2 = Equal.trans(Nat, w, Nat.add(Nat.double(q), r), Nat.add(q, Nat.add(q, r)), e, Equal.trans(Nat, Nat.add(Nat.double(q), r), Nat.add(Nat.add(q, q), r), Nat.add(q, Nat.add(q, r)), Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.double(q), Nat.add(q, q), NA.double_self(q)), N.add_assoc(q, q, r)))
  +es = Equal.trans(Nat, Nat.sub(w, q), Nat.sub(Nat.add(q, Nat.add(q, r)), q), Nat.add(q, r), Equal.cong(Nat, Nat, t => Nat.sub(t, q), w, Nat.add(q, Nat.add(q, r)), e2), N.add_sub_cancel(q, Nat.add(q, r)))
  +hw2 = L.subst(Nat, z => {Nat.is_le(z, Nat.double(p)) == True{} : Bool}, w, Nat.add(Nat.double(q), r), e, hw)
  L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, Nat.add(q, r), Nat.sub(w, q), Equal.sym(Nat, Nat.sub(w, q), Nat.add(q, r), es), w_r(q, r, p, BT.half_rem(w), hw2))

# x^k <= n < (1 + r)^k gives x <= r
def root_below_c(+r: Nat, +x: Nat, +k: Nat, +n: Nat, +hx: {Nat.is_le(Nat.pow(x, k), n) == True{} : Bool}, +hr: {Nat.is_lt(n, Nat.pow(1n+r, k)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(r, x) == c : Bool}) -> {Nat.is_le(x, r) == True{} : Bool}:
  match c:
    case True{}:
      +h1 = N.le_trans(Nat.pow(1n+r, k), Nat.pow(x, k), n, pow_mono(1n+r, x, k, N.lt_succ_le_succ(r, x, hc)), hx)
      Empty.absurd({Nat.is_le(x, r) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(n, Nat.pow(1n+r, k)), False{}, Equal.sym(Bool, Nat.is_lt(n, Nat.pow(1n+r, k)), True{}, hr), N.le_not_lt(n, Nat.pow(1n+r, k), h1))))
    case False{}:
      N.not_lt_le(r, x, hc)

def root_below(+r: Nat, +x: Nat, +k: Nat, +n: Nat, +hx: {Nat.is_le(Nat.pow(x, k), n) == True{} : Bool}, +hr: {Nat.is_lt(n, Nat.pow(1n+r, k)) == True{} : Bool}) -> {Nat.is_le(x, r) == True{} : Bool}:
  root_below_c(r, x, k, n, hx, hr, Nat.is_lt(r, x), {==})

# x^k > n >= r^k gives r < x
def root_above_c(+r: Nat, +x: Nat, +k: Nat, +n: Nat, +hx: {Nat.is_le(Nat.pow(x, k), n) == False{} : Bool}, +hr: {Nat.is_le(Nat.pow(r, k), n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(x, r) == c : Bool}) -> {Nat.is_lt(r, x) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_lt(r, x) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.pow(x, k), n), False{}, Equal.sym(Bool, Nat.is_le(Nat.pow(x, k), n), True{}, N.le_trans(Nat.pow(x, k), Nat.pow(r, k), n, pow_mono(x, r, k, hc), hr)), hx)))
    case False{}:
      N.not_le_lt(x, r, hc)

def root_above(+r: Nat, +x: Nat, +k: Nat, +n: Nat, +hx: {Nat.is_le(Nat.pow(x, k), n) == False{} : Bool}, +hr: {Nat.is_le(Nat.pow(r, k), n) == True{} : Bool}) -> {Nat.is_lt(r, x) == True{} : Bool}:
  root_above_c(r, x, k, n, hx, hr, Nat.is_le(x, r), {==})

# n < 2^K gives bit_length(n) <= K
def bl_le_c(+K: Nat, +bl: Nat, +h: {Nat.is_lt(C.pow2(bl), C.pow2(1n+K)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(1n+K, bl) == c : Bool}) -> {Nat.is_le(bl, K) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_le(bl, K) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(C.pow2(bl), C.pow2(1n+K)), False{}, Equal.sym(Bool, Nat.is_lt(C.pow2(bl), C.pow2(1n+K)), True{}, h), N.le_not_lt(C.pow2(bl), C.pow2(1n+K), N.pow2_mono(1n+K, bl, hc)))))
    case False{}:
      N.lt_succ_le(bl, K, N.not_le_lt(1n+K, bl, hc))

def bl_le_n(+K: Nat, +n: Nat, +hn: {Nat.is_lt(n, C.pow2(K)) == True{} : Bool}) -> {Nat.is_le(M.bit_length(n), K) == True{} : Bool}:
  match n:
    case 0n:
      L.subst(Nat, z => {Nat.is_le(z, K) == True{} : Bool}, 0n, M.bit_length(0n), Equal.sym(Nat, M.bit_length(0n), 0n, BT.bit_length_zero()), N.zero_le(K))
    case 1n+ +np:
      +bl = M.bit_length(1n+np)
      +h = N.le_lt_trans(C.pow2(bl), Nat.double(1n+np), C.pow2(1n+K), BT.bit_length_le(np), N.double_lt(1n+np, C.pow2(K), hn))
      bl_le_c(K, bl, h, Nat.is_le(1n+K, bl), {==})

# bl <= 32 gives 1 + bl / (2 + kp) < 32
def e_lt(+kp: Nat, +bl: Nat, +hbl: {Nat.is_le(bl, 32n) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.div(bl, 2n+kp), 32n) == True{} : Bool}:
  +x = Nat.div(bl, 2n+kp)
  +hx = Equal.trans(Bool, Nat.is_le(Nat.mul(x, 2n+kp), bl), Nat.is_le(x, x), True{}, Equal.sym(Bool, Nat.is_le(x, x), Nat.is_le(Nat.mul(x, 2n+kp), bl), NR.le_div(1n+kp, x, bl)), N.le_refl(x))
  +d = N.le_trans(Nat.double(x), bl, 32n, N.le_trans(Nat.double(x), Nat.mul(x, 2n+kp), bl, dbl_le_mul(x, kp), hx), hbl)
  N.le_lt_trans(1n+x, 17n, 32n, dle(x, 16n, d), {==})

# bl <= 64 gives 1 + bl / (2 + kp) < 64
def e_lt64(+kp: Nat, +bl: Nat, +hbl: {Nat.is_le(bl, 64n) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.div(bl, 2n+kp), 64n) == True{} : Bool}:
  +x = Nat.div(bl, 2n+kp)
  +hx = Equal.trans(Bool, Nat.is_le(Nat.mul(x, 2n+kp), bl), Nat.is_le(x, x), True{}, Equal.sym(Bool, Nat.is_le(x, x), Nat.is_le(Nat.mul(x, 2n+kp), bl), NR.le_div(1n+kp, x, bl)), N.le_refl(x))
  +d = N.le_trans(Nat.double(x), bl, 64n, N.le_trans(Nat.double(x), Nat.mul(x, 2n+kp), bl, dbl_le_mul(x, kp), hx), hbl)
  N.le_lt_trans(1n+x, 33n, 64n, dle(x, 32n, d), {==})
