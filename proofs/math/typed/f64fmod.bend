import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/lemmas/proofs/natural_division.bend as ND
import ../natural/misc.bend as MS
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64dmrem.bend as DR
import ./w64dmtop.bend as DQ
import ./f64bits.bend as FB
import ./f64light.bend as FL
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64adda.bend as AA
import ./f64cmp.bend as FC
import ./f64bl.bend as BL
import ./f64tools.bend as T
import ./f64exp.bend as EX

# fmod and remainder (IEEE 754-2019 5.3.1 remainder; C99 7.12.10.1,
# 7.12.10.2, F.9.7.1, F.9.7.2; python_style_math_stdlib_design.pdf 4.3):
# Fmod.value, Remainder.value. Both are exact. The implementation divides
# mant(x) 2^(e(x) - e(y)) by mant(y) ten bits at a time (fm_go); the loop
# keeps r = N mod B and q = N div B (mod 2) for the dividend N consumed so
# far (Knuth, TAOCP vol. 2, 4.3.1, long division; the invariant is
# (N 2^t) mod B = ((N mod B) 2^t) mod B), so it ends with the spec's
# A mod B and the parity of A div B that rounding to nearest-even needs.

# ---- division on Nat ----

def mod_mul_add(+q: Nat, +bp: Nat, +y: Nat) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), y), 1n+bp) == Nat.mod(y, 1n+bp) : Nat}:
  +B = Nat.add(1n, bp)
  +Qy = Nat.div(y, B)
  +Ry = Nat.mod(y, B)
  +e1 = Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(q, B), t), y, Nat.add(Nat.mul(Qy, B), Ry), MS.divmod_eq(y, bp))
  +e2 = Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Ry), Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), NA.add_assoc(Nat.mul(q, B), Nat.mul(Qy, B), Ry))
  +e3 = Equal.cong(Nat, Nat, t => Nat.add(t, Ry), Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Nat.mul(Nat.add(q, Qy), B), Equal.sym(Nat, Nat.mul(Nat.add(q, Qy), B), Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), NA.mul_add_right(q, Qy, B)))
  +ee = Equal.trans(Nat, Nat.add(Nat.mul(q, B), y), Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), e1, Equal.trans(Nat, Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), Nat.add(Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Ry), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), e2, e3))
  +hR = N.lt_succ_le(Ry, bp, MS.divmod_lt(y, bp))
  Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(q, B), y), B), Nat.mod(Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), B), Ry, Equal.cong(Nat, Nat, t => Nat.mod(t, B), Nat.add(Nat.mul(q, B), y), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), ee), ND.remainder(Nat.add(q, Qy), bp, Ry, hR))

def div_mul_add(+q: Nat, +bp: Nat, +y: Nat) -> {Nat.div(Nat.add(Nat.mul(q, 1n+bp), y), 1n+bp) == Nat.add(q, Nat.div(y, 1n+bp)) : Nat}:
  +B = Nat.add(1n, bp)
  +Qy = Nat.div(y, B)
  +Ry = Nat.mod(y, B)
  +e1 = Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(q, B), t), y, Nat.add(Nat.mul(Qy, B), Ry), MS.divmod_eq(y, bp))
  +e2 = Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Ry), Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), NA.add_assoc(Nat.mul(q, B), Nat.mul(Qy, B), Ry))
  +e3 = Equal.cong(Nat, Nat, t => Nat.add(t, Ry), Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Nat.mul(Nat.add(q, Qy), B), Equal.sym(Nat, Nat.mul(Nat.add(q, Qy), B), Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), NA.mul_add_right(q, Qy, B)))
  +ee = Equal.trans(Nat, Nat.add(Nat.mul(q, B), y), Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), e1, Equal.trans(Nat, Nat.add(Nat.mul(q, B), Nat.add(Nat.mul(Qy, B), Ry)), Nat.add(Nat.add(Nat.mul(q, B), Nat.mul(Qy, B)), Ry), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), e2, e3))
  +hR = N.lt_succ_le(Ry, bp, MS.divmod_lt(y, bp))
  Equal.trans(Nat, Nat.div(Nat.add(Nat.mul(q, B), y), B), Nat.div(Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), B), Nat.add(q, Qy), Equal.cong(Nat, Nat, t => Nat.div(t, B), Nat.add(Nat.mul(q, B), y), Nat.add(Nat.mul(Nat.add(q, Qy), B), Ry), ee), ND.quotient(Nat.add(q, Qy), bp, Ry, hR))

# N 2^t = (Q 2^t) B + r 2^t for N = Q B + r
def shq(+N0: Nat, +bp: Nat, +t: Nat) -> {C.shift(t, N0) == Nat.add(Nat.mul(C.shift(t, Nat.div(N0, 1n+bp)), 1n+bp), C.shift(t, Nat.mod(N0, 1n+bp))) : Nat}:
  +B = Nat.add(1n, bp)
  +Q = Nat.div(N0, B)
  +r = Nat.mod(N0, B)
  +e1 = Equal.cong(Nat, Nat, u => C.shift(t, u), N0, Nat.add(Nat.mul(Q, B), r), MS.divmod_eq(N0, bp))
  +e2 = WW.shift_add(t, Nat.mul(Q, B), r)
  +e3 = Equal.cong(Nat, Nat, u => Nat.add(u, C.shift(t, r)), C.shift(t, Nat.mul(Q, B)), Nat.mul(C.shift(t, Q), B), Equal.sym(Nat, Nat.mul(C.shift(t, Q), B), C.shift(t, Nat.mul(Q, B)), WW.shift_mul_l(t, Q, B)))
  Equal.trans(Nat, C.shift(t, N0), C.shift(t, Nat.add(Nat.mul(Q, B), r)), Nat.add(Nat.mul(C.shift(t, Q), B), C.shift(t, r)), e1, Equal.trans(Nat, C.shift(t, Nat.add(Nat.mul(Q, B), r)), Nat.add(C.shift(t, Nat.mul(Q, B)), C.shift(t, r)), Nat.add(Nat.mul(C.shift(t, Q), B), C.shift(t, r)), e2, e3))

def mod_shift(+N0: Nat, +bp: Nat, +t: Nat) -> {Nat.mod(C.shift(t, Nat.mod(N0, 1n+bp)), 1n+bp) == Nat.mod(C.shift(t, N0), 1n+bp) : Nat}:
  +B = Nat.add(1n, bp)
  +e1 = Equal.cong(Nat, Nat, u => Nat.mod(u, B), C.shift(t, N0), Nat.add(Nat.mul(C.shift(t, Nat.div(N0, B)), B), C.shift(t, Nat.mod(N0, B))), shq(N0, bp, t))
  Equal.sym(Nat, Nat.mod(C.shift(t, N0), B), Nat.mod(C.shift(t, Nat.mod(N0, B)), B), Equal.trans(Nat, Nat.mod(C.shift(t, N0), B), Nat.mod(Nat.add(Nat.mul(C.shift(t, Nat.div(N0, B)), B), C.shift(t, Nat.mod(N0, B))), B), Nat.mod(C.shift(t, Nat.mod(N0, B)), B), e1, mod_mul_add(C.shift(t, Nat.div(N0, B)), bp, C.shift(t, Nat.mod(N0, B)))))

# the quotient's parity after at least one more bit
def par_shift(+N0: Nat, +bp: Nat, +p: Nat) -> {Nat.mod(Nat.div(C.shift(1n+p, Nat.mod(N0, 1n+bp)), 1n+bp), 2n) == Nat.mod(Nat.div(C.shift(1n+p, N0), 1n+bp), 2n) : Nat}:
  +B = Nat.add(1n, bp)
  +t = Nat.add(1n, p)
  +Q = Nat.div(N0, B)
  +D = Nat.div(C.shift(t, Nat.mod(N0, B)), B)
  +e1 = Equal.cong(Nat, Nat, u => Nat.div(u, B), C.shift(t, N0), Nat.add(Nat.mul(C.shift(t, Q), B), C.shift(t, Nat.mod(N0, B))), shq(N0, bp, t))
  +e2 = div_mul_add(C.shift(t, Q), bp, C.shift(t, Nat.mod(N0, B)))
  +e3 = NA.add_comm(C.shift(t, Q), D)
  +ed = Equal.trans(Nat, Nat.div(C.shift(t, N0), B), Nat.div(Nat.add(Nat.mul(C.shift(t, Q), B), C.shift(t, Nat.mod(N0, B))), B), Nat.add(D, C.shift(t, Q)), e1, Equal.trans(Nat, Nat.div(Nat.add(Nat.mul(C.shift(t, Q), B), C.shift(t, Nat.mod(N0, B))), B), Nat.add(C.shift(t, Q), D), Nat.add(D, C.shift(t, Q)), e2, e3))
  +e4 = Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), Nat.div(C.shift(t, N0), B), Nat.add(D, C.shift(t, Q)), ed)
  Equal.sym(Nat, Nat.mod(Nat.div(C.shift(t, N0), B), 2n), Nat.mod(D, 2n), Equal.trans(Nat, Nat.mod(Nat.div(C.shift(t, N0), B), 2n), Nat.mod(Nat.add(D, C.shift(t, Q)), 2n), Nat.mod(D, 2n), e4, WW.odd_limb(p, D, Q)))

def min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      N.zero_le(b)
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      min_le_r(ap, bp)

def min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      min_le_l(ap, bp)

# ---- one step of the loop ----

def rfit(+bp: Nat, +hB: {C.fits(53n, 1n+bp) == True{} : Bool}, +rw: WU.U64, +N0: Nat, +hr: {SW.value(rw) == Nat.mod(N0, 1n+bp) : Nat}) -> {C.fits(53n, SW.value(rw)) == True{} : Bool}:
  +f = SH.fits_lek(53n, Nat.mod(N0, 1n+bp), 1n+bp, N.lt_le(Nat.mod(N0, 1n+bp), 1n+bp, MS.divmod_lt(N0, bp)), hB)
  L.subst(Nat, u => {C.fits(53n, u) == True{} : Bool}, Nat.mod(N0, 1n+bp), SW.value(rw), Equal.sym(Nat, SW.value(rw), Nat.mod(N0, 1n+bp), hr), f)

def shl_t(+rw: WU.U64, +t: Nat, +ht: {Nat.is_le(t, 10n) == True{} : Bool}, +hf: {C.fits(53n, SW.value(rw)) == True{} : Bool}) -> {SW.value(X.shl(rw, t)) == C.shift(t, SW.value(rw)) : Nat}:
  +hk = N.le_lt_trans(t, 10n, 64n, ht, {==})
  +hj = N.le_trans(Nat.add(t, 53n), Nat.add(10n, 53n), 64n, Equal.trans(Bool, Nat.is_le(Nat.add(t, 53n), Nat.add(10n, 53n)), Nat.is_le(t, 10n), True{}, FR.le_cancel_r(t, 10n, 53n), ht), {==})
  FL.shl_v(rw, t, 53n, hk, hj, hf)

def step_r(+b: WU.U64, +bp: Nat, +eB: {SW.value(b) == 1n+bp : Nat}, +hB: {C.fits(53n, 1n+bp) == True{} : Bool}, +hbz: {X.is_zero(b) == False{} : Bool}, +rw: WU.U64, +N0: Nat, +t: Nat, +ht: {Nat.is_le(t, 10n) == True{} : Bool}, +hr: {SW.value(rw) == Nat.mod(N0, 1n+bp) : Nat}) -> {SW.value(X.psnd(X.divmod(X.shl(rw, t), b))) == Nat.mod(C.shift(t, N0), 1n+bp) : Nat}:
  +A = X.shl(rw, t)
  +eA = shl_t(rw, t, ht, rfit(bp, hB, rw, N0, hr))
  +e2 = Equal.cong(Nat, Nat, u => Nat.mod(u, SW.value(b)), SW.value(A), C.shift(t, SW.value(rw)), eA)
  +e3 = Equal.cong(Nat, Nat, u => Nat.mod(C.shift(t, u), SW.value(b)), SW.value(rw), Nat.mod(N0, 1n+bp), hr)
  +e4 = Equal.cong(Nat, Nat, u => Nat.mod(C.shift(t, Nat.mod(N0, 1n+bp)), u), SW.value(b), 1n+bp, eB)
  +m1 = Nat.mod(SW.value(A), SW.value(b))
  +m2 = Nat.mod(C.shift(t, SW.value(rw)), SW.value(b))
  +m3 = Nat.mod(C.shift(t, Nat.mod(N0, 1n+bp)), SW.value(b))
  +m4 = Nat.mod(C.shift(t, Nat.mod(N0, 1n+bp)), 1n+bp)
  +m5 = Nat.mod(C.shift(t, N0), 1n+bp)
  Equal.trans(Nat, SW.value(X.rem(A, b)), m1, m5, DR.divmod_rem(A, b, hbz), Equal.trans(Nat, m1, m2, m5, e2, Equal.trans(Nat, m2, m3, m5, e3, Equal.trans(Nat, m3, m4, m5, e4, mod_shift(N0, bp, t)))))

def step_q(+b: WU.U64, +bp: Nat, +eB: {SW.value(b) == 1n+bp : Nat}, +hB: {C.fits(53n, 1n+bp) == True{} : Bool}, +hbz: {X.is_zero(b) == False{} : Bool}, +rw: WU.U64, +N0: Nat, +p: Nat, +ht: {Nat.is_le(1n+p, 10n) == True{} : Bool}, +hr: {SW.value(rw) == Nat.mod(N0, 1n+bp) : Nat}) -> {Nat.mod(SW.value(X.pfst(X.divmod(X.shl(rw, 1n+p), b))), 2n) == Nat.mod(Nat.div(C.shift(1n+p, N0), 1n+bp), 2n) : Nat}:
  +A = X.shl(rw, 1n+p)
  +eA = shl_t(rw, 1n+p, ht, rfit(bp, hB, rw, N0, hr))
  +e2 = Equal.cong(Nat, Nat, u => Nat.div(u, SW.value(b)), SW.value(A), C.shift(1n+p, SW.value(rw)), eA)
  +e3 = Equal.cong(Nat, Nat, u => Nat.div(C.shift(1n+p, u), SW.value(b)), SW.value(rw), Nat.mod(N0, 1n+bp), hr)
  +e4 = Equal.cong(Nat, Nat, u => Nat.div(C.shift(1n+p, Nat.mod(N0, 1n+bp)), u), SW.value(b), 1n+bp, eB)
  +d1 = Nat.div(SW.value(A), SW.value(b))
  +d2 = Nat.div(C.shift(1n+p, SW.value(rw)), SW.value(b))
  +d3 = Nat.div(C.shift(1n+p, Nat.mod(N0, 1n+bp)), SW.value(b))
  +d4 = Nat.div(C.shift(1n+p, Nat.mod(N0, 1n+bp)), 1n+bp)
  +ed = Equal.trans(Nat, SW.value(X.quot(A, b)), d1, d4, DQ.divmod_quot(A, b, hbz), Equal.trans(Nat, d1, d2, d4, e2, Equal.trans(Nat, d2, d3, d4, e3, e4)))
  Equal.trans(Nat, Nat.mod(SW.value(X.quot(A, b)), 2n), Nat.mod(d4, 2n), Nat.mod(Nat.div(C.shift(1n+p, N0), 1n+bp), 2n), Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), SW.value(X.quot(A, b)), d4, ed), par_shift(N0, bp, p))

# ---- the loop ----

def shc(+e: Nat, +t: Nat, +N0: Nat, +h: {Nat.is_le(t, 1n+e) == True{} : Bool}) -> {C.shift(Nat.sub(1n+e, t), C.shift(t, N0)) == C.shift(1n+e, N0) : Nat}:
  +es = Equal.trans(Nat, Nat.add(Nat.sub(1n+e, t), t), Nat.add(t, Nat.sub(1n+e, t)), 1n+e, NA.add_comm(Nat.sub(1n+e, t), t), N.sub_add(1n+e, t, h))
  Equal.trans(Nat, C.shift(Nat.sub(1n+e, t), C.shift(t, N0)), C.shift(Nat.add(Nat.sub(1n+e, t), t), N0), C.shift(1n+e, N0), Equal.sym(Nat, C.shift(Nat.add(Nat.sub(1n+e, t), t), N0), C.shift(Nat.sub(1n+e, t), C.shift(t, N0)), WW.shift_comp(Nat.sub(1n+e, t), t, N0)), Equal.cong(Nat, Nat, u => C.shift(u, N0), Nat.add(Nat.sub(1n+e, t), t), 1n+e, es))

def eta(p: WU.U64 & WU.U64) -> {p == (X.pfst(p), X.psnd(p)) : WU.U64 & WU.U64}:
  match p:
    case (a, b):
      {==}

def loop_r(fuel: Nat, +b: WU.U64, +bp: Nat, +eB: {SW.value(b) == 1n+bp : Nat}, +hB: {C.fits(53n, 1n+bp) == True{} : Bool}, +hbz: {X.is_zero(b) == False{} : Bool}, +d: Nat, +hd: {Nat.is_le(d, fuel) == True{} : Bool}, +q: WU.U64, +r: WU.U64, +N0: Nat, +hr: {SW.value(r) == Nat.mod(N0, 1n+bp) : Nat}) -> {SW.value(X.psnd(F.fm_go(fuel, b, d, (q, r)))) == Nat.mod(C.shift(d, N0), 1n+bp) : Nat}:
  match fuel d:
    case 0n 0n:
      hr
    case 0n 1n+ +e:
      Empty.absurd({SW.value(X.psnd(F.fm_go(0n, b, 1n+e, (q, r)))) == Nat.mod(C.shift(1n+e, N0), 1n+bp) : Nat}, FL.true_ne_false(Equal.sym(Bool, False{}, True{}, hd)))
    case 1n+ +f 0n:
      hr
    case 1n+ +f 1n+ +e:
      +t = Nat.min(1n+e, 10n)
      +d2 = Nat.sub(1n+e, t)
      +hr2 = step_r(b, bp, eB, hB, hbz, r, N0, t, min_le_r(1n+e, 10n), hr)
      +hd2 = N.le_trans(Nat.sub(e, Nat.min(e, 9n)), e, f, EX.sub_le_self(e, Nat.min(e, 9n)), hd)
      +ee = Equal.cong(WU.U64 & WU.U64, Nat, u => SW.value(X.psnd(F.fm_go(f, b, d2, u))), X.divmod(X.shl(r, t), b), (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b))), eta(X.divmod(X.shl(r, t), b)))
      +rec = loop_r(f, b, bp, eB, hB, hbz, d2, hd2, X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)), C.shift(t, N0), hr2)
      +es = Equal.cong(Nat, Nat, u => Nat.mod(u, 1n+bp), C.shift(d2, C.shift(t, N0)), C.shift(1n+e, N0), shc(e, t, N0, min_le_l(1n+e, 10n)))
      Equal.trans(Nat, SW.value(X.psnd(F.fm_go(f, b, d2, X.divmod(X.shl(r, t), b)))), SW.value(X.psnd(F.fm_go(f, b, d2, (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)))))), Nat.mod(C.shift(1n+e, N0), 1n+bp), ee, Equal.trans(Nat, SW.value(X.psnd(F.fm_go(f, b, d2, (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)))))), Nat.mod(C.shift(d2, C.shift(t, N0)), 1n+bp), Nat.mod(C.shift(1n+e, N0), 1n+bp), rec, es))

def loop_q(fuel: Nat, +b: WU.U64, +bp: Nat, +eB: {SW.value(b) == 1n+bp : Nat}, +hB: {C.fits(53n, 1n+bp) == True{} : Bool}, +hbz: {X.is_zero(b) == False{} : Bool}, +d: Nat, +hd: {Nat.is_le(d, fuel) == True{} : Bool}, +q: WU.U64, +r: WU.U64, +N0: Nat, +hr: {SW.value(r) == Nat.mod(N0, 1n+bp) : Nat}, +hq: {Nat.mod(SW.value(q), 2n) == Nat.mod(Nat.div(N0, 1n+bp), 2n) : Nat}) -> {Nat.mod(SW.value(X.pfst(F.fm_go(fuel, b, d, (q, r)))), 2n) == Nat.mod(Nat.div(C.shift(d, N0), 1n+bp), 2n) : Nat}:
  match fuel d:
    case 0n 0n:
      hq
    case 0n 1n+ +e:
      Empty.absurd({Nat.mod(SW.value(X.pfst(F.fm_go(0n, b, 1n+e, (q, r)))), 2n) == Nat.mod(Nat.div(C.shift(1n+e, N0), 1n+bp), 2n) : Nat}, FL.true_ne_false(Equal.sym(Bool, False{}, True{}, hd)))
    case 1n+ +f 0n:
      hq
    case 1n+ +f 1n+ +e:
      +t = Nat.min(1n+e, 10n)
      +d2 = Nat.sub(1n+e, t)
      +hr2 = step_r(b, bp, eB, hB, hbz, r, N0, t, min_le_r(1n+e, 10n), hr)
      +hq2 = step_q(b, bp, eB, hB, hbz, r, N0, Nat.min(e, 9n), min_le_r(e, 9n), hr)
      +hd2 = N.le_trans(Nat.sub(e, Nat.min(e, 9n)), e, f, EX.sub_le_self(e, Nat.min(e, 9n)), hd)
      +ee = Equal.cong(WU.U64 & WU.U64, Nat, u => Nat.mod(SW.value(X.pfst(F.fm_go(f, b, d2, u))), 2n), X.divmod(X.shl(r, t), b), (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b))), eta(X.divmod(X.shl(r, t), b)))
      +rec = loop_q(f, b, bp, eB, hB, hbz, d2, hd2, X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)), C.shift(t, N0), hr2, hq2)
      +es = Equal.cong(Nat, Nat, u => Nat.mod(Nat.div(u, 1n+bp), 2n), C.shift(d2, C.shift(t, N0)), C.shift(1n+e, N0), shc(e, t, N0, min_le_l(1n+e, 10n)))
      Equal.trans(Nat, Nat.mod(SW.value(X.pfst(F.fm_go(f, b, d2, X.divmod(X.shl(r, t), b)))), 2n), Nat.mod(SW.value(X.pfst(F.fm_go(f, b, d2, (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)))))), 2n), Nat.mod(Nat.div(C.shift(1n+e, N0), 1n+bp), 2n), ee, Equal.trans(Nat, Nat.mod(SW.value(X.pfst(F.fm_go(f, b, d2, (X.pfst(X.divmod(X.shl(r, t), b)), X.psnd(X.divmod(X.shl(r, t), b)))))), 2n), Nat.mod(Nat.div(C.shift(d2, C.shift(t, N0)), 1n+bp), 2n), Nat.mod(Nat.div(C.shift(1n+e, N0), 1n+bp), 2n), rec, es))

# ---- a finite double is the round of its own significand and scale ----

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def dec(+x: F.F64) -> {x == SF.encode(SF.sign(x), SF.efield(x), SF.frac(x)) : F.F64}:
  match x:
    case F.Bits{+l, +h}:
      +H = v(h)
      +H20 = C.high(20n, H)
      +e1 = WW.low_high(20n, H)
      +e2 = Equal.cong(Nat, Nat, t => Nat.add(C.low(20n, H), C.shift(20n, t)), H20, Nat.add(C.low(11n, H20), C.shift(11n, C.high(11n, H20))), WW.low_high(11n, H20))
      +e3 = Equal.trans(Nat, C.high(11n, H20), C.high(31n, H), SF.b2n(SF.sign(F.Bits{l, h})), Equal.sym(Nat, C.high(Nat.add(20n, 11n), H), C.high(11n, H20), WW.high_comp(11n, 20n, H)), FB.bit_c(C.high(31n, H), FB.half0(h)))
      +e4 = Equal.cong(Nat, Nat, t => Nat.add(C.low(20n, H), C.shift(20n, Nat.add(C.low(11n, H20), C.shift(11n, t)))), C.high(11n, H20), SF.b2n(SF.sign(F.Bits{l, h})), e3)
      +a1 = Nat.add(C.low(20n, H), C.shift(20n, H20))
      +a2 = Nat.add(C.low(20n, H), C.shift(20n, Nat.add(C.low(11n, H20), C.shift(11n, C.high(11n, H20)))))
      +a3 = Nat.add(C.low(20n, H), C.shift(20n, Nat.add(C.low(11n, H20), C.shift(11n, SF.b2n(SF.sign(F.Bits{l, h}))))))
      FB.enc_g(l, h, SF.sign(F.Bits{l, h}), h, Equal.trans(Nat, H, a1, a3, e1, Equal.trans(Nat, a1, a2, a3, e2, e4)))

# a significand of at most 52 bits at its own ulp u encodes as a subnormal;
# u stays abstract, so pack's exponent arithmetic is never evaluated on a
# literal (rt_sub instantiates u = 1926)
def ru_self(+s: Bool, +Fr: Nat, +u: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}) -> {SF.round_u(s, Fr, u, u) == SF.encode(s, 0n, Fr) : F.F64}:
  +f53 = SH.fits_mono(52n, 53n, Fr, {==}, hF)
  +l1 = EX.ru(s, Fr, u, u)
  +l2 = Equal.cong(Bool, F.F64, b => SF.pack(s, SF.pick(Nat, b, SF.rne(Fr, Nat.sub(u, u)), C.shift(Nat.sub(u, u), Fr)), u), Nat.is_le(u, u), True{}, N.le_refl(u))
  +l3 = Equal.cong(Nat, F.F64, t => SF.pack(s, SF.rne(Fr, t), u), Nat.sub(u, u), 0n, N.sub_self(u))
  +l4 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.pack_n(s, Fr, u), SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)), C.fits(53n, Fr), True{}, f53)
  +l5 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.encode(s, 0n, Fr), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, Fr))), C.fits(52n, Fr), True{}, hF)
  +p1 = SF.pack(s, SF.pick(Nat, Nat.is_le(u, u), SF.rne(Fr, Nat.sub(u, u)), C.shift(Nat.sub(u, u), Fr)), u)
  +p2 = SF.pack(s, SF.rne(Fr, Nat.sub(u, u)), u)
  +p3 = SF.pack(s, Fr, u)
  +p4 = SF.pack_n(s, Fr, u)
  +G = SF.encode(s, 0n, Fr)
  Equal.trans(F.F64, SF.round_u(s, Fr, u, u), p1, G, l1, Equal.trans(F.F64, p1, p2, G, l2, Equal.trans(F.F64, p2, p3, G, l3, Equal.trans(F.F64, p3, p4, G, l4, l5))))

def rt_sub(+s: Bool, +Fr: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(Fr, 0n) == z : Bool}) -> {SF.round(s, Fr, 1926n) == SF.encode(s, 0n, Fr) : F.F64}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(Fr, 0n, hz)
      +ea = Equal.cong(Nat, F.F64, t => SF.round(s, t, 1926n), Fr, 0n, e0)
      +eb = Equal.trans(F.F64, SF.encode(s, 0n, 0n), FR.bits(s, 0n), SF.zero(s), FR.enc_bits(s, 0n, 0n), EX.bz(s))
      +ec = Equal.cong(Nat, F.F64, t => SF.encode(s, 0n, t), 0n, Fr, Equal.sym(Nat, Fr, 0n, N.eq_from_is_eq(Fr, 0n, hz)))
      Equal.trans(F.F64, SF.round(s, Fr, 1926n), SF.zero(s), SF.encode(s, 0n, Fr), ea, Equal.trans(F.F64, SF.zero(s), SF.encode(s, 0n, 0n), SF.encode(s, 0n, Fr), Equal.sym(F.F64, SF.encode(s, 0n, 0n), SF.zero(s), eb), ec))
    case False{}:
      +B = M.bit_length(Fr)
      +A = Nat.sub(Nat.add(1926n, B), 53n)
      +hB = BL.bl_le(52n, Fr, hF, Nat.is_le(B, 52n), {==})
      +emax = EX.max_le(A, 1926n, N.le_trans(B, 52n, 53n, hB, {==}))
      +e1 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.zero(s), SF.round_u(s, Fr, 1926n, Nat.max(A, Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(Fr, 0n), False{}, hz)
      +e2 = Equal.cong(Nat, F.F64, u => SF.round_u(s, Fr, 1926n, u), Nat.max(A, 1926n), 1926n, emax)
      +r1 = SF.round_u(s, Fr, 1926n, Nat.max(A, 1926n))
      +r2 = SF.round_u(s, Fr, 1926n, 1926n)
      Equal.trans(F.F64, SF.round(s, Fr, 1926n), r1, SF.encode(s, 0n, Fr), e1, Equal.trans(F.F64, r1, r2, SF.encode(s, 0n, Fr), e2, ru_self(s, Fr, 1926n, hF)))

def rt_norm(+s: Bool, +E: Nat, +Fr: Nat, +one: Nat, +h1: {one == 1n : Nat}, +hE0: {Nat.is_eq(E, 0n) == False{} : Bool}, +hE: {Nat.is_lt(E, 2047n) == True{} : Bool}, +hF: {C.fits(52n, Fr) == True{} : Bool}) -> {SF.round(s, Nat.add(Fr, C.shift(52n, one)), Nat.add(1925n, E)) == SF.encode(s, E, Fr) : F.F64}:
  +Mn = Nat.add(Fr, C.shift(52n, one))
  +X0 = Nat.add(1925n, E)
  +hz0 = Equal.trans(Bool, Nat.is_eq(Mn, 0n), Bool.and(Nat.is_eq(Fr, 0n), Nat.is_eq(one, 0n)), False{}, FB.z2(Fr, 52n, one), Equal.trans(Bool, Bool.and(Nat.is_eq(Fr, 0n), Nat.is_eq(one, 0n)), Bool.and(Nat.is_eq(Fr, 0n), False{}), False{}, Equal.cong(Nat, Bool, t => Bool.and(Nat.is_eq(Fr, 0n), Nat.is_eq(t, 0n)), one, 1n, h1), FR.and_f(Nat.is_eq(Fr, 0n))))
  +ebl = FR.bl_c(52n, Mn, AA.n52(one, h1, Fr), AA.f53(one, h1, Fr, hF), Nat.cmp(M.bit_length(Mn), 53n), {==})
  +emx = FR.max_l(X0, 1926n, FL.nz_le(E, hE0))
  +e1 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.zero(s), SF.round_u(s, Mn, X0, Nat.max(Nat.sub(Nat.add(X0, M.bit_length(Mn)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(Mn, 0n), False{}, hz0)
  +e2 = Equal.cong(Nat, F.F64, t => SF.round_u(s, Mn, X0, Nat.max(Nat.sub(Nat.add(X0, t), 53n), 1926n)), M.bit_length(Mn), 53n, ebl)
  +e3 = Equal.cong(Nat, F.F64, t => SF.round_u(s, Mn, X0, Nat.max(t, 1926n)), Nat.sub(Nat.add(X0, 53n), 53n), X0, FR.sub_add_l(X0, 53n))
  +e4 = Equal.cong(Nat, F.F64, t => SF.round_u(s, Mn, X0, t), Nat.max(X0, 1926n), X0, emx)
  +e5 = Equal.cong(Bool, F.F64, b => SF.pack(s, SF.pick(Nat, b, SF.rne(Mn, Nat.sub(X0, X0)), C.shift(Nat.sub(X0, X0), Mn)), X0), Nat.is_le(X0, X0), True{}, N.le_refl(X0))
  +e6 = Equal.cong(Nat, F.F64, t => SF.pack(s, SF.rne(Mn, t), X0), Nat.sub(X0, X0), 0n, N.sub_self(X0))
  +e7 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.pack_n(s, Mn, X0), SF.pack_e(s, Nat.sub(Nat.add(1n+X0, 1075n), SF.zb()), 0n)), C.fits(53n, Mn), True{}, AA.f53(one, h1, Fr, hF))
  +e8 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.encode(s, 0n, Mn), SF.pack_e(s, Nat.sub(Nat.add(X0, 1075n), SF.zb()), C.low(52n, Mn))), C.fits(52n, Mn), False{}, AA.n52(one, h1, Fr))
  +e9 = Equal.cong(Nat, F.F64, t => SF.pack_e(s, t, C.low(52n, Mn)), Nat.sub(Nat.add(X0, 1075n), SF.zb()), E, FR.sub_add_l(E, 1075n))
  +e10 = Equal.cong(Nat, F.F64, t => SF.pack_e(s, E, t), C.low(52n, Mn), Fr, WW.low_u(52n, Fr, one, hF))
  +e11 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.inf(s), SF.encode(s, E, Fr)), Nat.is_le(2047n, E), False{}, N.lt_not_le(E, 2047n, hE))
  +r1 = SF.round_u(s, Mn, X0, Nat.max(Nat.sub(Nat.add(X0, M.bit_length(Mn)), 53n), 1926n))
  +r2 = SF.round_u(s, Mn, X0, Nat.max(Nat.sub(Nat.add(X0, 53n), 53n), 1926n))
  +r3 = SF.round_u(s, Mn, X0, Nat.max(X0, 1926n))
  +r4 = SF.round_u(s, Mn, X0, X0)
  +r5 = SF.pack(s, SF.rne(Mn, Nat.sub(X0, X0)), X0)
  +r6 = SF.pack(s, Mn, X0)
  +r7 = SF.pack_n(s, Mn, X0)
  +r8 = SF.pack_e(s, Nat.sub(Nat.add(X0, 1075n), SF.zb()), C.low(52n, Mn))
  +r9 = SF.pack_e(s, E, C.low(52n, Mn))
  +r10 = SF.pack_e(s, E, Fr)
  +G = SF.encode(s, E, Fr)
  Equal.trans(F.F64, SF.round(s, Mn, X0), r1, G, e1, Equal.trans(F.F64, r1, r2, G, e2, Equal.trans(F.F64, r2, r3, G, e3, Equal.trans(F.F64, r3, r4, G, e4, Equal.trans(F.F64, r4, r5, G, e5, Equal.trans(F.F64, r5, r6, G, e6, Equal.trans(F.F64, r6, r7, G, e7, Equal.trans(F.F64, r7, r8, G, e8, Equal.trans(F.F64, r8, r9, G, e9, Equal.trans(F.F64, r9, r10, G, e10, e11))))))))))

def frac52(+x: F.F64) -> {C.fits(52n, SF.frac(x)) == True{} : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      FL.hF(xl, xh)

def rt_c(+x: F.F64, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +z: Bool, +hz: {Nat.is_eq(SF.efield(x), 0n) == z : Bool}) -> {SF.round(SF.sign(x), SF.mant(x), SF.xexp(x)) == x : F.F64}:
  match z:
    case True{}:
      +s = SF.sign(x)
      +E = SF.efield(x)
      +Fr = SF.frac(x)
      +e1 = Equal.cong(Bool, F.F64, b => SF.round(s, Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(b)))), SF.pick(Nat, b, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n))), Nat.is_eq(E, 0n), True{}, hz)
      +e2 = Equal.cong(Nat, F.F64, t => SF.round(s, t, 1926n), Nat.add(Fr, 0n), Fr, N.add_zero(Fr))
      +e3 = rt_sub(s, Fr, frac52(x), Nat.is_eq(Fr, 0n), {==})
      +e4 = Equal.cong(Nat, F.F64, t => SF.encode(s, t, Fr), 0n, E, Equal.sym(Nat, E, 0n, N.eq_from_is_eq(E, 0n, hz)))
      +e5 = Equal.sym(F.F64, x, SF.encode(s, E, Fr), dec(x))
      Equal.trans(F.F64, SF.round(s, SF.mant(x), SF.xexp(x)), SF.round(s, Nat.add(Fr, 0n), 1926n), x, e1, Equal.trans(F.F64, SF.round(s, Nat.add(Fr, 0n), 1926n), SF.round(s, Fr, 1926n), x, e2, Equal.trans(F.F64, SF.round(s, Fr, 1926n), SF.encode(s, 0n, Fr), x, e3, Equal.trans(F.F64, SF.encode(s, 0n, Fr), SF.encode(s, E, Fr), x, e4, e5))))
    case False{}:
      +s = SF.sign(x)
      +E = SF.efield(x)
      +Fr = SF.frac(x)
      +eb = Equal.trans(Nat, SF.b2n(Bool.not(Nat.is_eq(E, 0n))), 1n, one, Equal.cong(Bool, Nat, b => SF.b2n(Bool.not(b)), Nat.is_eq(E, 0n), False{}, hz), Equal.sym(Nat, one, 1n, h1))
      +e1 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.add(Fr, C.shift(52n, t)), SF.xexp(x)), SF.b2n(Bool.not(Nat.is_eq(E, 0n))), one, eb)
      +e2 = Equal.cong(Bool, F.F64, b => SF.round(s, Nat.add(Fr, C.shift(52n, one)), SF.pick(Nat, b, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n))), Nat.is_eq(E, 0n), False{}, hz)
      +e3 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.add(Fr, C.shift(52n, one)), t), Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), FC.esub(E))
      +e4 = rt_norm(s, E, Fr, one, h1, hz, hfin, frac52(x))
      +e5 = Equal.sym(F.F64, x, SF.encode(s, E, Fr), dec(x))
      +r1 = SF.round(s, Nat.add(Fr, C.shift(52n, one)), SF.xexp(x))
      +r2 = SF.round(s, Nat.add(Fr, C.shift(52n, one)), Nat.sub(Nat.add(E, SF.zb()), 1075n))
      +r3 = SF.round(s, Nat.add(Fr, C.shift(52n, one)), Nat.add(1925n, E))
      Equal.trans(F.F64, SF.round(s, SF.mant(x), SF.xexp(x)), r1, x, e1, Equal.trans(F.F64, r1, r2, x, e2, Equal.trans(F.F64, r2, r3, x, e3, Equal.trans(F.F64, r3, SF.encode(s, E, Fr), x, e4, e5))))

def rt(+x: F.F64, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}) -> {SF.round(SF.sign(x), SF.mant(x), SF.xexp(x)) == x : F.F64}:
  rt_c(x, hfin, 1n, {==}, Nat.is_eq(SF.efield(x), 0n), {==})

# ---- the pieces of fmod ----

def fin(+x: F.F64, +hn: {SF.is_nan(x) == False{} : Bool}, +hi: {SF.is_inf(x) == False{} : Bool}) -> {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      FC.lt2047(xl, xh, hi, hn)

def mod_small(+a: Nat, +n: Nat, +h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.mod(a, n) == a : Nat}:
  match n:
    case 0n:
      Empty.absurd({Nat.mod(a, 0n) == a : Nat}, N.lt_zero_absurd(a, h))
    case 1n+ +np:
      ND.remainder(0n, np, a, N.lt_succ_le(a, np, h))

def div_small(+a: Nat, +n: Nat, +h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.div(a, n) == 0n : Nat}:
  match n:
    case 0n:
      Empty.absurd({Nat.div(a, 0n) == 0n : Nat}, N.lt_zero_absurd(a, h))
    case 1n+ +np:
      ND.quotient(0n, np, a, N.lt_succ_le(a, np, h))

def xge_c(+x: F.F64, +c: Bool, +hc: {Nat.is_eq(SF.efield(x), 0n) == c : Bool}) -> {Nat.is_le(1926n, SF.pick(Nat, c, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(SF.efield(x), SF.zb()), 1075n))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      L.subst(Nat, t => {Nat.is_le(1926n, t) == True{} : Bool}, Nat.add(1925n, SF.efield(x)), Nat.sub(Nat.add(SF.efield(x), SF.zb()), 1075n), Equal.sym(Nat, Nat.sub(Nat.add(SF.efield(x), SF.zb()), 1075n), Nat.add(1925n, SF.efield(x)), FC.esub(SF.efield(x))), FL.nz_le(SF.efield(x), hc))

def xge(+x: F.F64) -> {Nat.is_le(1926n, SF.xexp(x)) == True{} : Bool}:
  xge_c(x, Nat.is_eq(SF.efield(x), 0n), {==})

# a scale above another double's is a normal number's
def yn_c(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(SF.efield(y), 0n) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +h1 = L.subst(Bool, b => {Nat.is_lt(SF.xexp(x), SF.pick(Nat, b, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(SF.efield(y), SF.zb()), 1075n))) == True{} : Bool}, Nat.is_eq(SF.efield(y), 0n), True{}, hc, hlt)
      +h2 = N.le_not_lt(SF.xexp(x), 1926n, xge(x))
      Empty.absurd({True{} == False{} : Bool}, FL.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(SF.xexp(x), 1926n), False{}, Equal.sym(Bool, Nat.is_lt(SF.xexp(x), 1926n), True{}, h1), h2)))
    case False{}:
      {==}

def nf52(+y: F.F64, +hz: {Nat.is_eq(SF.efield(y), 0n) == False{} : Bool}) -> {C.fits(52n, SF.mant(y)) == False{} : Bool}:
  AA.n52(SF.b2n(Bool.not(Nat.is_eq(SF.efield(y), 0n))), Equal.cong(Bool, Nat, b => SF.b2n(Bool.not(b)), Nat.is_eq(SF.efield(y), 0n), False{}, hz), SF.frac(y))

# y's significand moved up by k >= 1 is at least 2^53 > mant(x)
def far_lt(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(SF.mant(x), C.shift(Nat.sub(SF.xexp(y), SF.xexp(x)), SF.mant(y))) == True{} : Bool}:
  +k = Nat.sub(SF.xexp(y), SF.xexp(x))
  +S = C.shift(k, SF.mant(y))
  +hk = FR.lt_sub_pos(SF.xexp(x), SF.xexp(y), hlt)
  +hy = yn_c(x, y, hlt, Nat.is_eq(SF.efield(y), 0n), {==})
  +f1 = Equal.trans(Bool, C.fits(Nat.add(k, 52n), S), C.fits(52n, SF.mant(y)), False{}, RT.fits_sh(k, 52n, SF.mant(y)), nf52(y, hy))
  +h53 = Equal.trans(Bool, Nat.is_le(Nat.add(1n, 52n), Nat.add(k, 52n)), Nat.is_le(1n, k), True{}, FR.le_cancel_r(1n, k, 52n), hk)
  +f2 = FL.nfit_mono(53n, Nat.add(k, 52n), S, h53, f1)
  +l1 = Equal.trans(Bool, Nat.is_lt(SF.mant(x), C.shift(53n, one)), C.fits(53n, SF.mant(x)), True{}, FR.lt_fit(53n, one, h1, SF.mant(x)), T.mant_fits(x))
  +l2 = Equal.trans(Bool, Nat.is_le(C.shift(53n, one), S), Bool.not(C.fits(53n, S)), True{}, FB.le_fit(53n, one, h1, S), Equal.cong(Bool, Bool, b => Bool.not(b), C.fits(53n, S), False{}, f2))
  N.lt_le_trans(SF.mant(x), C.shift(53n, one), S, l1, l2)

def FM(+x: F.F64, +y: F.F64) -> F.F64:
  SF.round(SF.sign(x), Nat.mod(SF.ra(x, y), SF.rb(x, y)), SF.rsc(x, y))

# the spec's operands when x has the smaller scale
def fm_far(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}) -> {FM(x, y) == x : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +xy = SF.xexp(y)
  +mx = SF.mant(x)
  +my = SF.mant(y)
  +S = C.shift(Nat.sub(xy, xx), my)
  +e1 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), t), Nat.min(xx, xy), xx, N.min_left(xx, xy, hlt))
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(C.shift(t, mx), S), xx), Nat.sub(xx, xx), 0n, N.sub_self(xx))
  +e3 = Equal.cong(Nat, F.F64, t => SF.round(s, t, xx), Nat.mod(mx, S), mx, mod_small(mx, S, far_lt(x, y, hlt, 1n, {==})))
  +r1 = SF.round(s, Nat.mod(C.shift(Nat.sub(xx, xx), mx), S), xx)
  +r2 = SF.round(s, Nat.mod(mx, S), xx)
  Equal.trans(F.F64, FM(x, y), r1, x, e1, Equal.trans(F.F64, r1, r2, x, e2, Equal.trans(F.F64, r2, SF.round(s, mx, xx), x, e3, rt(x, hfin))))

# a zero x
def fm_zero(+x: F.F64, +y: F.F64, +hzx: {SF.is_zero(x) == True{} : Bool}, +hzy: {SF.is_zero(y) == False{} : Bool}, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}) -> {FM(x, y) == x : F.F64}:
  +s = SF.sign(x)
  +em = N.eq_from_is_eq(SF.mant(x), 0n, Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), SF.is_zero(x), True{}, T.mant_z(x), hzx))
  +a = Nat.sub(SF.xexp(x), SF.rsc(x, y))
  +rb = SF.rb(x, y)
  +hmy = FL.nz_le(SF.mant(y), Equal.trans(Bool, Nat.is_eq(SF.mant(y), 0n), SF.is_zero(y), False{}, T.mant_z(y), hzy))
  +hrb = N.succ_le_lt(0n, rb, N.le_trans(1n, SF.mant(y), rb, hmy, WW.shift_ge(Nat.sub(SF.xexp(y), SF.rsc(x, y)), SF.mant(y))))
  +e1 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(C.shift(a, t), rb), SF.rsc(x, y)), SF.mant(x), 0n, em)
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(t, rb), SF.rsc(x, y)), C.shift(a, 0n), 0n, WW.shift_zero(a))
  +e3 = Equal.cong(Nat, F.F64, t => SF.round(s, t, SF.rsc(x, y)), Nat.mod(0n, rb), 0n, mod_small(0n, rb, hrb))
  +e4 = Equal.cong(Nat, F.F64, t => SF.round(s, t, SF.xexp(x)), 0n, SF.mant(x), Equal.sym(Nat, SF.mant(x), 0n, N.eq_from_is_eq(SF.mant(x), 0n, Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), SF.is_zero(x), True{}, T.mant_z(x), hzx))))
  +r1 = SF.round(s, Nat.mod(C.shift(a, 0n), rb), SF.rsc(x, y))
  +r2 = SF.round(s, Nat.mod(0n, rb), SF.rsc(x, y))
  +r3 = SF.round(s, 0n, SF.rsc(x, y))
  +r4 = SF.round(s, 0n, SF.xexp(x))
  Equal.trans(F.F64, FM(x, y), r1, x, e1, Equal.trans(F.F64, r1, r2, x, e2, Equal.trans(F.F64, r2, r3, x, e3, Equal.trans(F.F64, r3, r4, x, {==}, Equal.trans(F.F64, r4, SF.round(s, SF.mant(x), SF.xexp(x)), x, e4, rt(x, hfin))))))

# ---- the loop's result for a nonzero y ----

def bpv(+y: F.F64) -> Nat:
  Nat.sub(SW.value(F.dmant(y)), 1n)

def ynz(+y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {Nat.is_eq(SW.value(F.dmant(y)), 0n) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(SW.value(F.dmant(y)), 0n), SF.is_zero(y), False{}, T.dmz(y), hzy)

def eBy(+y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {SW.value(F.dmant(y)) == 1n+bpv(y) : Nat}:
  Equal.sym(Nat, Nat.add(1n, bpv(y)), SW.value(F.dmant(y)), N.sub_add(SW.value(F.dmant(y)), 1n, FL.nz_le(SW.value(F.dmant(y)), ynz(y, hzy))))

def hbzy(+y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {X.is_zero(F.dmant(y)) == False{} : Bool}:
  Equal.trans(Bool, X.is_zero(F.dmant(y)), Nat.is_eq(SW.value(F.dmant(y)), 0n), False{}, WA.is_zero_value(F.dmant(y)), ynz(y, hzy))

def hBy(+y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {C.fits(53n, 1n+bpv(y)) == True{} : Bool}:
  L.subst(Nat, t => {C.fits(53n, t) == True{} : Bool}, SW.value(F.dmant(y)), 1n+bpv(y), eBy(y, hzy), T.mw53(y))

def DD(+x: F.F64, +y: F.F64) -> Nat:
  Nat.sub(F.dexp(x), F.dexp(y))

def qr_r(+x: F.F64, +y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {SW.value(X.psnd(F.fm_qr(x, y))) == Nat.mod(C.shift(DD(x, y), SW.value(F.dmant(x))), SW.value(F.dmant(y))) : Nat}:
  +xw = F.dmant(x)
  +yw = F.dmant(y)
  +D = DD(x, y)
  +bp = bpv(y)
  +V = SW.value(yw)
  +e0 = Equal.cong(WU.U64 & WU.U64, Nat, u => SW.value(X.psnd(F.fm_go(D, yw, D, u))), X.divmod(xw, yw), (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw))), eta(X.divmod(xw, yw)))
  +hr0 = Equal.trans(Nat, SW.value(X.rem(xw, yw)), Nat.mod(SW.value(xw), V), Nat.mod(SW.value(xw), 1n+bp), DR.divmod_rem(xw, yw, hbzy(y, hzy)), Equal.cong(Nat, Nat, t => Nat.mod(SW.value(xw), t), V, 1n+bp, eBy(y, hzy)))
  +e1 = loop_r(D, yw, bp, eBy(y, hzy), hBy(y, hzy), hbzy(y, hzy), D, N.le_refl(D), X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)), SW.value(xw), hr0)
  +e2 = Equal.cong(Nat, Nat, t => Nat.mod(C.shift(D, SW.value(xw)), t), 1n+bp, V, Equal.sym(Nat, V, 1n+bp, eBy(y, hzy)))
  Equal.trans(Nat, SW.value(X.psnd(F.fm_go(D, yw, D, X.divmod(xw, yw)))), SW.value(X.psnd(F.fm_go(D, yw, D, (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)))))), Nat.mod(C.shift(D, SW.value(xw)), V), e0, Equal.trans(Nat, SW.value(X.psnd(F.fm_go(D, yw, D, (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)))))), Nat.mod(C.shift(D, SW.value(xw)), 1n+bp), Nat.mod(C.shift(D, SW.value(xw)), V), e1, e2))

def qr_q(+x: F.F64, +y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {Nat.mod(SW.value(X.pfst(F.fm_qr(x, y))), 2n) == Nat.mod(Nat.div(C.shift(DD(x, y), SW.value(F.dmant(x))), SW.value(F.dmant(y))), 2n) : Nat}:
  +xw = F.dmant(x)
  +yw = F.dmant(y)
  +D = DD(x, y)
  +bp = bpv(y)
  +V = SW.value(yw)
  +e0 = Equal.cong(WU.U64 & WU.U64, Nat, u => Nat.mod(SW.value(X.pfst(F.fm_go(D, yw, D, u))), 2n), X.divmod(xw, yw), (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw))), eta(X.divmod(xw, yw)))
  +hr0 = Equal.trans(Nat, SW.value(X.rem(xw, yw)), Nat.mod(SW.value(xw), V), Nat.mod(SW.value(xw), 1n+bp), DR.divmod_rem(xw, yw, hbzy(y, hzy)), Equal.cong(Nat, Nat, t => Nat.mod(SW.value(xw), t), V, 1n+bp, eBy(y, hzy)))
  +hq0 = Equal.cong(Nat, Nat, t => Nat.mod(t, 2n), SW.value(X.quot(xw, yw)), Nat.div(SW.value(xw), 1n+bp), Equal.trans(Nat, SW.value(X.quot(xw, yw)), Nat.div(SW.value(xw), V), Nat.div(SW.value(xw), 1n+bp), DQ.divmod_quot(xw, yw, hbzy(y, hzy)), Equal.cong(Nat, Nat, t => Nat.div(SW.value(xw), t), V, 1n+bp, eBy(y, hzy))))
  +e1 = loop_q(D, yw, bp, eBy(y, hzy), hBy(y, hzy), hbzy(y, hzy), D, N.le_refl(D), X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)), SW.value(xw), hr0, hq0)
  +e2 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.div(C.shift(D, SW.value(xw)), t), 2n), 1n+bp, V, Equal.sym(Nat, V, 1n+bp, eBy(y, hzy)))
  Equal.trans(Nat, Nat.mod(SW.value(X.pfst(F.fm_go(D, yw, D, X.divmod(xw, yw)))), 2n), Nat.mod(SW.value(X.pfst(F.fm_go(D, yw, D, (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)))))), 2n), Nat.mod(Nat.div(C.shift(D, SW.value(xw)), V), 2n), e0, Equal.trans(Nat, Nat.mod(SW.value(X.pfst(F.fm_go(D, yw, D, (X.pfst(X.divmod(xw, yw)), X.psnd(X.divmod(xw, yw)))))), 2n), Nat.mod(Nat.div(C.shift(D, SW.value(xw)), 1n+bp), 2n), Nat.mod(Nat.div(C.shift(D, SW.value(xw)), V), 2n), e1, e2))

# ---- fmod ----

def NRd(+s: Bool, +a: Nat, +b: Nat, +m1: Nat, +m2: Nat) -> F.F64:
  SF.round(s, Nat.mod(C.shift(Nat.sub(a, b), m1), m2), b)

# FM when y has the smaller (or equal) scale
def fm_spec_near(+x: F.F64, +y: F.F64, +hge: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == False{} : Bool}) -> {FM(x, y) == NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y)) : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +xy = SF.xexp(y)
  +mx = SF.mant(x)
  +my = SF.mant(y)
  +e1 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), t), Nat.min(xx, xy), xy, N.min_right(xx, xy, hge))
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(s, Nat.mod(C.shift(Nat.sub(xx, xy), mx), C.shift(t, my)), xy), Nat.sub(xy, xy), 0n, N.sub_self(xy))
  Equal.trans(F.F64, FM(x, y), SF.round(s, Nat.mod(C.shift(Nat.sub(xx, xy), mx), C.shift(Nat.sub(xy, xy), my)), xy), NRd(s, xx, xy, mx, my), e1, e2)

def nrd_v(+x: F.F64, +y: F.F64) -> {NRd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))) == NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y)) : F.F64}:
  +e1 = Equal.cong(Bool, F.F64, t => NRd(t, F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e2 = Equal.cong(Nat, F.F64, t => NRd(SF.sign(x), t, F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +e3 = Equal.cong(Nat, F.F64, t => NRd(SF.sign(x), SF.xexp(x), t, SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.dexp(y), SF.xexp(y), T.dexp_value(y))
  +e4 = Equal.cong(Nat, F.F64, t => NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), t, SW.value(F.dmant(y))), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
  +e5 = Equal.cong(Nat, F.F64, t => NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), t), SW.value(F.dmant(y)), SF.mant(y), T.dmant_value(y))
  +r1 = NRd(SF.sign(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r2 = NRd(SF.sign(x), SF.xexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r3 = NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r4 = NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SW.value(F.dmant(y)))
  +G = NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y))
  Equal.trans(F.F64, NRd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), r1, G, e1, Equal.trans(F.F64, r1, r2, G, e2, Equal.trans(F.F64, r2, r3, G, e3, Equal.trans(F.F64, r3, r4, G, e4, e5))))

def xlt(+x: F.F64, +y: F.F64, +b: Bool, +h: {Nat.is_lt(F.dexp(x), F.dexp(y)) == b : Bool}) -> {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == b : Bool}:
  +h1 = L.subst(Nat, t => {Nat.is_lt(t, F.dexp(y)) == b : Bool}, F.dexp(x), SF.xexp(x), T.dexp_value(x), h)
  L.subst(Nat, t => {Nat.is_lt(SF.xexp(x), t) == b : Bool}, F.dexp(y), SF.xexp(y), T.dexp_value(y), h1)

def fm_near(+x: F.F64, +y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}, +hge: {Nat.is_lt(F.dexp(x), F.dexp(y)) == False{} : Bool}) -> {F.round_w(F.signbit(x), F.dexp(y), X.psnd(F.fm_qr(x, y))) == FM(x, y) : F.F64}:
  +r = X.psnd(F.fm_qr(x, y))
  +e1 = T.rw_value(F.signbit(x), F.dexp(y), r, T.dexp_ge(y))
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(F.signbit(x), t, F.dexp(y)), SW.value(r), Nat.mod(C.shift(DD(x, y), SW.value(F.dmant(x))), SW.value(F.dmant(y))), qr_r(x, y, hzy))
  +G = NRd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y))
  +e3 = nrd_v(x, y)
  +e4 = Equal.sym(F.F64, FM(x, y), G, fm_spec_near(x, y, xlt(x, y, False{}, hge)))
  +r1 = SF.round(F.signbit(x), SW.value(r), F.dexp(y))
  +r2 = NRd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  Equal.trans(F.F64, F.round_w(F.signbit(x), F.dexp(y), r), r1, FM(x, y), e1, Equal.trans(F.F64, r1, r2, FM(x, y), e2, Equal.trans(F.F64, r2, G, FM(x, y), e3, e4)))

def nn(+b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def badv(+x: F.F64, +y: F.F64) -> {Bool.or(Bool.or(F.unordered(x, y), F.is_inf(x)), F.is_zero(y)) == SF.rbad(x, y) : Bool}:
  +e1 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(Bool.or(t, F.is_nan(y)), F.is_inf(x)), F.is_zero(y)), F.is_nan(x), SF.is_nan(x), FB.is_nan_value(x))
  +e2 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(Bool.or(SF.is_nan(x), t), F.is_inf(x)), F.is_zero(y)), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y))
  +U = Bool.or(SF.is_nan(x), SF.is_nan(y))
  +e3 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(t, F.is_inf(x)), F.is_zero(y)), U, Bool.not(Bool.not(U)), Equal.sym(Bool, Bool.not(Bool.not(U)), U, nn(U)))
  +e4 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(Bool.not(Bool.not(U)), t), F.is_zero(y)), F.is_inf(x), SF.is_inf(x), FB.is_inf_value(x))
  +e5 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(Bool.not(Bool.not(U)), SF.is_inf(x)), t), F.is_zero(y), SF.is_zero(y), FB.is_zero_value(y))
  +b1 = Bool.or(Bool.or(Bool.or(SF.is_nan(x), F.is_nan(y)), F.is_inf(x)), F.is_zero(y))
  +b2 = Bool.or(Bool.or(U, F.is_inf(x)), F.is_zero(y))
  +b3 = Bool.or(Bool.or(Bool.not(Bool.not(U)), F.is_inf(x)), F.is_zero(y))
  +b4 = Bool.or(Bool.or(Bool.not(Bool.not(U)), SF.is_inf(x)), F.is_zero(y))
  Equal.trans(Bool, Bool.or(Bool.or(F.unordered(x, y), F.is_inf(x)), F.is_zero(y)), b1, SF.rbad(x, y), e1, Equal.trans(Bool, b1, b2, SF.rbad(x, y), e2, Equal.trans(Bool, b2, b3, SF.rbad(x, y), e3, Equal.trans(Bool, b3, b4, SF.rbad(x, y), e4, e5))))

# what a false rbad says
def ok_zy(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}) -> {SF.is_zero(y) == False{} : Bool}:
  FC.or_r(Bool.or(Bool.not(SF.ordered(x, y)), SF.is_inf(x)), SF.is_zero(y), h)

def ok_ix(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}) -> {SF.is_inf(x) == False{} : Bool}:
  FC.or_r(Bool.not(SF.ordered(x, y)), SF.is_inf(x), FC.or_l(Bool.or(Bool.not(SF.ordered(x, y)), SF.is_inf(x)), SF.is_zero(y), h))

def ok_u(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}) -> {Bool.or(SF.is_nan(x), SF.is_nan(y)) == False{} : Bool}:
  +h1 = FC.or_l(Bool.not(SF.ordered(x, y)), SF.is_inf(x), FC.or_l(Bool.or(Bool.not(SF.ordered(x, y)), SF.is_inf(x)), SF.is_zero(y), h))
  FR.not_t(Bool.or(SF.is_nan(x), SF.is_nan(y)), FR.not_f(SF.ordered(x, y), h1))

def ok_fin(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}) -> {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}:
  fin(x, FC.or_l(SF.is_nan(x), SF.is_nan(y), ok_u(x, y, h)), ok_ix(x, y, h))

def ff_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +far: Bool, +hfar: {Nat.is_lt(F.dexp(x), F.dexp(y)) == far : Bool}) -> {F.fmod_fin(x, y, far) == FM(x, y) : F.F64}:
  match far:
    case True{}:
      Equal.sym(F.F64, FM(x, y), x, fm_far(x, y, xlt(x, y, True{}, hfar), ok_fin(x, y, h)))
    case False{}:
      fm_near(x, y, ok_zy(x, y, h), hfar)

def fz_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +zx: Bool, +hzx: {SF.is_zero(x) == zx : Bool}) -> {F.fmod_z(x, y, zx) == FM(x, y) : F.F64}:
  match zx:
    case True{}:
      Equal.sym(F.F64, FM(x, y), x, fm_zero(x, y, hzx, ok_zy(x, y, h), ok_fin(x, y, h)))
    case False{}:
      ff_c(x, y, h, Nat.is_lt(F.dexp(x), F.dexp(y)), {==})

def fyi_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +yi: Bool) -> {F.fmod_yi(x, y, yi) == SF.pick(F.F64, yi, x, FM(x, y)) : F.F64}:
  match yi:
    case True{}:
      {==}
    case False{}:
      Equal.trans(F.F64, F.fmod_z(x, y, F.is_zero(x)), F.fmod_z(x, y, SF.is_zero(x)), FM(x, y), Equal.cong(Bool, F.F64, t => F.fmod_z(x, y, t), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x)), fz_c(x, y, h, SF.is_zero(x), {==}))

def fb_c(+x: F.F64, +y: F.F64, +bad: Bool, +h: {SF.rbad(x, y) == bad : Bool}) -> {F.fmod_bad(x, y, bad) == SF.pick(F.F64, bad, SF.qnan(), SF.pick(F.F64, SF.is_inf(y), x, FM(x, y))) : F.F64}:
  match bad:
    case True{}:
      {==}
    case False{}:
      Equal.trans(F.F64, F.fmod_yi(x, y, F.is_inf(y)), F.fmod_yi(x, y, SF.is_inf(y)), SF.pick(F.F64, SF.is_inf(y), x, FM(x, y)), Equal.cong(Bool, F.F64, t => F.fmod_yi(x, y, t), F.is_inf(y), SF.is_inf(y), FB.is_inf_value(y)), fyi_c(x, y, h, SF.is_inf(y)))

def fmod_value(+x: F.F64, +y: F.F64) -> SF.Fmod.value(x, y):
  +e1 = Equal.cong(Bool, F.F64, t => F.fmod_bad(x, y, t), Bool.or(Bool.or(F.unordered(x, y), F.is_inf(x)), F.is_zero(y)), SF.rbad(x, y), badv(x, y))
  Equal.trans(F.F64, F.fmod(x, y), F.fmod_bad(x, y, SF.rbad(x, y)), SF.fmod(x, y), e1, fb_c(x, y, SF.rbad(x, y), {==}))

# ---- remainder ----

def addrr(+r: WU.U64, +Rv: Nat, +er: {SW.value(r) == Rv : Nat}, +hf: {C.fits(53n, Rv) == True{} : Bool}) -> {SW.value(X.add(r, r)) == Nat.add(Rv, Rv) : Nat}:
  +f64 = SH.fits_mono(54n, 64n, Nat.add(Rv, Rv), {==}, FR.fits_add1(53n, Rv, Rv, hf, hf))
  e1 = WA.add_value(r, r)
  +e2 = Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(t, t)), SW.value(r), Rv, er)
  Equal.trans(Nat, SW.value(X.add(r, r)), C.low(64n, Nat.add(SW.value(r), SW.value(r))), Nat.add(Rv, Rv), e1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(r), SW.value(r))), C.low(64n, Nat.add(Rv, Rv)), Nat.add(Rv, Rv), e2, WW.low_fit(64n, Nat.add(Rv, Rv), f64)))

def rmp_c(+s: Bool, +u: Nat, +hu: {Nat.is_le(63n, u) == True{} : Bool}, +b: WU.U64, +r: WU.U64, +Bv: Nat, +Rv: Nat, +eb: {SW.value(b) == Bv : Nat}, +er: {SW.value(r) == Rv : Nat}, +hRB: {Nat.is_le(Rv, Bv) == True{} : Bool}, +c: Bool) -> {F.rm_pick(s, u, b, r, c) == SF.pick(F.F64, c, SF.round(Bool.not(s), Nat.sub(Bv, Rv), u), SF.round(s, Rv, u)) : F.F64}:
  match c:
    case True{}:
      +hle = L.subst(Nat, t => {Nat.is_le(t, SW.value(b)) == True{} : Bool}, Rv, SW.value(r), Equal.sym(Nat, SW.value(r), Rv, er), L.subst(Nat, t => {Nat.is_le(Rv, t) == True{} : Bool}, Bv, SW.value(b), Equal.sym(Nat, SW.value(b), Bv, eb), hRB))
      +es = Equal.trans(Nat, SW.value(X.sub(b, r)), Nat.sub(SW.value(b), SW.value(r)), Nat.sub(Bv, Rv), WA.sub_value(b, r, hle), Equal.trans(Nat, Nat.sub(SW.value(b), SW.value(r)), Nat.sub(Bv, SW.value(r)), Nat.sub(Bv, Rv), Equal.cong(Nat, Nat, t => Nat.sub(t, SW.value(r)), SW.value(b), Bv, eb), Equal.cong(Nat, Nat, t => Nat.sub(Bv, t), SW.value(r), Rv, er)))
      Equal.trans(F.F64, F.round_w(Bool.not(s), u, X.sub(b, r)), SF.round(Bool.not(s), SW.value(X.sub(b, r)), u), SF.round(Bool.not(s), Nat.sub(Bv, Rv), u), T.rw_value(Bool.not(s), u, X.sub(b, r), hu), Equal.cong(Nat, F.F64, t => SF.round(Bool.not(s), t, u), SW.value(X.sub(b, r)), Nat.sub(Bv, Rv), es))
    case False{}:
      Equal.trans(F.F64, F.round_w(s, u, r), SF.round(s, SW.value(r), u), SF.round(s, Rv, u), T.rw_value(s, u, r, hu), Equal.cong(Nat, F.F64, t => SF.round(s, t, u), SW.value(r), Rv, er))

# rm_fix on words is the spec's rnear on their values
def rmfix_v(+s: Bool, +u: Nat, +hu: {Nat.is_le(63n, u) == True{} : Bool}, +b: WU.U64, +r: WU.U64, +q: WU.U64, +Bv: Nat, +Rv: Nat, +Qv: Nat, +eb: {SW.value(b) == Bv : Nat}, +er: {SW.value(r) == Rv : Nat}, +hq: {Nat.mod(SW.value(q), 2n) == Nat.mod(Qv, 2n) : Nat}, +hRB: {Nat.is_le(Rv, Bv) == True{} : Bool}, +hf: {C.fits(53n, Rv) == True{} : Bool}) -> {F.rm_fix(s, u, b, r, q) == SF.rnear(s, Rv, Bv, Qv, u) : F.F64}:
  +R2 = Nat.add(Rv, Rv)
  +ea = addrr(r, Rv, er, hf)
  +f1 = Equal.trans(Bool, X.lt(b, X.add(r, r)), Nat.is_lt(SW.value(b), SW.value(X.add(r, r))), Nat.is_lt(Bv, R2), WA.lt_value(b, X.add(r, r)), Equal.trans(Bool, Nat.is_lt(SW.value(b), SW.value(X.add(r, r))), Nat.is_lt(Bv, SW.value(X.add(r, r))), Nat.is_lt(Bv, R2), Equal.cong(Nat, Bool, t => Nat.is_lt(t, SW.value(X.add(r, r))), SW.value(b), Bv, eb), Equal.cong(Nat, Bool, t => Nat.is_lt(Bv, t), SW.value(X.add(r, r)), R2, ea)))
  +f2 = Equal.trans(Bool, X.eq(X.add(r, r), b), Nat.is_eq(SW.value(X.add(r, r)), SW.value(b)), Nat.is_eq(R2, Bv), WA.eq_value(X.add(r, r), b), Equal.trans(Bool, Nat.is_eq(SW.value(X.add(r, r)), SW.value(b)), Nat.is_eq(R2, SW.value(b)), Nat.is_eq(R2, Bv), Equal.cong(Nat, Bool, t => Nat.is_eq(t, SW.value(b)), SW.value(X.add(r, r)), R2, addrr(r, Rv, er, hf)), Equal.cong(Nat, Bool, t => Nat.is_eq(R2, t), SW.value(b), Bv, eb)))
  +f3 = Equal.trans(Bool, X.odd(q), Nat.is_eq(Nat.mod(SW.value(q), 2n), 1n), Nat.is_eq(Nat.mod(Qv, 2n), 1n), WA.odd_value(q), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 1n), Nat.mod(SW.value(q), 2n), Nat.mod(Qv, 2n), hq))
  +g1 = Equal.cong(Bool, F.F64, t => F.rm_pick(s, u, b, r, Bool.or(t, Bool.and(X.eq(X.add(r, r), b), X.odd(q)))), X.lt(b, X.add(r, r)), Nat.is_lt(Bv, R2), f1)
  +g2 = Equal.cong(Bool, F.F64, t => F.rm_pick(s, u, b, r, Bool.or(Nat.is_lt(Bv, R2), Bool.and(t, X.odd(q)))), X.eq(X.add(r, r), b), Nat.is_eq(R2, Bv), f2)
  +g3 = Equal.cong(Bool, F.F64, t => F.rm_pick(s, u, b, r, Bool.or(Nat.is_lt(Bv, R2), Bool.and(Nat.is_eq(R2, Bv), t))), X.odd(q), Nat.is_eq(Nat.mod(Qv, 2n), 1n), f3)
  +a1 = F.rm_pick(s, u, b, r, Bool.or(Nat.is_lt(Bv, R2), Bool.and(X.eq(X.add(r, r), b), X.odd(q))))
  +a2 = F.rm_pick(s, u, b, r, Bool.or(Nat.is_lt(Bv, R2), Bool.and(Nat.is_eq(R2, Bv), X.odd(q))))
  +a3 = F.rm_pick(s, u, b, r, SF.rflip(Rv, Bv, Qv))
  Equal.trans(F.F64, F.rm_fix(s, u, b, r, q), a1, SF.rnear(s, Rv, Bv, Qv, u), g1, Equal.trans(F.F64, a1, a2, SF.rnear(s, Rv, Bv, Qv, u), g2, Equal.trans(F.F64, a2, a3, SF.rnear(s, Rv, Bv, Qv, u), g3, rmp_c(s, u, hu, b, r, Bv, Rv, eb, er, hRB, SF.rflip(Rv, Bv, Qv)))))

def RNs(+x: F.F64, +y: F.F64) -> F.F64:
  SF.rnear(SF.sign(x), Nat.mod(SF.ra(x, y), SF.rb(x, y)), SF.rb(x, y), Nat.div(SF.ra(x, y), SF.rb(x, y)), SF.rsc(x, y))

def RNd(+s: Bool, +a: Nat, +b: Nat, +m1: Nat, +m2: Nat) -> F.F64:
  SF.rnear(s, Nat.mod(C.shift(Nat.sub(a, b), m1), m2), m2, Nat.div(C.shift(Nat.sub(a, b), m1), m2), b)

def rn_spec_near(+x: F.F64, +y: F.F64, +hge: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == False{} : Bool}) -> {RNs(x, y) == RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y)) : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +xy = SF.xexp(y)
  +mx = SF.mant(x)
  +my = SF.mant(y)
  +e1 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), C.shift(Nat.sub(xy, t), my), Nat.div(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), t), Nat.min(xx, xy), xy, N.min_right(xx, xy, hge))
  +A = C.shift(Nat.sub(xx, xy), mx)
  +e2 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(A, C.shift(t, my)), C.shift(t, my), Nat.div(A, C.shift(t, my)), xy), Nat.sub(xy, xy), 0n, N.sub_self(xy))
  Equal.trans(F.F64, RNs(x, y), SF.rnear(s, Nat.mod(A, C.shift(Nat.sub(xy, xy), my)), C.shift(Nat.sub(xy, xy), my), Nat.div(A, C.shift(Nat.sub(xy, xy), my)), xy), RNd(s, xx, xy, mx, my), e1, e2)

def rnd_v(+x: F.F64, +y: F.F64) -> {RNd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))) == RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y)) : F.F64}:
  +e1 = Equal.cong(Bool, F.F64, t => RNd(t, F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e2 = Equal.cong(Nat, F.F64, t => RNd(SF.sign(x), t, F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +e3 = Equal.cong(Nat, F.F64, t => RNd(SF.sign(x), SF.xexp(x), t, SW.value(F.dmant(x)), SW.value(F.dmant(y))), F.dexp(y), SF.xexp(y), T.dexp_value(y))
  +e4 = Equal.cong(Nat, F.F64, t => RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), t, SW.value(F.dmant(y))), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
  +e5 = Equal.cong(Nat, F.F64, t => RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), t), SW.value(F.dmant(y)), SF.mant(y), T.dmant_value(y))
  +r1 = RNd(SF.sign(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r2 = RNd(SF.sign(x), SF.xexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r3 = RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
  +r4 = RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SW.value(F.dmant(y)))
  +G = RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y))
  Equal.trans(F.F64, RNd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))), r1, G, e1, Equal.trans(F.F64, r1, r2, G, e2, Equal.trans(F.F64, r2, r3, G, e3, Equal.trans(F.F64, r3, r4, G, e4, e5))))

def modlt(+n: Nat, +V: Nat, +hne: {Nat.is_eq(V, 0n) == False{} : Bool}) -> {Nat.is_lt(Nat.mod(n, V), V) == True{} : Bool}:
  match V:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(n, 0n), 0n) == True{} : Bool}, FL.true_ne_false(hne))
    case 1n+ +vp:
      MS.divmod_lt(n, vp)

def rm_near_c(+x: F.F64, +y: F.F64, +hzy: {SF.is_zero(y) == False{} : Bool}) -> {F.rm_qr(x, y, F.fm_qr(x, y)) == RNd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y))) : F.F64}:
  +Vx = SW.value(F.dmant(x))
  +Vy = SW.value(F.dmant(y))
  +Rv = Nat.mod(C.shift(DD(x, y), Vx), Vy)
  +Qv = Nat.div(C.shift(DD(x, y), Vx), Vy)
  +e0 = Equal.cong(WU.U64 & WU.U64, F.F64, p => F.rm_qr(x, y, p), F.fm_qr(x, y), (X.pfst(F.fm_qr(x, y)), X.psnd(F.fm_qr(x, y))), eta(F.fm_qr(x, y)))
  +hRB = N.lt_le(Rv, Vy, modlt(C.shift(DD(x, y), Vx), Vy, ynz(y, hzy)))
  +hf = SH.fits_lek(53n, Rv, Vy, N.lt_le(Rv, Vy, modlt(C.shift(DD(x, y), Vx), Vy, ynz(y, hzy))), T.mw53(y))
  +e1 = rmfix_v(F.signbit(x), F.dexp(y), T.dexp_ge(y), F.dmant(y), X.psnd(F.fm_qr(x, y)), X.pfst(F.fm_qr(x, y)), Vy, Rv, Qv, {==}, qr_r(x, y, hzy), qr_q(x, y, hzy), hRB, hf)
  Equal.trans(F.F64, F.rm_qr(x, y, F.fm_qr(x, y)), F.rm_fix(F.signbit(x), F.dexp(y), F.dmant(y), X.psnd(F.fm_qr(x, y)), X.pfst(F.fm_qr(x, y))), RNd(F.signbit(x), F.dexp(x), F.dexp(y), Vx, Vy), e0, e1)

def rn_spec_far(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}) -> {RNs(x, y) == SF.rnear(SF.sign(x), SF.mant(x), C.shift(Nat.sub(SF.xexp(y), SF.xexp(x)), SF.mant(y)), 0n, SF.xexp(x)) : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +xy = SF.xexp(y)
  +mx = SF.mant(x)
  +my = SF.mant(y)
  +S = C.shift(Nat.sub(xy, xx), my)
  +e1 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), C.shift(Nat.sub(xy, t), my), Nat.div(C.shift(Nat.sub(xx, t), mx), C.shift(Nat.sub(xy, t), my)), t), Nat.min(xx, xy), xx, N.min_left(xx, xy, hlt))
  +e2 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(C.shift(t, mx), S), S, Nat.div(C.shift(t, mx), S), xx), Nat.sub(xx, xx), 0n, N.sub_self(xx))
  +e3 = Equal.cong(Nat, F.F64, t => SF.rnear(s, t, S, Nat.div(mx, S), xx), Nat.mod(mx, S), mx, mod_small(mx, S, far_lt(x, y, hlt, 1n, {==})))
  +e4 = Equal.cong(Nat, F.F64, t => SF.rnear(s, mx, S, t, xx), Nat.div(mx, S), 0n, div_small(mx, S, far_lt(x, y, hlt, 1n, {==})))
  +r1 = SF.rnear(s, Nat.mod(C.shift(Nat.sub(xx, xx), mx), S), S, Nat.div(C.shift(Nat.sub(xx, xx), mx), S), xx)
  +r2 = SF.rnear(s, Nat.mod(mx, S), S, Nat.div(mx, S), xx)
  +r3 = SF.rnear(s, mx, S, Nat.div(mx, S), xx)
  +G = SF.rnear(s, mx, S, 0n, xx)
  Equal.trans(F.F64, RNs(x, y), r1, G, e1, Equal.trans(F.F64, r1, r2, G, e2, Equal.trans(F.F64, r2, r3, G, e3, e4)))

def xsub(+x: F.F64, +y: F.F64) -> {Nat.sub(F.dexp(y), F.dexp(x)) == Nat.sub(SF.xexp(y), SF.xexp(x)) : Nat}:
  Equal.trans(Nat, Nat.sub(F.dexp(y), F.dexp(x)), Nat.sub(SF.xexp(y), F.dexp(x)), Nat.sub(SF.xexp(y), SF.xexp(x)), Equal.cong(Nat, Nat, t => Nat.sub(t, F.dexp(x)), F.dexp(y), SF.xexp(y), T.dexp_value(y)), Equal.cong(Nat, Nat, t => Nat.sub(SF.xexp(y), t), F.dexp(x), SF.xexp(x), T.dexp_value(x)))

# exactly one scale step below y
def rm_one(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +hk: {Nat.sub(F.dexp(y), F.dexp(x)) == 1n : Nat}) -> {F.rm_fix(F.signbit(x), F.dexp(x), X.add(F.dmant(y), F.dmant(y)), F.dmant(x), WU.U64{0, 0}) == RNs(x, y) : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +mx = SF.mant(x)
  +my = SF.mant(y)
  +my2 = Nat.add(my, my)
  +ek = Equal.trans(Nat, Nat.sub(SF.xexp(y), xx), Nat.sub(F.dexp(y), F.dexp(x)), 1n, Equal.sym(Nat, Nat.sub(F.dexp(y), F.dexp(x)), Nat.sub(SF.xexp(y), xx), xsub(x, y)), hk)
  +h0 = L.subst(Nat, t => {Nat.is_lt(mx, C.shift(t, my)) == True{} : Bool}, Nat.sub(SF.xexp(y), xx), 1n, ek, far_lt(x, y, hlt, 1n, {==}))
  +h2 = L.subst(Nat, t => {Nat.is_lt(mx, t) == True{} : Bool}, Nat.double(my), my2, NA.double_self(my), h0)
  +e1 = rmfix_v(F.signbit(x), F.dexp(x), T.dexp_ge(x), X.add(F.dmant(y), F.dmant(y)), F.dmant(x), WU.U64{0, 0}, my2, mx, 0n, addrr(F.dmant(y), my, T.dmant_value(y), T.mant_fits(y)), T.dmant_value(x), {==}, N.lt_le(mx, my2, h2), T.mant_fits(x))
  +e2 = Equal.cong(Bool, F.F64, t => SF.rnear(t, mx, my2, 0n, F.dexp(x)), F.signbit(x), s, FB.signbit_value(x))
  +e3 = Equal.cong(Nat, F.F64, t => SF.rnear(s, mx, my2, 0n, t), F.dexp(x), xx, T.dexp_value(x))
  +S = C.shift(Nat.sub(SF.xexp(y), xx), my)
  +f1 = rn_spec_far(x, y, hlt)
  +f2 = Equal.cong(Nat, F.F64, t => SF.rnear(s, mx, C.shift(t, my), 0n, xx), Nat.sub(SF.xexp(y), xx), 1n, ek)
  +f3 = Equal.cong(Nat, F.F64, t => SF.rnear(s, mx, t, 0n, xx), Nat.double(my), my2, NA.double_self(my))
  +G = SF.rnear(s, mx, my2, 0n, xx)
  +eR = Equal.trans(F.F64, RNs(x, y), SF.rnear(s, mx, S, 0n, xx), G, f1, Equal.trans(F.F64, SF.rnear(s, mx, S, 0n, xx), SF.rnear(s, mx, Nat.double(my), 0n, xx), G, f2, f3))
  +a1 = SF.rnear(F.signbit(x), mx, my2, 0n, F.dexp(x))
  +a2 = SF.rnear(s, mx, my2, 0n, F.dexp(x))
  Equal.trans(F.F64, F.rm_fix(F.signbit(x), F.dexp(x), X.add(F.dmant(y), F.dmant(y)), F.dmant(x), WU.U64{0, 0}), a1, RNs(x, y), e1, Equal.trans(F.F64, a1, a2, RNs(x, y), e2, Equal.trans(F.F64, a2, G, RNs(x, y), e3, Equal.sym(F.F64, RNs(x, y), G, eR))))

def two_le(+k: Nat, +h1: {Nat.is_le(1n, k) == True{} : Bool}, +h2: {Nat.is_eq(k, 1n) == False{} : Bool}) -> {Nat.is_le(2n, k) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(2n, 0n) == True{} : Bool}, FL.true_ne_false(Equal.sym(Bool, False{}, True{}, h1)))
    case 1n:
      Empty.absurd({Nat.is_le(2n, 1n) == True{} : Bool}, FL.true_ne_false(h2))
    case 2n+ +kp:
      N.zero_le(kp)

def big54(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +hk: {Nat.is_eq(Nat.sub(SF.xexp(y), SF.xexp(x)), 1n) == False{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(C.shift(Nat.sub(SF.xexp(y), SF.xexp(x)), SF.mant(y)), Nat.add(SF.mant(x), SF.mant(x))) == False{} : Bool}:
  +k = Nat.sub(SF.xexp(y), SF.xexp(x))
  +S = C.shift(k, SF.mant(y))
  +m2 = Nat.add(SF.mant(x), SF.mant(x))
  +hk2 = two_le(k, FR.lt_sub_pos(SF.xexp(x), SF.xexp(y), hlt), hk)
  +f1 = Equal.trans(Bool, C.fits(Nat.add(k, 52n), S), C.fits(52n, SF.mant(y)), False{}, RT.fits_sh(k, 52n, SF.mant(y)), nf52(y, yn_c(x, y, hlt, Nat.is_eq(SF.efield(y), 0n), {==})))
  +h54 = Equal.trans(Bool, Nat.is_le(Nat.add(2n, 52n), Nat.add(k, 52n)), Nat.is_le(2n, k), True{}, FR.le_cancel_r(2n, k, 52n), hk2)
  +f2 = FL.nfit_mono(54n, Nat.add(k, 52n), S, h54, f1)
  +f3 = FR.fits_add1(53n, SF.mant(x), SF.mant(x), T.mant_fits(x), T.mant_fits(x))
  +l1 = Equal.trans(Bool, Nat.is_lt(m2, C.shift(54n, one)), C.fits(54n, m2), True{}, FR.lt_fit(54n, one, h1, m2), f3)
  +l2 = Equal.trans(Bool, Nat.is_le(C.shift(54n, one), S), Bool.not(C.fits(54n, S)), True{}, FB.le_fit(54n, one, h1, S), Equal.cong(Bool, Bool, b => Bool.not(b), C.fits(54n, S), False{}, f2))
  N.le_not_lt(S, m2, N.lt_le(m2, S, N.lt_le_trans(m2, C.shift(54n, one), S, l1, l2)))

def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(False{}, b), False{}, Equal.cong(Bool, Bool, t => Bool.or(t, b), a, False{}, ha), hb)

# two or more scale steps below y: x itself
def rm_many(+x: F.F64, +y: F.F64, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +hk: {Nat.is_eq(Nat.sub(F.dexp(y), F.dexp(x)), 1n) == False{} : Bool}, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}) -> {RNs(x, y) == x : F.F64}:
  +s = SF.sign(x)
  +xx = SF.xexp(x)
  +mx = SF.mant(x)
  +S = C.shift(Nat.sub(SF.xexp(y), xx), SF.mant(y))
  +hk2 = L.subst(Nat, t => {Nat.is_eq(t, 1n) == False{} : Bool}, Nat.sub(F.dexp(y), F.dexp(x)), Nat.sub(SF.xexp(y), xx), xsub(x, y), hk)
  +fl = or_ff(Nat.is_lt(S, Nat.add(mx, mx)), Bool.and(Nat.is_eq(Nat.add(mx, mx), S), False{}), big54(x, y, hlt, hk2, 1n, {==}), FR.and_f(Nat.is_eq(Nat.add(mx, mx), S)))
  +e1 = rn_spec_far(x, y, hlt)
  +e2 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.round(Bool.not(s), Nat.sub(S, mx), xx), SF.round(s, mx, xx)), SF.rflip(mx, S, 0n), False{}, fl)
  Equal.trans(F.F64, RNs(x, y), SF.rnear(s, mx, S, 0n, xx), x, e1, Equal.trans(F.F64, SF.rnear(s, mx, S, 0n, xx), SF.round(s, mx, xx), x, e2, rt(x, hfin)))

def rm_zero(+x: F.F64, +y: F.F64, +hzx: {SF.is_zero(x) == True{} : Bool}, +hzy: {SF.is_zero(y) == False{} : Bool}, +hfin: {Nat.is_lt(SF.efield(x), 2047n) == True{} : Bool}) -> {RNs(x, y) == x : F.F64}:
  +s = SF.sign(x)
  +em = N.eq_from_is_eq(SF.mant(x), 0n, Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), SF.is_zero(x), True{}, T.mant_z(x), hzx))
  +a = Nat.sub(SF.xexp(x), SF.rsc(x, y))
  +rb = SF.rb(x, y)
  +u = SF.rsc(x, y)
  +hmy = FL.nz_le(SF.mant(y), Equal.trans(Bool, Nat.is_eq(SF.mant(y), 0n), SF.is_zero(y), False{}, T.mant_z(y), hzy))
  +hrb = N.succ_le_lt(0n, rb, N.le_trans(1n, SF.mant(y), rb, hmy, WW.shift_ge(Nat.sub(SF.xexp(y), SF.rsc(x, y)), SF.mant(y))))
  +e1 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(C.shift(a, t), rb), rb, Nat.div(C.shift(a, t), rb), u), SF.mant(x), 0n, em)
  +e2 = Equal.cong(Nat, F.F64, t => SF.rnear(s, Nat.mod(t, rb), rb, Nat.div(t, rb), u), C.shift(a, 0n), 0n, WW.shift_zero(a))
  +e3 = Equal.cong(Nat, F.F64, t => SF.rnear(s, t, rb, Nat.div(0n, rb), u), Nat.mod(0n, rb), 0n, mod_small(0n, rb, hrb))
  +e4 = Equal.cong(Nat, F.F64, t => SF.rnear(s, 0n, rb, t, u), Nat.div(0n, rb), 0n, div_small(0n, rb, N.succ_le_lt(0n, rb, N.le_trans(1n, SF.mant(y), rb, FL.nz_le(SF.mant(y), Equal.trans(Bool, Nat.is_eq(SF.mant(y), 0n), SF.is_zero(y), False{}, T.mant_z(y), hzy)), WW.shift_ge(Nat.sub(SF.xexp(y), SF.rsc(x, y)), SF.mant(y))))))
  +fl = or_ff(Nat.is_lt(rb, 0n), Bool.and(Nat.is_eq(0n, rb), False{}), N.not_lt_zero(rb), FR.and_f(Nat.is_eq(0n, rb)))
  +e5 = Equal.cong(Bool, F.F64, b => SF.pick(F.F64, b, SF.round(Bool.not(s), Nat.sub(rb, 0n), u), SF.round(s, 0n, u)), SF.rflip(0n, rb, 0n), False{}, fl)
  +e6 = Equal.cong(Nat, F.F64, t => SF.round(s, t, SF.xexp(x)), 0n, SF.mant(x), Equal.sym(Nat, SF.mant(x), 0n, N.eq_from_is_eq(SF.mant(x), 0n, Equal.trans(Bool, Nat.is_eq(SF.mant(x), 0n), SF.is_zero(x), True{}, T.mant_z(x), hzx))))
  +r1 = SF.rnear(s, Nat.mod(C.shift(a, 0n), rb), rb, Nat.div(C.shift(a, 0n), rb), u)
  +r2 = SF.rnear(s, Nat.mod(0n, rb), rb, Nat.div(0n, rb), u)
  +r3 = SF.rnear(s, 0n, rb, Nat.div(0n, rb), u)
  +r4 = SF.rnear(s, 0n, rb, 0n, u)
  +r5 = SF.round(s, 0n, u)
  +r6 = SF.round(s, 0n, SF.xexp(x))
  Equal.trans(F.F64, RNs(x, y), r1, x, e1, Equal.trans(F.F64, r1, r2, x, e2, Equal.trans(F.F64, r2, r3, x, e3, Equal.trans(F.F64, r3, r4, x, e4, Equal.trans(F.F64, r4, r5, x, e5, Equal.trans(F.F64, r5, r6, x, {==}, Equal.trans(F.F64, r6, SF.round(s, SF.mant(x), SF.xexp(x)), x, e6, rt(x, hfin))))))))

def rone_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +hlt: {Nat.is_lt(SF.xexp(x), SF.xexp(y)) == True{} : Bool}, +o: Bool, +ho: {Nat.is_eq(Nat.sub(F.dexp(y), F.dexp(x)), 1n) == o : Bool}) -> {F.rm_near(x, y, o) == RNs(x, y) : F.F64}:
  match o:
    case True{}:
      rm_one(x, y, hlt, N.eq_from_is_eq(Nat.sub(F.dexp(y), F.dexp(x)), 1n, ho))
    case False{}:
      Equal.sym(F.F64, RNs(x, y), x, rm_many(x, y, hlt, ho, ok_fin(x, y, h)))

def rfar_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +far: Bool, +hfar: {Nat.is_lt(F.dexp(x), F.dexp(y)) == far : Bool}) -> {F.rm_far(x, y, far) == RNs(x, y) : F.F64}:
  match far:
    case True{}:
      rone_c(x, y, h, xlt(x, y, True{}, hfar), Nat.is_eq(Nat.sub(F.dexp(y), F.dexp(x)), 1n), {==})
    case False{}:
      +G = RNd(SF.sign(x), SF.xexp(x), SF.xexp(y), SF.mant(x), SF.mant(y))
      +a1 = RNd(F.signbit(x), F.dexp(x), F.dexp(y), SW.value(F.dmant(x)), SW.value(F.dmant(y)))
      Equal.trans(F.F64, F.rm_qr(x, y, F.fm_qr(x, y)), a1, RNs(x, y), rm_near_c(x, y, ok_zy(x, y, h)), Equal.trans(F.F64, a1, G, RNs(x, y), rnd_v(x, y), Equal.sym(F.F64, RNs(x, y), G, rn_spec_near(x, y, xlt(x, y, False{}, hfar)))))

def rz_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +zx: Bool, +hzx: {SF.is_zero(x) == zx : Bool}) -> {F.rm_z(x, y, zx) == RNs(x, y) : F.F64}:
  match zx:
    case True{}:
      Equal.sym(F.F64, RNs(x, y), x, rm_zero(x, y, hzx, ok_zy(x, y, h), ok_fin(x, y, h)))
    case False{}:
      rfar_c(x, y, h, Nat.is_lt(F.dexp(x), F.dexp(y)), {==})

def ryi_c(+x: F.F64, +y: F.F64, +h: {SF.rbad(x, y) == False{} : Bool}, +yi: Bool) -> {F.rm_yi(x, y, yi) == SF.pick(F.F64, yi, x, RNs(x, y)) : F.F64}:
  match yi:
    case True{}:
      {==}
    case False{}:
      Equal.trans(F.F64, F.rm_z(x, y, F.is_zero(x)), F.rm_z(x, y, SF.is_zero(x)), RNs(x, y), Equal.cong(Bool, F.F64, t => F.rm_z(x, y, t), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x)), rz_c(x, y, h, SF.is_zero(x), {==}))

def rb_c(+x: F.F64, +y: F.F64, +bad: Bool, +h: {SF.rbad(x, y) == bad : Bool}) -> {F.rm_bad(x, y, bad) == SF.pick(F.F64, bad, SF.qnan(), SF.pick(F.F64, SF.is_inf(y), x, RNs(x, y))) : F.F64}:
  match bad:
    case True{}:
      {==}
    case False{}:
      Equal.trans(F.F64, F.rm_yi(x, y, F.is_inf(y)), F.rm_yi(x, y, SF.is_inf(y)), SF.pick(F.F64, SF.is_inf(y), x, RNs(x, y)), Equal.cong(Bool, F.F64, t => F.rm_yi(x, y, t), F.is_inf(y), SF.is_inf(y), FB.is_inf_value(y)), ryi_c(x, y, h, SF.is_inf(y)))

def remainder_value(+x: F.F64, +y: F.F64) -> SF.Remainder.value(x, y):
  +e1 = Equal.cong(Bool, F.F64, t => F.rm_bad(x, y, t), Bool.or(Bool.or(F.unordered(x, y), F.is_inf(x)), F.is_zero(y)), SF.rbad(x, y), badv(x, y))
  Equal.trans(F.F64, F.remainder(x, y), F.rm_bad(x, y, SF.rbad(x, y)), SF.remainder(x, y), e1, rb_c(x, y, SF.rbad(x, y), {==}))
