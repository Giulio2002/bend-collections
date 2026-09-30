import Base
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../spec/lib/common.bend as SC2
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/typed/width.bend as WW
import ../curve25519/num.bend as M
import ./pw.bend as PW
import ./nl.bend as NL

# The field's products through the native 32-bit multiplier
# (src/crypto/curve25519/limbs.bend pu, pm, convp): for limbs below 2^19,
# pm(a, b) == a b (b split at bit 9, both half products below 2^29 < 2^32),
# so convp is conv, the schoolbook product the rest of the proofs reason
# about.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def ml(+x: Nat, +y: Nat, +c: Nat, +e: {x == y : Nat}) -> {Nat.mul(x, c) == Nat.mul(y, c) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(z, c), x, y, e)

def mr(+c: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.mul(c, x) == Nat.mul(c, y) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(c, z), x, y, e)

# U32 products below 2^32 are exact
def mulv(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +c: U32, +h: {Nat.is_lt(Nat.mul(v(a), v(c)), WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.mul(a, c)) == Nat.mul(v(a), v(c)) : Nat}:
  match a c:
    case U32{+x} U32{+y}:
      +ex = U.to_nat_word(x)
      +ey = U.to_nat_word(y)
      +es = tr(Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), Equal.cong(Nat, Nat, z => Nat.mul(z, v(U32{y})), v(U32{x}), S.unsigned(32n, x), ex), Equal.cong(Nat, Nat, z => Nat.mul(S.unsigned(32n, x), z), v(U32{y}), S.unsigned(32n, y), ey))
      +h2 = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), es, h)
      +m = Word.mul(32n, x, y)
      tr(U32.to_nat(U32{m}), S.unsigned(32n, m), Nat.mul(v(U32{x}), v(U32{y})), U.to_nat_word(m), tr(S.unsigned(32n, m), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), Nat.mul(v(U32{x}), v(U32{y})), WD.mul_exact(32n, one, h1, x, y, h2), sy(Nat.mul(v(U32{x}), v(U32{y})), Nat.mul(S.unsigned(32n, x), S.unsigned(32n, y)), es)))

def sb(+k: Nat, +x: Nat) -> {S.scale_binary(k, x) == SC2.shift(k, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), S.scale_binary(p, x), SC2.shift(p, x), sb(p, x))

# a value below 2^32 survives from_nat / to_nat (the bound reaches the
# closed 2^32 only through equal terms, never by evaluation)
def tnfn(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_lt(x, WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.from_nat(x)) == x : Nat}:
  +e0 = sb(32n, one)
  +e1 = Equal.cong(Nat, Nat, z => SC2.shift(32n, z), one, 1n, h1)
  +e2 = WW.shift_one(32n)
  +e = Equal.trans(Nat, WD.sc(32n, one), SC2.shift(32n, one), SC2.pow2(32n), e0, Equal.trans(Nat, SC2.shift(32n, one), SC2.shift(32n, 1n), SC2.pow2(32n), e1, e2))
  U.to_nat_from_nat(x, 32n, {==}, L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, WD.sc(32n, one), SC2.pow2(32n), e, hx))

# pu(a, b) == a b when a, b and a b are below 2^32
def pu_eq(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +b: Nat, +ha: {Nat.is_lt(a, WD.sc(32n, one)) == True{} : Bool}, +hb: {Nat.is_lt(b, WD.sc(32n, one)) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LS.pu(a, b) == Nat.mul(a, b) : Nat}:
  +ua = U32.from_nat(a)
  +ub = U32.from_nat(b)
  +ea = tnfn(one, h1, a, ha)
  +eb = tnfn(one, h1, b, hb)
  +ep = tr(Nat.mul(v(ua), v(ub)), Nat.mul(a, v(ub)), Nat.mul(a, b), ml(v(ua), a, v(ub), ea), mr(a, v(ub), b, eb))
  +hp = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.mul(a, b), Nat.mul(v(ua), v(ub)), sy(Nat.mul(v(ua), v(ub)), Nat.mul(a, b), ep), hab)
  tr(v(U32.mul(ua, ub)), Nat.mul(v(ua), v(ub)), Nat.mul(a, b), mulv(one, h1, ua, ub, hp), ep)

def k512(+one: Nat, +h1: {one == 1n : Nat}) -> {WD.sc(9n, one) == 512n : Nat}:
  L.subst(Nat, o => {WD.sc(9n, o) == 512n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 2^k < 2^32 for k <= 29 as used here
def lt32(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +k: Nat, +d: Nat, +hd: {Nat.add(d, 1n+k) == 32n : Nat}, +hx: {Nat.is_lt(x, WD.sc(k, one)) == True{} : Bool}) -> {Nat.is_lt(x, WD.sc(32n, one)) == True{} : Bool}:
  N.lt_trans(x, WD.sc(k, one), WD.sc(32n, one), hx, L.subst(Nat, z => {Nat.is_lt(WD.sc(k, one), WD.sc(z, one)) == True{} : Bool}, Nat.add(d, 1n+k), 32n, hd, PW.lt_sc(d, k, one, h1)))

# x y < 2^(j + k) for x < 2^j, y < 2^k
def lt_prod(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +y: Nat, +j: Nat, +k: Nat, +hx: {Nat.is_lt(x, WD.sc(j, one)) == True{} : Bool}, +hy: {Nat.is_lt(y, WD.sc(k, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), WD.sc(Nat.add(j, k), one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.mul(x, y), z) == True{} : Bool}, Nat.mul(WD.sc(j, one), WD.sc(k, one)), WD.sc(Nat.add(j, k), one), PW.scsc(j, k, one, h1), NL.lt_mul2(x, y, WD.sc(j, one), WD.sc(k, one), hx, hy))

# b div 512 < 2^10 for b < 2^19
def hi_lt(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +hb: {Nat.is_lt(b, WD.sc(19n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(b, 512n), WD.sc(10n, one)) == True{} : Bool}:
  +E = WD.sc(10n, one)
  +e0 = NR.le_div(511n, E, b)
  +e19 = tr(Nat.mul(E, 512n), Nat.mul(E, WD.sc(9n, one)), WD.sc(19n, one), mr(E, 512n, WD.sc(9n, one), sy(WD.sc(9n, one), 512n, k512(one, h1))), PW.scsc(10n, 9n, one, h1))
  +nle = N.lt_not_le(b, Nat.mul(E, 512n), L.subst(Nat, z => {Nat.is_lt(b, z) == True{} : Bool}, WD.sc(19n, one), Nat.mul(E, 512n), sy(Nat.mul(E, 512n), WD.sc(19n, one), e19), hb))
  N.not_le_lt(E, Nat.div(b, 512n), Equal.trans(Bool, Nat.is_le(E, Nat.div(b, 512n)), Nat.is_le(Nat.mul(E, 512n), b), False{}, e0, nle))

# pm(a, b) == a b for a, b < 2^19
def pm_eq(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +b: Nat, +ha: {Nat.is_lt(a, WD.sc(19n, one)) == True{} : Bool}, +hb: {Nat.is_lt(b, WD.sc(19n, one)) == True{} : Bool}) -> {LS.pm(a, b) == Nat.mul(a, b) : Nat}:
  +lo = Nat.mod(b, 512n)
  +hi = Nat.div(b, 512n)
  +hlo = L.subst(Nat, z => {Nat.is_lt(lo, z) == True{} : Bool}, 512n, WD.sc(9n, one), sy(WD.sc(9n, one), 512n, k512(one, h1)), NR.dm_lt(511n, b))
  +hhi = hi_lt(one, h1, b, hb)
  +a32 = lt32(one, h1, a, 19n, 12n, {==}, ha)
  +e1 = pu_eq(one, h1, a, lo, a32, lt32(one, h1, lo, 9n, 22n, {==}, hlo), lt32(one, h1, Nat.mul(a, lo), 28n, 3n, {==}, lt_prod(one, h1, a, lo, 19n, 9n, ha, hlo)))
  +e2 = pu_eq(one, h1, a, hi, a32, lt32(one, h1, hi, 10n, 21n, {==}, hhi), lt32(one, h1, Nat.mul(a, hi), 29n, 2n, {==}, lt_prod(one, h1, a, hi, 19n, 10n, ha, hhi)))
  +e3 = M.cong_add(LS.pu(a, lo), Nat.mul(a, lo), Nat.mul(LS.pu(a, hi), 512n), Nat.mul(Nat.mul(a, hi), 512n), e1, ml(LS.pu(a, hi), Nat.mul(a, hi), 512n, e2))
  +eb = NR.dm_eq(511n, b)
  +e4 = tr(Nat.mul(a, b), Nat.mul(a, Nat.add(Nat.mul(hi, 512n), lo)), Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), mr(a, b, Nat.add(Nat.mul(hi, 512n), lo), eb), NA.mul_add_left(a, Nat.mul(hi, 512n), lo))
  +e5 = tr(Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), Nat.add(Nat.mul(a, lo), Nat.mul(a, Nat.mul(hi, 512n))), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), NA.add_comm(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), M.cong_r(Nat.mul(a, lo), Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(Nat.mul(a, hi), 512n), sy(Nat.mul(Nat.mul(a, hi), 512n), Nat.mul(a, Nat.mul(hi, 512n)), NA.mul_assoc(a, hi, 512n))))
  tr(LS.pm(a, b), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), Nat.mul(a, b), e3, sy(Nat.mul(a, b), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), tr(Nat.mul(a, b), Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), e4, e5)))

def scalp_eq(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +ys: List<&2, Nat>, +ha: {Nat.is_lt(a, WD.sc(19n, one)) == True{} : Bool}, +hy: {FV.below(ys, WD.sc(19n, one)) == True{} : Bool}) -> {LS.scalp(a, ys) == LS.scal(a, ys) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      +s = WD.sc(19n, one)
      +e1 = Equal.cong(Nat, List<&2, Nat>, z => Con{z, LS.scalp(a, yt)}, LS.pm(a, y), Nat.mul(a, y), pm_eq(one, h1, a, y, ha, NL.below_head(y, yt, s, hy)))
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{Nat.mul(a, y), z}, LS.scalp(a, yt), LS.scal(a, yt), scalp_eq(one, h1, a, yt, ha, NL.below_tail(y, yt, s, hy)))
      Equal.trans(List<&2, Nat>, Con{LS.pm(a, y), LS.scalp(a, yt)}, Con{Nat.mul(a, y), LS.scalp(a, yt)}, Con{Nat.mul(a, y), LS.scal(a, yt)}, e1, e2)

# convp is conv on limbs below 2^19
def convp_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {FV.below(xs, WD.sc(19n, one)) == True{} : Bool}, +hy: {FV.below(ys, WD.sc(19n, one)) == True{} : Bool}) -> {LS.convp(xs, ys) == LS.conv(xs, ys) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          +s = WD.sc(19n, one)
          +hxh = NL.below_head(x, xt, s, hx)
          +e0 = pm_eq(one, h1, x, y, hxh, NL.below_head(y, yt, s, hy))
          +e1 = scalp_eq(one, h1, x, yt, hxh, NL.below_tail(y, yt, s, hy))
          +e2 = convp_eq(one, h1, xt, Con{y, yt}, NL.below_tail(x, xt, s, hx), hy)
          +T0 = LS.addl(LS.scalp(x, yt), LS.convp(xt, Con{y, yt}))
          +T1 = LS.addl(LS.scal(x, yt), LS.convp(xt, Con{y, yt}))
          +T2 = LS.addl(LS.scal(x, yt), LS.conv(xt, Con{y, yt}))
          +et = Equal.trans(List<&2, Nat>, T0, T1, T2, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.addl(z, LS.convp(xt, Con{y, yt})), LS.scalp(x, yt), LS.scal(x, yt), e1), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.addl(LS.scal(x, yt), z), LS.convp(xt, Con{y, yt}), LS.conv(xt, Con{y, yt}), e2))
          Equal.trans(List<&2, Nat>, Con{LS.pm(x, y), T0}, Con{Nat.mul(x, y), T0}, Con{Nat.mul(x, y), T2}, Equal.cong(Nat, List<&2, Nat>, z => Con{z, T0}, LS.pm(x, y), Nat.mul(x, y), e0), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{Nat.mul(x, y), z}, T0, T2, et))
