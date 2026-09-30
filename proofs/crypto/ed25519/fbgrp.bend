import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/edwards.bend as G
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/ed25519_group.bend as EG
import ../../../src/crypto/ed25519/point.bend as PT
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./group/gpt.bend as GP
import ./prel.bend as PR
import ./group/ext.bend as GX
import ./group/smul.bend as SM
import ./pfb.bend as PFB
import ./fbspec.bend as FB
import ../../math/typed/width.bend as WI
import ../curve25519/limbs.bend as LM
import ../fe/conv.bend as CV
import ./bytefield.bend as BF

# The table form of [k] B (fbspec.bend) in the affine group of the curve
# (spec/crypto/curve25519/edwards.bend): every point the table form builds
# is valid, and its affine point is the multiple G.nmul the digits say.
# VA(a, q): the extended point a is valid and its affine point is q.

def VA(+mp: Nat, +d: Nat, +a: SE.EPt, +q: G.APt) -> Data:
  PR.DP(EG.Valid(1n+mp, d, a), PR.DP({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q)))

def vV(+mp: Nat, +d: Nat, +a: SE.EPt, +q: G.APt, +h: VA(mp, d, a, q)) -> EG.Valid(1n+mp, d, a):
  PR.fst(EG.Valid(1n+mp, d, a), PR.DP({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q)), h)

def vE(+mp: Nat, +d: Nat, +a: SE.EPt, +q: G.APt, +h: VA(mp, d, a, q)) -> {EG.affine(1n+mp, a) == q : G.APt}:
  PR.fst({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q), PR.snd(EG.Valid(1n+mp, d, a), PR.DP({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q)), h))

def vO(+mp: Nat, +d: Nat, +a: SE.EPt, +q: G.APt, +h: VA(mp, d, a, q)) -> G.OnCurve(1n+mp, d, q):
  PR.snd({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q), PR.snd(EG.Valid(1n+mp, d, a), PR.DP({EG.affine(1n+mp, a) == q : G.APt}, G.OnCurve(1n+mp, d, q)), h))

# from validity and the affine point
def va_mk(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +hv: EG.Valid(1n+mp, d, a), +he: {EG.affine(1n+mp, a) == q : G.APt}) -> VA(mp, d, a, q):
  (hv, (he, L.subst(G.APt, z => G.OnCurve(1n+mp, d, z), EG.affine(1n+mp, a), q, he, GX.aff_on(mp, d, a, hv))))

# the same point written another way
def va_cast(+mp: Nat, +d: Nat, +a: SE.EPt, +q: G.APt, +q2: G.APt, +e: {q == q2 : G.APt}, +h: VA(mp, d, a, q)) -> VA(mp, d, a, q2):
  L.subst(G.APt, z => VA(mp, d, a, z), q, q2, e, h)

def aadd2(+mp: Nat, +d: Nat, +a: G.APt, +a2: G.APt, +b: G.APt, +b2: G.APt, +ea: {a == a2 : G.APt}, +eb: {b == b2 : G.APt}) -> {G.aadd(1n+mp, d, a, b) == G.aadd(1n+mp, d, a2, b2) : G.APt}:
  Equal.trans(G.APt, G.aadd(1n+mp, d, a, b), G.aadd(1n+mp, d, a2, b), G.aadd(1n+mp, d, a2, b2), Equal.cong(G.APt, G.APt, z => G.aadd(1n+mp, d, z, b), a, a2, ea), Equal.cong(G.APt, G.APt, z => G.aadd(1n+mp, d, a2, z), b, b2, eb))

def va_id(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d)) -> VA(mp, d, SE.identity(), G.azero()):
  va_mk(mp, d, hc, SE.identity(), G.azero(), GX.id_valid(mp, d, hc), GX.id_aff(mp, d, hc))

def va_add(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +b: SE.EPt, +qa: G.APt, +qb: G.APt, +ha: VA(mp, d, a, qa), +hb: VA(mp, d, b, qb)) -> VA(mp, d, SE.add(1n+mp, d, a, b), G.aadd(1n+mp, d, qa, qb)):
  +P = {1n+mp : Nat}
  +va = vV(mp, d, a, qa, ha)
  +vb = vV(mp, d, b, qb, hb)
  va_mk(mp, d, hc, SE.add(P, d, a, b), G.aadd(P, d, qa, qb), GX.add_valid(mp, d, hc, a, b, va, vb), Equal.trans(G.APt, EG.affine(P, SE.add(P, d, a, b)), G.aadd(P, d, EG.affine(P, a), EG.affine(P, b)), G.aadd(P, d, qa, qb), GX.add_aff(mp, d, hc, a, b, va, vb), aadd2(mp, d, EG.affine(P, a), qa, EG.affine(P, b), qb, vE(mp, d, a, qa, ha), vE(mp, d, b, qb, hb))))

# q + q == [2] q
def two_eq(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +q: G.APt, +hq: G.OnCurve(1n+mp, d, q)) -> {G.aadd(1n+mp, d, q, q) == G.nmul(1n+mp, d, 2n, q) : G.APt}:
  Equal.cong(G.APt, G.APt, z => G.aadd(1n+mp, d, q, z), q, G.aadd(1n+mp, d, q, G.azero()), Equal.sym(G.APt, G.aadd(1n+mp, d, q, G.azero()), q, GP.add_zero_r(mp, d, hc, q, hq)))

def va_dbl(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +h: VA(mp, d, a, q)) -> VA(mp, d, SE.double(1n+mp, a), G.nmul(1n+mp, d, 2n, q)):
  +P = {1n+mp : Nat}
  +va = vV(mp, d, a, q, h)
  +e1 = Equal.trans(G.APt, EG.affine(P, SE.double(P, a)), G.aadd(P, d, EG.affine(P, a), EG.affine(P, a)), G.aadd(P, d, q, q), GX.dbl_aff(mp, d, hc, a, va), aadd2(mp, d, EG.affine(P, a), q, EG.affine(P, a), q, vE(mp, d, a, q, h), vE(mp, d, a, q, h)))
  va_mk(mp, d, hc, SE.double(P, a), G.nmul(P, d, 2n, q), GX.dbl_valid(mp, d, hc, a, va), Equal.trans(G.APt, EG.affine(P, SE.double(P, a)), G.aadd(P, d, q, q), G.nmul(P, d, 2n, q), e1, two_eq(mp, d, hc, q, vO(mp, d, a, q, h))))

# [2] ([k] q) == [2 k] q
def dbl_mul(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +k: Nat, +q: G.APt, +hq: G.OnCurve(1n+mp, d, q)) -> {G.nmul(1n+mp, d, 2n, G.nmul(1n+mp, d, k, q)) == G.nmul(1n+mp, d, Nat.mul(2n, k), q) : G.APt}:
  Equal.sym(G.APt, G.nmul(1n+mp, d, Nat.mul(2n, k), q), G.nmul(1n+mp, d, 2n, G.nmul(1n+mp, d, k, q)), GP.nmul_mul(mp, d, hc, 2n, k, q, hq))

# 16 a
def va_dbl4(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +h: VA(mp, d, a, q)) -> VA(mp, d, FB.sdbl4(1n+mp, a), G.nmul(1n+mp, d, 16n, q)):
  +P = {1n+mp : Nat}
  +hq = vO(mp, d, a, q, h)
  +a1 = SE.double(P, a)
  +g1 = va_dbl(mp, d, hc, a, q, h)
  +a2 = SE.double(P, a1)
  +g2 = va_cast(mp, d, a2, G.nmul(P, d, 2n, G.nmul(P, d, 2n, q)), G.nmul(P, d, 4n, q), dbl_mul(mp, d, hc, 2n, q, hq), va_dbl(mp, d, hc, a1, G.nmul(P, d, 2n, q), g1))
  +a3 = SE.double(P, a2)
  +g3 = va_cast(mp, d, a3, G.nmul(P, d, 2n, G.nmul(P, d, 4n, q)), G.nmul(P, d, 8n, q), dbl_mul(mp, d, hc, 4n, q, hq), va_dbl(mp, d, hc, a2, G.nmul(P, d, 4n, q), g2))
  va_cast(mp, d, SE.double(P, a3), G.nmul(P, d, 2n, G.nmul(P, d, 8n, q)), G.nmul(P, d, 16n, q), dbl_mul(mp, d, hc, 8n, q, hq), va_dbl(mp, d, hc, a3, G.nmul(P, d, 8n, q), g3))

# entry j of [m, m + a, ...] (n entries), for m == [i] a: [i + j] a
def va_row_go(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +n: Nat, +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +m: SE.EPt, +i: Nat, +hm: VA(mp, d, m, G.nmul(1n+mp, d, i, q)), +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> VA(mp, d, FB.snth(j, FB.srow_go(n, 1n+mp, d, a, m)), G.nmul(1n+mp, d, Nat.add(i, j), q)):
  match n:
    case 0n:
      Empty.absurd(VA(mp, d, FB.snth(j, FB.srow_go(0n, 1n+mp, d, a, m)), G.nmul(1n+mp, d, Nat.add(i, j), q)), N.lt_zero_absurd(j, hj))
    case 1n+ +k:
      match j:
        case 0n:
          va_cast(mp, d, m, G.nmul(1n+mp, d, i, q), G.nmul(1n+mp, d, Nat.add(i, 0n), q), Equal.cong(Nat, G.APt, z => G.nmul(1n+mp, d, z, q), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i))), hm)
        case 1n+ +j2:
          +P = {1n+mp : Nat}
          +m2 = SE.add(P, d, m, a)
          +hm2 = va_cast(mp, d, m2, G.aadd(P, d, G.nmul(P, d, i, q), q), G.nmul(P, d, 1n+i, q), GP.add_comm(mp, d, G.nmul(P, d, i, q), q), va_add(mp, d, hc, m, a, G.nmul(P, d, i, q), q, hm, ha))
          va_cast(mp, d, FB.snth(j2, FB.srow_go(k, P, d, a, m2)), G.nmul(P, d, 1n+Nat.add(i, j2), q), G.nmul(P, d, Nat.add(i, 1n+j2), q), Equal.cong(Nat, G.APt, z => G.nmul(P, d, z, q), 1n+Nat.add(i, j2), Nat.add(i, 1n+j2), Equal.sym(Nat, Nat.add(i, 1n+j2), 1n+Nat.add(i, j2), N.add_succ(i, j2))), va_row_go(mp, d, hc, k, a, q, ha, m2, 1n+i, hm2, j2, hj))

# entry dg of the row of a: [dg] a
def va_row(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +dg: Nat, +hd: {Nat.is_lt(dg, 16n) == True{} : Bool}) -> VA(mp, d, FB.snth(dg, FB.srow(1n+mp, d, a)), G.nmul(1n+mp, d, dg, q)):
  match dg:
    case 0n:
      va_id(mp, d, hc)
    case 1n+ +j:
      +P = {1n+mp : Nat}
      +h1 = va_cast(mp, d, a, q, G.nmul(P, d, 1n, q), Equal.sym(G.APt, G.nmul(P, d, 1n, q), q, GP.add_zero_r(mp, d, hc, q, vO(mp, d, a, q, ha))), ha)
      va_row_go(mp, d, hc, 15n, a, q, ha, a, 1n, h1, j, hd)

# the number the first n digits write in base 16
def dval(n: Nat, ds: List<&2, Nat>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      match ds:
        case Nil{}:
          0n
        case Con{dg, dt}:
          Nat.add(dg, Nat.mul(dval(k, dt), 16n))

# the sum over the first n rows of the table of a: acc + [dval] a
def va_fb(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +n: Nat, +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +ds: List<&2, Nat>, +hd: {PFB.dok(ds) == True{} : Bool}, +acc: SE.EPt, +qacc: G.APt, +hacc: VA(mp, d, acc, qacc)) -> VA(mp, d, FB.sfb(1n+mp, d, FB.stab(n, 1n+mp, d, a), ds, acc), G.aadd(1n+mp, d, qacc, G.nmul(1n+mp, d, dval(n, ds), q))):
  match n:
    case 0n:
      va_cast(mp, d, acc, qacc, G.aadd(1n+mp, d, qacc, G.azero()), Equal.sym(G.APt, G.aadd(1n+mp, d, qacc, G.azero()), qacc, GP.add_zero_r(mp, d, hc, qacc, vO(mp, d, acc, qacc, hacc))), hacc)
    case 1n+ +k:
      match ds:
        case Nil{}:
          va_cast(mp, d, acc, qacc, G.aadd(1n+mp, d, qacc, G.azero()), Equal.sym(G.APt, G.aadd(1n+mp, d, qacc, G.azero()), qacc, GP.add_zero_r(mp, d, hc, qacc, vO(mp, d, acc, qacc, hacc))), hacc)
        case Con{+dg, +dt}:
          +P = {1n+mp : Nat}
          +hq = vO(mp, d, a, q, ha)
          +ho = vO(mp, d, acc, qacc, hacc)
          +X = G.nmul(P, d, dg, q)
          +M = Nat.mul(dval(k, dt), 16n)
          +Y = G.nmul(P, d, M, q)
          +e = SE.add(P, d, acc, FB.snth(dg, FB.srow(P, d, a)))
          +he = va_add(mp, d, hc, acc, FB.snth(dg, FB.srow(P, d, a)), qacc, X, hacc, va_row(mp, d, hc, a, q, ha, dg, L.and_left(Nat.is_lt(dg, 16n), PFB.dok(dt), hd)))
          +ih = va_fb(mp, d, hc, k, FB.sdbl4(P, a), G.nmul(P, d, 16n, q), va_dbl4(mp, d, hc, a, q, ha), dt, L.and_right(Nat.is_lt(dg, 16n), PFB.dok(dt), hd), e, G.aadd(P, d, qacc, X), he)
          +Y0 = G.nmul(P, d, dval(k, dt), G.nmul(P, d, 16n, q))
          +e1 = Equal.cong(G.APt, G.APt, z => G.aadd(P, d, G.aadd(P, d, qacc, X), z), Y0, Y, Equal.sym(G.APt, Y, Y0, GP.nmul_mul(mp, d, hc, dval(k, dt), 16n, q, hq)))
          +e2 = GP.add_assoc(mp, d, hc, qacc, X, Y, ho, GP.nmul_on(mp, d, hc, dg, q, hq), GP.nmul_on(mp, d, hc, M, q, hq))
          +e3 = Equal.cong(G.APt, G.APt, z => G.aadd(P, d, qacc, z), G.aadd(P, d, X, Y), G.nmul(P, d, Nat.add(dg, M), q), Equal.sym(G.APt, G.nmul(P, d, Nat.add(dg, M), q), G.aadd(P, d, X, Y), GP.nmul_add(mp, d, hc, dg, M, q, hq)))
          va_cast(mp, d, FB.sfb(P, d, FB.stab(k, P, d, FB.sdbl4(P, a)), dt, e), G.aadd(P, d, G.aadd(P, d, qacc, X), Y0), G.aadd(P, d, qacc, G.nmul(P, d, Nat.add(dg, M), q)), Equal.trans(G.APt, G.aadd(P, d, G.aadd(P, d, qacc, X), Y0), G.aadd(P, d, G.aadd(P, d, qacc, X), Y), G.aadd(P, d, qacc, G.nmul(P, d, Nat.add(dg, M), q)), e1, Equal.trans(G.APt, G.aadd(P, d, G.aadd(P, d, qacc, X), Y), G.aadd(P, d, qacc, G.aadd(P, d, X, Y)), G.aadd(P, d, qacc, G.nmul(P, d, Nat.add(dg, M), q)), e2, e3)), ih)

# ---- the digits of a byte string ----

# 2 m
def dn(m: Nat) -> Nat:
  match m:
    case 0n:
      0n
    case 1n+k:
      2n+dn(k)

# the 2 m hexadecimal digits of m bytes write their value
def dval_nibs(+m: Nat, +bs: List<&2, U32>, +hb: {FS.bytes_ok(m, bs) == True{} : Bool}) -> {dval(dn(m), PT.nibs(bs)) == FS.value(bs) : Nat}:
  match m bs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({dval(dn(0n), PT.nibs(Con{x, xt})) == FS.value(Con{x, xt}) : Nat}, L.false_true(hb))
    case 1n+k Nil{}:
      Empty.absurd({dval(dn(1n+k), PT.nibs(Nil{})) == FS.value(Nil{}) : Nat}, L.false_true(hb))
    case 1n+ +k Con{+b, +bt}:
      +n = U32.to_nat(b)
      +V = FS.value(bt)
      +W = dval(dn(k), PT.nibs(bt))
      +r = Nat.mod(n, 16n)
      +q = Nat.div(n, 16n)
      +ih = dval_nibs(k, bt, L.and_right(Nat.is_lt(U32.to_nat(b), 256n), FS.bytes_ok(k, bt), hb))
      +T = Nat.mul(Nat.mul(W, 16n), 16n)
      +s1 = Equal.cong(Nat, Nat, z => Nat.add(r, z), Nat.mul(Nat.add(q, Nat.mul(W, 16n)), 16n), Nat.add(Nat.mul(q, 16n), T), NA.mul_add_right(q, Nat.mul(W, 16n), 16n))
      +s2 = Equal.sym(Nat, Nat.add(Nat.add(r, Nat.mul(q, 16n)), T), Nat.add(r, Nat.add(Nat.mul(q, 16n), T)), N.add_assoc(r, Nat.mul(q, 16n), T))
      +en = Equal.trans(Nat, Nat.add(r, Nat.mul(q, 16n)), Nat.add(Nat.mul(q, 16n), r), n, NA.add_comm(r, Nat.mul(q, 16n)), Equal.sym(Nat, n, Nat.add(Nat.mul(q, 16n), r), NR.dm_eq(15n, n)))
      +eT = Equal.trans(Nat, T, C.shift(8n, W), C.shift(8n, V), Equal.trans(Nat, T, Nat.mul(C.shift(4n, W), 16n), C.shift(8n, W), Equal.cong(Nat, Nat, z => Nat.mul(z, 16n), Nat.mul(W, 16n), C.shift(4n, W), AR.mul_sc(4n, W)), AR.mul_sc(4n, C.shift(4n, W))), Equal.cong(Nat, Nat, z => C.shift(8n, z), W, V, ih))
      Equal.trans(Nat, Nat.add(r, Nat.mul(Nat.add(q, Nat.mul(W, 16n)), 16n)), Nat.add(r, Nat.add(Nat.mul(q, 16n), T)), Nat.add(n, C.shift(8n, V)), s1, Equal.trans(Nat, Nat.add(r, Nat.add(Nat.mul(q, 16n), T)), Nat.add(Nat.add(r, Nat.mul(q, 16n)), T), Nat.add(n, C.shift(8n, V)), s2, Equal.trans(Nat, Nat.add(Nat.add(r, Nat.mul(q, 16n)), T), Nat.add(n, T), Nat.add(n, C.shift(8n, V)), Equal.cong(Nat, Nat, z => Nat.add(z, T), Nat.add(r, Nat.mul(q, 16n)), n, en), Equal.cong(Nat, Nat, z => Nat.add(n, z), T, C.shift(8n, V), eT))))

# the table form over the 2^6 one rows of a point b, for 32 bytes: [value] b
def va_smulb(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +b: SE.EPt, +q: G.APt, +hb: VA(mp, d, b, q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}) -> VA(mp, d, FB.sfb(1n+mp, d, FB.stab(C.shift(6n, one), 1n+mp, d, b), PT.nibs(bs), SE.identity()), G.nmul(1n+mp, d, FS.value(bs), q)):
  +P = {1n+mp : Nat}
  +n0 = C.shift(6n, one)
  +ds = PT.nibs(bs)
  +g = va_fb(mp, d, hc, n0, b, q, hb, ds, PFB.nibs_ok(bs, CV.nat_below(32n, bs, hs)), SE.identity(), G.azero(), va_id(mp, d, hc))
  +ev = Equal.trans(Nat, dval(n0, ds), dval(dn(32n), ds), FS.value(bs), Equal.cong(Nat, Nat, z => dval(C.shift(6n, z), ds), one, 1n, h1), dval_nibs(32n, bs, hs))
  +X = G.nmul(P, d, FS.value(bs), q)
  +hX = GP.nmul_on(mp, d, hc, FS.value(bs), q, vO(mp, d, b, q, hb))
  va_cast(mp, d, FB.sfb(P, d, FB.stab(n0, P, d, b), ds, SE.identity()), G.aadd(P, d, G.azero(), G.nmul(P, d, dval(n0, ds), q)), X, Equal.trans(G.APt, G.aadd(P, d, G.azero(), G.nmul(P, d, dval(n0, ds), q)), G.aadd(P, d, G.azero(), X), X, Equal.cong(Nat, G.APt, z => G.aadd(P, d, G.azero(), G.nmul(P, d, z, q)), dval(n0, ds), FS.value(bs), ev), GP.add_zero_l(mp, d, hc, X, hX)), g)

# ---- the specification's double-and-add (group/smul.bend) ----

# the specification's [value(bs)] a for 32 bytes: [value] a in the group
def va_mul(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}) -> VA(mp, d, SE.mul(one, 1n+mp, d, FS.value(bs), a), G.nmul(1n+mp, d, FS.value(bs), q)):
  +P = {1n+mp : Nat}
  +k = FS.value(bs)
  +va = vV(mp, d, a, q, ha)
  +hfit = L.subst(Nat, z => {C.fits(C.shift(8n, z), k) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WI.fits_one(256n, one, h1, k, BF.val_lt(one, h1, 32n, bs, LM.bytes_okb(32n, bs, hs))))
  va_mk(mp, d, hc, SE.mul(one, P, d, k, a), G.nmul(P, d, k, q), SM.mul_valid(one, mp, d, hc, k, a, va), Equal.trans(G.APt, EG.affine(P, SE.mul(one, P, d, k, a)), G.nmul(P, d, k, EG.affine(P, a)), G.nmul(P, d, k, q), SM.mul_aff_fit(one, mp, d, hc, k, a, va, hfit), Equal.cong(G.APt, G.APt, z => G.nmul(P, d, k, z), EG.affine(P, a), q, vE(mp, d, a, q, ha))))
