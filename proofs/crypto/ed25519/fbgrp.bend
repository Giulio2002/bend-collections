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
import ./gext.bend as GX
import ./pfb.bend as PFB
import ./fbspec.bend as FB
import ../../../spec/crypto/curve25519/x25519.bend as SX
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
  (hv, (he, L.subst(G.APt, z => G.OnCurve(1n+mp, d, z), EG.affine(1n+mp, a), q, he, GX.valid_on(mp, d, hc, a, hv))))

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

# ---- the specification's double-and-add ----

# the top bit of the low 1 + t bits
def low_top(+t: Nat, +k: Nat) -> {C.low(1n+t, k) == Nat.add(C.low(t, k), C.shift(t, C.bit(C.high(t, k)))) : Nat}:
  match t:
    case 0n:
      Equal.trans(Nat, Nat.add(C.bit(k), 0n), C.bit(k), Nat.add(0n, C.bit(k)), N.add_zero(C.bit(k)), {==})
    case 1n+ +s:
      +hk = C.half(k)
      +A = C.low(s, hk)
      +B = C.shift(s, C.bit(C.high(s, hk)))
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(C.bit(k), Nat.double(z)), C.low(1n+s, hk), Nat.add(A, B), low_top(s, hk))
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(C.bit(k), z), Nat.double(Nat.add(A, B)), Nat.add(Nat.double(A), Nat.double(B)), Equal.sym(Nat, Nat.add(Nat.double(A), Nat.double(B)), Nat.double(Nat.add(A, B)), N.add_double(A, B)))
      +e3 = Equal.sym(Nat, Nat.add(Nat.add(C.bit(k), Nat.double(A)), Nat.double(B)), Nat.add(C.bit(k), Nat.add(Nat.double(A), Nat.double(B))), N.add_assoc(C.bit(k), Nat.double(A), Nat.double(B)))
      Equal.trans(Nat, Nat.add(C.bit(k), Nat.double(C.low(1n+s, hk))), Nat.add(C.bit(k), Nat.double(Nat.add(A, B))), Nat.add(Nat.add(C.bit(k), Nat.double(A)), Nat.double(B)), e1, Equal.trans(Nat, Nat.add(C.bit(k), Nat.double(Nat.add(A, B))), Nat.add(C.bit(k), Nat.add(Nat.double(A), Nat.double(B))), Nat.add(Nat.add(C.bit(k), Nat.double(A)), Nat.double(B)), e2, e3))

# x 2 == 2 x
def mul_two(+x: Nat) -> {Nat.mul(x, 2n) == Nat.double(x) : Nat}:
  Equal.trans(Nat, Nat.mul(x, 2n), Nat.double(Nat.mul(x, 1n)), Nat.double(x), Equal.sym(Nat, Nat.double(Nat.mul(x, 1n)), Nat.mul(x, 2n), WI.dbl_mul(x, 1n)), Equal.cong(Nat, Nat, z => Nat.double(z), Nat.mul(x, 1n), x, NA.mul_one(x)))

# 2^t b + low(t, k) == low(1 + t, k) for the bit b at t
def low_step(+t: Nat, +k: Nat) -> {Nat.add(Nat.mul(C.pow2(t), SX.kbit(k, t)), C.low(t, k)) == C.low(1n+t, k) : Nat}:
  +b = SX.kbit(k, t)
  +e1 = Equal.trans(Nat, Nat.mul(C.pow2(t), b), Nat.mul(b, C.pow2(t)), C.shift(t, b), NA.mul_comm(C.pow2(t), b), Equal.sym(Nat, C.shift(t, b), Nat.mul(b, C.pow2(t)), Equal.trans(Nat, C.shift(t, b), Nat.mul(b, C.shift(t, 1n)), Nat.mul(b, C.pow2(t)), WI.shift_mul(t, b), Equal.cong(Nat, Nat, z => Nat.mul(b, z), C.shift(t, 1n), C.pow2(t), WI.shift_one(t)))))
  Equal.trans(Nat, Nat.add(Nat.mul(C.pow2(t), b), C.low(t, k)), Nat.add(C.shift(t, b), C.low(t, k)), C.low(1n+t, k), Equal.cong(Nat, Nat, z => Nat.add(z, C.low(t, k)), Nat.mul(C.pow2(t), b), C.shift(t, b), e1), Equal.trans(Nat, Nat.add(C.shift(t, b), C.low(t, k)), Nat.add(C.low(t, k), C.shift(t, b)), C.low(1n+t, k), NA.add_comm(C.shift(t, b), C.low(t, k)), Equal.sym(Nat, C.low(1n+t, k), Nat.add(C.low(t, k), C.shift(t, b)), low_top(t, k))))

# one step of the loop: q2 on a zero bit, q2 + a on a one bit
def va_pick(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +b: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +q2: SE.EPt, +a: SE.EPt, +Q2: G.APt, +q: G.APt, +h2: VA(mp, d, q2, Q2), +ha: VA(mp, d, a, q)) -> VA(mp, d, SE.pick(b, q2, SE.add(1n+mp, d, q2, a)), G.aadd(1n+mp, d, Q2, G.nmul(1n+mp, d, b, q))):
  match b:
    case 0n:
      va_cast(mp, d, q2, Q2, G.aadd(1n+mp, d, Q2, G.azero()), Equal.sym(G.APt, G.aadd(1n+mp, d, Q2, G.azero()), Q2, GP.add_zero_r(mp, d, hc, Q2, vO(mp, d, q2, Q2, h2))), h2)
    case 1n+ +c:
      match c:
        case 0n:
          va_cast(mp, d, SE.add(1n+mp, d, q2, a), G.aadd(1n+mp, d, Q2, q), G.aadd(1n+mp, d, Q2, G.aadd(1n+mp, d, q, G.azero())), Equal.cong(G.APt, G.APt, z => G.aadd(1n+mp, d, Q2, z), q, G.aadd(1n+mp, d, q, G.azero()), Equal.sym(G.APt, G.aadd(1n+mp, d, q, G.azero()), q, GP.add_zero_r(mp, d, hc, q, vO(mp, d, a, q, ha)))), va_add(mp, d, hc, q2, a, Q2, q, h2, ha))
        case 1n+e:
          Empty.absurd(VA(mp, d, SE.pick(2n+e, q2, SE.add(1n+mp, d, q2, a)), G.aadd(1n+mp, d, Q2, G.nmul(1n+mp, d, 2n+e, q))), L.false_true(hb))

# the loop over the low n bits of k, from acc: [2^n] acc + [low n bits of k] a
def va_smul(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +n: Nat, +k: Nat, +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +acc: SE.EPt, +qacc: G.APt, +hacc: VA(mp, d, acc, qacc)) -> VA(mp, d, SE.smul(1n+mp, d, n, k, a, acc), G.aadd(1n+mp, d, G.nmul(1n+mp, d, C.pow2(n), qacc), G.nmul(1n+mp, d, C.low(n, k), q))):
  match n:
    case 0n:
      +P = {1n+mp : Nat}
      +ho = vO(mp, d, acc, qacc, hacc)
      +e1 = GP.add_zero_r(mp, d, hc, qacc, ho)
      va_cast(mp, d, acc, qacc, G.aadd(P, d, G.aadd(P, d, qacc, G.azero()), G.azero()), Equal.sym(G.APt, G.aadd(P, d, G.aadd(P, d, qacc, G.azero()), G.azero()), qacc, Equal.trans(G.APt, G.aadd(P, d, G.aadd(P, d, qacc, G.azero()), G.azero()), G.aadd(P, d, qacc, G.azero()), qacc, Equal.cong(G.APt, G.APt, z => G.aadd(P, d, z, G.azero()), G.aadd(P, d, qacc, G.azero()), qacc, e1), e1)), hacc)
    case 1n+ +t:
      +P = {1n+mp : Nat}
      +hq = vO(mp, d, a, q, ha)
      +ho = vO(mp, d, acc, qacc, hacc)
      +b = SX.kbit(k, t)
      +q2 = SE.double(P, acc)
      +Q2 = G.nmul(P, d, 2n, qacc)
      +h2 = va_dbl(mp, d, hc, acc, qacc, hacc)
      +nx = SE.pick(b, q2, SE.add(P, d, q2, a))
      +Bq = G.nmul(P, d, b, q)
      +QN = G.aadd(P, d, Q2, Bq)
      +hn = va_pick(mp, d, hc, b, WI.bit_le1(C.high(t, k)), q2, a, Q2, q, h2, ha)
      +ih = va_smul(mp, d, hc, t, k, a, q, ha, nx, QN, hn)
      +pt = C.pow2(t)
      +Lq = G.nmul(P, d, C.low(t, k), q)
      +hQ2 = GP.nmul_on(mp, d, hc, 2n, qacc, ho)
      +hBq = GP.nmul_on(mp, d, hc, b, q, hq)
      +X1 = G.nmul(P, d, Nat.double(pt), qacc)
      +X2 = G.nmul(P, d, Nat.mul(pt, b), q)
      +e1 = GP.nmul_dist(mp, d, hc, pt, Q2, Bq, hQ2, hBq)
      +e2 = Equal.trans(G.APt, G.nmul(P, d, pt, Q2), G.nmul(P, d, Nat.mul(pt, 2n), qacc), X1, Equal.sym(G.APt, G.nmul(P, d, Nat.mul(pt, 2n), qacc), G.nmul(P, d, pt, Q2), GP.nmul_mul(mp, d, hc, pt, 2n, qacc, ho)), Equal.cong(Nat, G.APt, z => G.nmul(P, d, z, qacc), Nat.mul(pt, 2n), Nat.double(pt), mul_two(pt)))
      +e3 = Equal.sym(G.APt, X2, G.nmul(P, d, pt, Bq), GP.nmul_mul(mp, d, hc, pt, b, q, hq))
      +e4 = Equal.trans(G.APt, G.nmul(P, d, pt, QN), G.aadd(P, d, G.nmul(P, d, pt, Q2), G.nmul(P, d, pt, Bq)), G.aadd(P, d, X1, X2), e1, aadd2(mp, d, G.nmul(P, d, pt, Q2), X1, G.nmul(P, d, pt, Bq), X2, e2, e3))
      +e5 = GP.add_assoc(mp, d, hc, X1, X2, Lq, GP.nmul_on(mp, d, hc, Nat.double(pt), qacc, ho), GP.nmul_on(mp, d, hc, Nat.mul(pt, b), q, hq), GP.nmul_on(mp, d, hc, C.low(t, k), q, hq))
      +e6 = Equal.trans(G.APt, G.aadd(P, d, X2, Lq), G.nmul(P, d, Nat.add(Nat.mul(pt, b), C.low(t, k)), q), G.nmul(P, d, C.low(1n+t, k), q), Equal.sym(G.APt, G.nmul(P, d, Nat.add(Nat.mul(pt, b), C.low(t, k)), q), G.aadd(P, d, X2, Lq), GP.nmul_add(mp, d, hc, Nat.mul(pt, b), C.low(t, k), q, hq)), Equal.cong(Nat, G.APt, z => G.nmul(P, d, z, q), Nat.add(Nat.mul(pt, b), C.low(t, k)), C.low(1n+t, k), low_step(t, k)))
      +G0 = G.aadd(P, d, G.nmul(P, d, pt, QN), Lq)
      +G1 = G.aadd(P, d, G.aadd(P, d, X1, X2), Lq)
      +G2 = G.aadd(P, d, X1, G.aadd(P, d, X2, Lq))
      +G3 = G.aadd(P, d, X1, G.nmul(P, d, C.low(1n+t, k), q))
      va_cast(mp, d, SE.smul(P, d, t, k, a, nx), G0, G3, Equal.trans(G.APt, G0, G1, G3, Equal.cong(G.APt, G.APt, z => G.aadd(P, d, z, Lq), G.nmul(P, d, pt, QN), G.aadd(P, d, X1, X2), e4), Equal.trans(G.APt, G1, G2, G3, e5, Equal.cong(G.APt, G.APt, z => G.aadd(P, d, X1, z), G.aadd(P, d, X2, Lq), G.nmul(P, d, C.low(1n+t, k), q), e6))), ih)

# the specification's [value(bs)] a for 32 bytes: [value] a in the group
def va_mul(+one: Nat, +h1: {one == 1n : Nat}, +mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +q: G.APt, +ha: VA(mp, d, a, q), +bs: List<&2, U32>, +hs: {FS.bytes_ok(32n, bs) == True{} : Bool}) -> VA(mp, d, SE.mul(one, 1n+mp, d, FS.value(bs), a), G.nmul(1n+mp, d, FS.value(bs), q)):
  +P = {1n+mp : Nat}
  +k = FS.value(bs)
  +n0 = C.shift(8n, one)
  +g = va_smul(mp, d, hc, n0, k, a, q, ha, SE.identity(), G.azero(), va_id(mp, d, hc))
  +hfit = L.subst(Nat, z => {C.fits(C.shift(8n, z), k) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WI.fits_one(256n, one, h1, k, BF.val_lt(one, h1, 32n, bs, LM.bytes_okb(32n, bs, hs))))
  +X = G.nmul(P, d, k, q)
  +hX = GP.nmul_on(mp, d, hc, k, q, vO(mp, d, a, q, ha))
  +e1 = aadd2(mp, d, G.nmul(P, d, C.pow2(n0), G.azero()), G.azero(), G.nmul(P, d, C.low(n0, k), q), X, GP.nmul_zero(mp, d, hc, C.pow2(n0)), Equal.cong(Nat, G.APt, z => G.nmul(P, d, z, q), C.low(n0, k), k, WI.low_fit(n0, k, hfit)))
  va_cast(mp, d, SE.smul(P, d, n0, k, a, SE.identity()), G.aadd(P, d, G.nmul(P, d, C.pow2(n0), G.azero()), G.nmul(P, d, C.low(n0, k), q)), X, Equal.trans(G.APt, G.aadd(P, d, G.nmul(P, d, C.pow2(n0), G.azero()), G.nmul(P, d, C.low(n0, k), q)), G.aadd(P, d, G.azero(), X), X, e1, GP.add_zero_l(mp, d, hc, X, hX)), g)
