import Base
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ./pw.bend as PW
import ./nl.bend as NL
import ./prod.bend as PD

# The field's squaring (src/crypto/curve25519/limbs.bend sqp: each cross
# product once, the other factor doubled) is the schoolbook product of a
# limb list with itself, conv(xs, xs), limb for limb: by list algebra
# (addl is associative and commutative, conv(xs, y :: ys) is
# xs y + R conv(xs, ys)) and, for limbs below 2^19, pm(a, b) == a b with
# b below 2^20.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def ltr(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +e1: {a == b : List<&2, Nat>}, +e2: {b == c : List<&2, Nat>}) -> {a == c : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, a, b, c, e1, e2)

def lsy(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: {a == b : List<&2, Nat>}) -> {b == a : List<&2, Nat>}:
  Equal.sym(List<&2, Nat>, a, b, e)

# Con{h, t} == Con{h2, t2} from h == h2, t == t2
def con_eq(+h: Nat, +h2: Nat, +t: List<&2, Nat>, +t2: List<&2, Nat>, +eh: {h == h2 : Nat}, +et: {t == t2 : List<&2, Nat>}) -> {Con{h, t} == Con{h2, t2} : List<&2, Nat>}:
  ltr(Con{h, t}, Con{h2, t}, Con{h2, t2}, Equal.cong(Nat, List<&2, Nat>, z => Con{z, t}, h, h2, eh), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{h2, z}, t, t2, et))

# ---- addl ----

def addl_nil_r(+xs: List<&2, Nat>) -> {LS.addl(xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def addl_comm(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {LS.addl(xs, ys) == LS.addl(ys, xs) : List<&2, Nat>}:
  match xs ys:
    case Nil{} _:
      lsy(LS.addl(ys, Nil{}), ys, addl_nil_r(ys))
    case Con{+x, +xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      con_eq(Nat.add(x, y), Nat.add(y, x), LS.addl(xt, yt), LS.addl(yt, xt), NA.add_comm(x, y), addl_comm(xt, yt))

def addl_assoc(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {LS.addl(LS.addl(xs, ys), zs) == LS.addl(xs, LS.addl(ys, zs)) : List<&2, Nat>}:
  match xs ys zs:
    case Nil{} _ _:
      {==}
    case Con{+x, +xt} Nil{} _:
      {==}
    case Con{+x, +xt} Con{+y, +yt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt} Con{+z, +zt}:
      con_eq(Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), LS.addl(LS.addl(xt, yt), zt), LS.addl(xt, LS.addl(yt, zt)), NA.add_assoc(x, y, z), addl_assoc(xt, yt, zt))

# addl(a, addl(b, c)) == addl(b, addl(a, c))
def addl_swap(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>) -> {LS.addl(a, LS.addl(b, c)) == LS.addl(b, LS.addl(a, c)) : List<&2, Nat>}:
  +e1 = lsy(LS.addl(LS.addl(a, b), c), LS.addl(a, LS.addl(b, c)), addl_assoc(a, b, c))
  +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.addl(z, c), LS.addl(a, b), LS.addl(b, a), addl_comm(a, b))
  ltr(LS.addl(a, LS.addl(b, c)), LS.addl(LS.addl(a, b), c), LS.addl(b, LS.addl(a, c)), e1, ltr(LS.addl(LS.addl(a, b), c), LS.addl(LS.addl(b, a), c), LS.addl(b, LS.addl(a, c)), e2, addl_assoc(b, a, c)))

# ---- conv by one limb ----

# conv(x :: [], ys) == x ys
def conv_one_l(+x: Nat, +ys: List<&2, Nat>) -> {LS.conv(Con{x, Nil{}}, ys) == LS.scal(x, ys) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{Nat.mul(x, y), z}, LS.addl(LS.scal(x, yt), Nil{}), LS.scal(x, yt), addl_nil_r(LS.scal(x, yt)))

# conv(x :: xt, ys) == x ys + R conv(xt, ys) (ys not empty)
def conv_cons_l(+x: Nat, +xt: List<&2, Nat>, +z: Nat, +zs: List<&2, Nat>) -> {LS.conv(Con{x, xt}, Con{z, zs}) == LS.addl(LS.scal(x, Con{z, zs}), Con{0n, LS.conv(xt, Con{z, zs})}) : List<&2, Nat>}:
  Equal.cong(Nat, List<&2, Nat>, h => Con{h, LS.addl(LS.scal(x, zs), LS.conv(xt, Con{z, zs}))}, Nat.mul(x, z), Nat.add(Nat.mul(x, z), 0n), sy(Nat.add(Nat.mul(x, z), 0n), Nat.mul(x, z), N.add_zero(Nat.mul(x, z))))

# conv(xs, y :: ys) == xs y + R conv(xs, ys) (xs not empty)
def conv_cons_r(+xt: List<&2, Nat>, +x: Nat, +y: Nat, +ys: List<&2, Nat>) -> {LS.conv(Con{x, xt}, Con{y, ys}) == LS.addl(LS.scal_r(Con{x, xt}, y), Con{0n, LS.conv(Con{x, xt}, ys)}) : List<&2, Nat>}:
  match xt ys:
    case Nil{} _:
      +hd = sy(Nat.add(Nat.mul(x, y), 0n), Nat.mul(x, y), N.add_zero(Nat.mul(x, y)))
      +e1 = ltr(LS.addl(LS.scal(x, ys), Nil{}), LS.scal(x, ys), LS.conv(Con{x, Nil{}}, ys), addl_nil_r(LS.scal(x, ys)), lsy(LS.conv(Con{x, Nil{}}, ys), LS.scal(x, ys), conv_one_l(x, ys)))
      con_eq(Nat.mul(x, y), Nat.add(Nat.mul(x, y), 0n), LS.addl(LS.scal(x, ys), Nil{}), LS.conv(Con{x, Nil{}}, ys), hd, e1)
    case Con{+x2, +xt2} Nil{}:
      +hd = sy(Nat.add(Nat.mul(x, y), 0n), Nat.mul(x, y), N.add_zero(Nat.mul(x, y)))
      +xt0 = {Con{x2, xt2} : List<&2, Nat>}
      +ih = conv_cons_r(xt2, x2, y, Nil{})
      +B = LS.scal_r(xt0, y)
      +c = LS.scal_r(xt2, y)
      +e2 = con_eq(Nat.add(Nat.mul(x2, y), 0n), Nat.mul(x2, y), LS.addl(c, Nil{}), c, N.add_zero(Nat.mul(x2, y)), addl_nil_r(c))
      +tl = ltr(LS.addl(Nil{}, LS.conv(xt0, Con{y, Nil{}})), LS.addl(Nil{}, LS.addl(B, Con{0n, Nil{}})), LS.addl(B, Nil{}), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.addl(Nil{}, z), LS.conv(xt0, Con{y, Nil{}}), LS.addl(B, Con{0n, Nil{}}), ih), ltr(LS.addl(B, Con{0n, Nil{}}), B, LS.addl(B, Nil{}), e2, lsy(LS.addl(B, Nil{}), B, addl_nil_r(B))))
      con_eq(Nat.mul(x, y), Nat.add(Nat.mul(x, y), 0n), LS.addl(Nil{}, LS.conv(xt0, Con{y, Nil{}})), LS.addl(B, Nil{}), hd, tl)
    case Con{+x2, +xt2} Con{+z, +zs}:
      +hd = sy(Nat.add(Nat.mul(x, y), 0n), Nat.mul(x, y), N.add_zero(Nat.mul(x, y)))
      +xt0 = {Con{x2, xt2} : List<&2, Nat>}
      +ys0 = {Con{z, zs} : List<&2, Nat>}
      +ih = conv_cons_r(xt2, x2, y, ys0)
      +B = LS.scal_r(xt0, y)
      +A0 = LS.scal(x, ys0)
      +D = LS.conv(xt0, ys0)
      +e3 = conv_cons_l(x, xt0, z, zs)
      +tl = ltr(LS.addl(A0, LS.conv(xt0, Con{y, ys0})), LS.addl(A0, LS.addl(B, Con{0n, D})), LS.addl(B, LS.conv(Con{x, xt0}, ys0)), Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(A0, w), LS.conv(xt0, Con{y, ys0}), LS.addl(B, Con{0n, D}), ih), ltr(LS.addl(A0, LS.addl(B, Con{0n, D})), LS.addl(B, LS.addl(A0, Con{0n, D})), LS.addl(B, LS.conv(Con{x, xt0}, ys0)), addl_swap(A0, B, Con{0n, D}), Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(B, w), LS.addl(A0, Con{0n, D}), LS.conv(Con{x, xt0}, ys0), lsy(LS.conv(Con{x, xt0}, ys0), LS.addl(A0, Con{0n, D}), e3))))
      con_eq(Nat.mul(x, y), Nat.add(Nat.mul(x, y), 0n), LS.addl(A0, LS.conv(xt0, Con{y, ys0})), LS.addl(B, LS.conv(Con{x, xt0}, ys0)), hd, tl)

# x t + t x == x (t + t), limbwise
def scal_dbl(+x: Nat, +ts: List<&2, Nat>) -> {LS.addl(LS.scal(x, ts), LS.scal_r(ts, x)) == LS.scal(x, LS.dbl(ts)) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +tt}:
      +e = tr(Nat.add(Nat.mul(x, t), Nat.mul(t, x)), Nat.add(Nat.mul(x, t), Nat.mul(x, t)), Nat.mul(x, Nat.add(t, t)), M.cong_r(Nat.mul(x, t), Nat.mul(t, x), Nat.mul(x, t), NA.mul_comm(t, x)), sy(Nat.mul(x, Nat.add(t, t)), Nat.add(Nat.mul(x, t), Nat.mul(x, t)), NA.mul_add_left(x, t, t)))
      con_eq(Nat.add(Nat.mul(x, t), Nat.mul(t, x)), Nat.mul(x, Nat.add(t, t)), LS.addl(LS.scal(x, tt), LS.scal_r(tt, x)), LS.scal(x, LS.dbl(tt)), e, scal_dbl(x, tt))

# ---- the square with Nat products ----

def sqc(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          Con{Nat.mul(x, x), Nil{}}
        case Con{+t0, +tt}:
          Con{Nat.mul(x, x), Con{Nat.mul(x, Nat.add(t0, t0)), LS.addl(LS.scal(x, LS.dbl(tt)), sqc(xt))}}

def sqc_conv(+xs: List<&2, Nat>) -> {sqc(xs) == LS.conv(xs, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          {==}
        case Con{+t0, +tt}:
          +xt0 = {Con{t0, tt} : List<&2, Nat>}
          +C = LS.conv(xt0, xt0)
          +ih = sqc_conv(xt0)
          +er = conv_cons_r(tt, t0, x, xt0)
          +hd = tr(Nat.mul(x, Nat.add(t0, t0)), Nat.add(Nat.mul(x, t0), Nat.mul(x, t0)), Nat.add(Nat.mul(x, t0), Nat.add(Nat.mul(t0, x), 0n)), NA.mul_add_left(x, t0, t0), M.cong_r(Nat.mul(x, t0), Nat.mul(x, t0), Nat.add(Nat.mul(t0, x), 0n), tr(Nat.mul(x, t0), Nat.mul(t0, x), Nat.add(Nat.mul(t0, x), 0n), NA.mul_comm(x, t0), sy(Nat.add(Nat.mul(t0, x), 0n), Nat.mul(t0, x), N.add_zero(Nat.mul(t0, x))))))
          +S1 = LS.scal(x, LS.dbl(tt))
          +A = LS.scal(x, tt)
          +B = LS.scal_r(tt, x)
          +t1 = Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(S1, w), sqc(xt0), C, ih)
          +t2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(w, C), S1, LS.addl(A, B), lsy(LS.addl(A, B), S1, scal_dbl(x, tt)))
          +tl = ltr(LS.addl(S1, sqc(xt0)), LS.addl(S1, C), LS.addl(A, LS.addl(B, C)), t1, ltr(LS.addl(S1, C), LS.addl(LS.addl(A, B), C), LS.addl(A, LS.addl(B, C)), t2, addl_assoc(A, B, C)))
          +e1 = con_eq(Nat.mul(x, Nat.add(t0, t0)), Nat.add(Nat.mul(x, t0), Nat.add(Nat.mul(t0, x), 0n)), LS.addl(S1, sqc(xt0)), LS.addl(A, LS.addl(B, C)), hd, tl)
          +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(LS.scal(x, xt0), w), LS.conv(xt0, Con{x, xt0}), LS.addl(LS.scal_r(xt0, x), Con{0n, C}), er)
          Equal.cong(List<&2, Nat>, List<&2, Nat>, w => Con{Nat.mul(x, x), w}, Con{Nat.mul(x, Nat.add(t0, t0)), LS.addl(S1, sqc(xt0))}, LS.addl(LS.scal(x, xt0), LS.conv(xt0, Con{x, xt0})), ltr(Con{Nat.mul(x, Nat.add(t0, t0)), LS.addl(S1, sqc(xt0))}, LS.addl(LS.scal(x, xt0), LS.addl(LS.scal_r(xt0, x), Con{0n, C})), LS.addl(LS.scal(x, xt0), LS.conv(xt0, Con{x, xt0})), e1, lsy(LS.addl(LS.scal(x, xt0), LS.conv(xt0, Con{x, xt0})), LS.addl(LS.scal(x, xt0), LS.addl(LS.scal_r(xt0, x), Con{0n, C})), e2)))

# ---- pm with the other factor below 2^20 ----

def hi_lt20(+one: Nat, +h1: {one == 1n : Nat}, +b: Nat, +hb: {Nat.is_lt(b, WD.sc(20n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(b, 512n), WD.sc(11n, one)) == True{} : Bool}:
  +E = WD.sc(11n, one)
  +e0 = NR.le_div(511n, E, b)
  +e20 = tr(Nat.mul(E, 512n), Nat.mul(E, WD.sc(9n, one)), WD.sc(20n, one), PD.mr(E, 512n, WD.sc(9n, one), sy(WD.sc(9n, one), 512n, PD.k512(one, h1))), PW.scsc(11n, 9n, one, h1))
  +nle = N.lt_not_le(b, Nat.mul(E, 512n), L.subst(Nat, z => {Nat.is_lt(b, z) == True{} : Bool}, WD.sc(20n, one), Nat.mul(E, 512n), sy(Nat.mul(E, 512n), WD.sc(20n, one), e20), hb))
  N.not_le_lt(E, Nat.div(b, 512n), Equal.trans(Bool, Nat.is_le(E, Nat.div(b, 512n)), Nat.is_le(Nat.mul(E, 512n), b), False{}, e0, nle))

def pm_eq20(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +b: Nat, +ha: {Nat.is_lt(a, WD.sc(19n, one)) == True{} : Bool}, +hb: {Nat.is_lt(b, WD.sc(20n, one)) == True{} : Bool}) -> {LS.pm(a, b) == Nat.mul(a, b) : Nat}:
  +lo = Nat.mod(b, 512n)
  +hi = Nat.div(b, 512n)
  +hlo = L.subst(Nat, z => {Nat.is_lt(lo, z) == True{} : Bool}, 512n, WD.sc(9n, one), sy(WD.sc(9n, one), 512n, PD.k512(one, h1)), NR.dm_lt(511n, b))
  +hhi = hi_lt20(one, h1, b, hb)
  +a32 = PD.lt32(one, h1, a, 19n, 12n, {==}, ha)
  +e1 = PD.pu_eq(one, h1, a, lo, a32, PD.lt32(one, h1, lo, 9n, 22n, {==}, hlo), PD.lt32(one, h1, Nat.mul(a, lo), 28n, 3n, {==}, PD.lt_prod(one, h1, a, lo, 19n, 9n, ha, hlo)))
  +e2 = PD.pu_eq(one, h1, a, hi, a32, PD.lt32(one, h1, hi, 11n, 20n, {==}, hhi), PD.lt32(one, h1, Nat.mul(a, hi), 30n, 1n, {==}, PD.lt_prod(one, h1, a, hi, 19n, 11n, ha, hhi)))
  +e3 = M.cong_add(LS.pu(a, lo), Nat.mul(a, lo), Nat.mul(LS.pu(a, hi), 512n), Nat.mul(Nat.mul(a, hi), 512n), e1, PD.ml(LS.pu(a, hi), Nat.mul(a, hi), 512n, e2))
  +eb = NR.dm_eq(511n, b)
  +e4 = tr(Nat.mul(a, b), Nat.mul(a, Nat.add(Nat.mul(hi, 512n), lo)), Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), PD.mr(a, b, Nat.add(Nat.mul(hi, 512n), lo), eb), NA.mul_add_left(a, Nat.mul(hi, 512n), lo))
  +e5 = tr(Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), Nat.add(Nat.mul(a, lo), Nat.mul(a, Nat.mul(hi, 512n))), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), NA.add_comm(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), M.cong_r(Nat.mul(a, lo), Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(Nat.mul(a, hi), 512n), sy(Nat.mul(Nat.mul(a, hi), 512n), Nat.mul(a, Nat.mul(hi, 512n)), NA.mul_assoc(a, hi, 512n))))
  tr(LS.pm(a, b), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), Nat.mul(a, b), e3, sy(Nat.mul(a, b), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), tr(Nat.mul(a, b), Nat.add(Nat.mul(a, Nat.mul(hi, 512n)), Nat.mul(a, lo)), Nat.add(Nat.mul(a, lo), Nat.mul(Nat.mul(a, hi), 512n)), e4, e5)))

# t + t < 2^20 for t < 2^19
def dbl_lt(+one: Nat, +t: Nat, +ht: {Nat.is_lt(t, WD.sc(19n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(t, t), WD.sc(20n, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(t, t), z) == True{} : Bool}, Nat.add(WD.sc(19n, one), WD.sc(19n, one)), WD.sc(20n, one), PW.dbl(19n, one), NL.lt_add2(t, t, WD.sc(19n, one), WD.sc(19n, one), ht, ht))

def scalp_dbl(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +ts: List<&2, Nat>, +ha: {Nat.is_lt(a, WD.sc(19n, one)) == True{} : Bool}, +ht: {FV.below(ts, WD.sc(19n, one)) == True{} : Bool}) -> {LS.scalp(a, LS.dbl(ts)) == LS.scal(a, LS.dbl(ts)) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +tt}:
      +s = WD.sc(19n, one)
      con_eq(LS.pm(a, Nat.add(t, t)), Nat.mul(a, Nat.add(t, t)), LS.scalp(a, LS.dbl(tt)), LS.scal(a, LS.dbl(tt)), pm_eq20(one, h1, a, Nat.add(t, t), ha, dbl_lt(one, t, NL.below_head(t, tt, s, ht))), scalp_dbl(one, h1, a, tt, ha, NL.below_tail(t, tt, s, ht)))

# sqp is sqc on limbs below 2^19
def sqp_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +hx: {FV.below(xs, WD.sc(19n, one)) == True{} : Bool}) -> {LS.sqp(xs) == sqc(xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          +s = WD.sc(19n, one)
          +hxh = NL.below_head(x, Nil{}, s, hx)
          Equal.cong(Nat, List<&2, Nat>, z => Con{z, Nil{}}, LS.pm(x, x), Nat.mul(x, x), PD.pm_eq(one, h1, x, x, hxh, hxh))
        case Con{+t0, +tt}:
          +s = WD.sc(19n, one)
          +xt0 = {Con{t0, tt} : List<&2, Nat>}
          +hxh = NL.below_head(x, xt0, s, hx)
          +hxt = NL.below_tail(x, xt0, s, hx)
          +ht0 = NL.below_head(t0, tt, s, hxt)
          +htt = NL.below_tail(t0, tt, s, hxt)
          +e1 = PD.pm_eq(one, h1, x, x, hxh, hxh)
          +e2 = pm_eq20(one, h1, x, Nat.add(t0, t0), hxh, dbl_lt(one, t0, ht0))
          +e3 = ltr(LS.addl(LS.scalp(x, LS.dbl(tt)), LS.sqp(xt0)), LS.addl(LS.scal(x, LS.dbl(tt)), LS.sqp(xt0)), LS.addl(LS.scal(x, LS.dbl(tt)), sqc(xt0)), Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(w, LS.sqp(xt0)), LS.scalp(x, LS.dbl(tt)), LS.scal(x, LS.dbl(tt)), scalp_dbl(one, h1, x, tt, hxh, htt)), Equal.cong(List<&2, Nat>, List<&2, Nat>, w => LS.addl(LS.scal(x, LS.dbl(tt)), w), LS.sqp(xt0), sqc(xt0), sqp_eq(one, h1, xt0, hxt)))
          con_eq(LS.pm(x, x), Nat.mul(x, x), Con{LS.pm(x, Nat.add(t0, t0)), LS.addl(LS.scalp(x, LS.dbl(tt)), LS.sqp(xt0))}, Con{Nat.mul(x, Nat.add(t0, t0)), LS.addl(LS.scal(x, LS.dbl(tt)), sqc(xt0))}, e1, con_eq(LS.pm(x, Nat.add(t0, t0)), Nat.mul(x, Nat.add(t0, t0)), LS.addl(LS.scalp(x, LS.dbl(tt)), LS.sqp(xt0)), LS.addl(LS.scal(x, LS.dbl(tt)), sqc(xt0)), e2, e3))

# sqp(xs) == conv(xs, xs) on limbs below 2^19
def sqp_conv(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +hx: {FV.below(xs, WD.sc(19n, one)) == True{} : Bool}) -> {LS.sqp(xs) == LS.conv(xs, xs) : List<&2, Nat>}:
  ltr(LS.sqp(xs), sqc(xs), LS.conv(xs, xs), sqp_eq(one, h1, xs, hx), sqc_conv(xs))
