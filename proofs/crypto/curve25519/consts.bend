import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./num.bend as M
import ./limbs.bend as LM
import ./poly.bend as PL

# Constant limb lists. The checker keeps closed naturals in unary, so the
# value of a constant such as 8p is never formed: every constant is read
# through valo(one, xs) = one * value(xs), which stays open in the symbolic
# one, and the carries of its digits are proved once, symbolically.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the value of xs times one, digit by digit
def valo(+one: Nat, xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(Nat.mul(one, U32.to_nat(h)), C.shift(8n, valo(one, t)))

def valo_value(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {valo(one, xs) == FS.value(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +e0 = L.subst(Nat, o => {Nat.mul(o, v(h)) == v(h) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), AR.one_mul(v(h)))
      M.cong_add(Nat.mul(one, v(h)), v(h), C.shift(8n, valo(one, t)), C.shift(8n, FS.value(t)), e0, M.cong_sc(8n, valo(one, t), FS.value(t), valo_value(one, h1, t)))

# n copies of k, then tl
def rep(n: Nat, +k: U32, tl: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      tl
    case 1n+m:
      Con{k, rep(m, k, tl)}

# a run of 2040 = 8 * 255 absorbs a carry of 8
def run8(+one: Nat, +n: Nat, +tl: List<&2, U32>) -> {Nat.add(valo(one, rep(n, 2040, tl)), Nat.mul(one, 8n)) == LM.shn(n, Nat.add(valo(one, tl), Nat.mul(one, 8n))) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +R = valo(one, rep(m, 2040, tl))
      +a = Nat.mul(one, v(2040))
      +b = Nat.mul(one, 8n)
      +k1 = Equal.trans(Nat, Nat.add(a, b), Nat.mul(one, Nat.add(v(2040), 8n)), Nat.mul(one, WD.sc(8n, 8n)), Equal.sym(Nat, Nat.mul(one, Nat.add(v(2040), 8n)), Nat.add(a, b), NA.mul_add_left(one, v(2040), 8n)), Equal.cong(Nat, Nat, t => Nat.mul(one, t), Nat.add(v(2040), 8n), WD.sc(8n, 8n), {==}))
      +k2 = Equal.trans(Nat, Nat.add(a, b), Nat.mul(one, WD.sc(8n, 8n)), WD.sc(8n, b), k1, Equal.sym(Nat, WD.sc(8n, b), Nat.mul(one, WD.sc(8n, 8n)), PL.sc_mul_l(8n, one, 8n)))
      +e1 = Equal.trans(Nat, Nat.add(Nat.add(a, C.shift(8n, R)), b), Nat.add(a, Nat.add(C.shift(8n, R), b)), Nat.add(Nat.add(a, b), C.shift(8n, R)), NA.add_assoc(a, C.shift(8n, R), b),
        Equal.trans(Nat, Nat.add(a, Nat.add(C.shift(8n, R), b)), Nat.add(a, Nat.add(b, C.shift(8n, R))), Nat.add(Nat.add(a, b), C.shift(8n, R)), M.cong_r(a, Nat.add(C.shift(8n, R), b), Nat.add(b, C.shift(8n, R)), NA.add_comm(C.shift(8n, R), b)), Equal.sym(Nat, Nat.add(Nat.add(a, b), C.shift(8n, R)), Nat.add(a, Nat.add(b, C.shift(8n, R))), NA.add_assoc(a, b, C.shift(8n, R)))))
      +e2 = M.cong_l(Nat.add(a, b), WD.sc(8n, b), C.shift(8n, R), k2)
      +e3 = Equal.trans(Nat, Nat.add(WD.sc(8n, b), C.shift(8n, R)), WD.sc(8n, Nat.add(b, R)), WD.sc(8n, Nat.add(R, b)), M.sc_add(8n, b, R), M.cong_sc(8n, Nat.add(b, R), Nat.add(R, b), NA.add_comm(b, R)))
      +e4 = M.cong_sc(8n, Nat.add(R, b), LM.shn(m, Nat.add(valo(one, tl), b)), run8(one, m, tl))
      Equal.trans(Nat, Nat.add(Nat.add(a, C.shift(8n, R)), b), Nat.add(Nat.add(a, b), C.shift(8n, R)), C.shift(8n, LM.shn(m, Nat.add(valo(one, tl), b))), e1,
        Equal.trans(Nat, Nat.add(Nat.add(a, b), C.shift(8n, R)), Nat.add(WD.sc(8n, b), C.shift(8n, R)), C.shift(8n, LM.shn(m, Nat.add(valo(one, tl), b))), e2,
          Equal.trans(Nat, Nat.add(WD.sc(8n, b), C.shift(8n, R)), WD.sc(8n, Nat.add(R, b)), C.shift(8n, LM.shn(m, Nat.add(valo(one, tl), b))), e3, e4)))

# a run of zeros shifts
def run0(+one: Nat, +n: Nat, +tl: List<&2, U32>) -> {valo(one, rep(n, 0, tl)) == LM.shn(n, valo(one, tl)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +R = valo(one, rep(m, 0, tl))
      +e1 = M.cong_l(Nat.mul(one, 0n), 0n, C.shift(8n, R), NA.mul_zero(one))
      Equal.trans(Nat, Nat.add(Nat.mul(one, 0n), C.shift(8n, R)), C.shift(8n, R), C.shift(8n, LM.shn(m, valo(one, tl))), e1, M.cong_sc(8n, R, LM.shn(m, valo(one, tl)), run0(one, m, tl)))

def one_k(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.mul(one, k) == k : Nat}:
  L.subst(Nat, o => {Nat.mul(o, k) == k : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), AR.one_mul(k))

# 2^258 == 8 p + 152
def s258(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {WD.sc(258n, one) == Nat.add(Nat.mul(8n, 1n+pp), 152n) : Nat}:
  +X = WD.sc(255n, one)
  +P = {1n+pp : Nat}
  +e1 = Equal.trans(Nat, WD.sc(3n, X), Nat.mul(X, 8n), Nat.mul(8n, X), Equal.sym(Nat, Nat.mul(X, 8n), WD.sc(3n, X), AR.mul_sc(3n, X)), NA.mul_comm(X, 8n))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mul(8n, t), X, Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), X, hP))
  +e3 = NA.mul_add_left(8n, P, 19n)
  Equal.trans(Nat, WD.sc(3n, X), Nat.mul(8n, X), Nat.add(Nat.mul(8n, P), 152n), e1, Equal.trans(Nat, Nat.mul(8n, X), Nat.mul(8n, Nat.add(P, 19n)), Nat.add(Nat.mul(8n, P), 152n), e2, e3))

def eight_p_shape() -> {F.eight_p() == Con{1896, rep(30n, 2040, Con{1016, Nil{}})} : List<&2, U32>}:
  {==}

# value(8p limbs) == 8 p
def eight_p_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {valo(one, F.eight_p()) == Nat.mul(8n, 1n+pp) : Nat}:
  %Equal.sym(List<&2, U32>, F.eight_p(), Con{1896, rep(30n, 2040, Con{1016, Nil{}})}, eight_p_shape()) : {valo(one, _) == Nat.mul(8n, 1n+pp) : Nat}
  +R = valo(one, rep(30n, 2040, Con{1016, Nil{}}))
  +a = Nat.mul(one, v(1896))
  +b = Nat.mul(one, 152n)
  +c8 = Nat.mul(one, 8n)
  +t = Nat.add(valo(one, Con{1016, Nil{}}), c8)
  +k1 = Equal.trans(Nat, Nat.add(a, b), Nat.mul(one, Nat.add(v(1896), 152n)), Nat.mul(one, WD.sc(8n, 8n)), Equal.sym(Nat, Nat.mul(one, Nat.add(v(1896), 152n)), Nat.add(a, b), NA.mul_add_left(one, v(1896), 152n)), Equal.cong(Nat, Nat, z => Nat.mul(one, z), Nat.add(v(1896), 152n), WD.sc(8n, 8n), {==}))
  +k2 = Equal.trans(Nat, Nat.add(a, b), Nat.mul(one, WD.sc(8n, 8n)), WD.sc(8n, c8), k1, Equal.sym(Nat, WD.sc(8n, c8), Nat.mul(one, WD.sc(8n, 8n)), PL.sc_mul_l(8n, one, 8n)))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(a, C.shift(8n, R)), b), Nat.add(a, Nat.add(C.shift(8n, R), b)), Nat.add(Nat.add(a, b), C.shift(8n, R)), NA.add_assoc(a, C.shift(8n, R), b),
    Equal.trans(Nat, Nat.add(a, Nat.add(C.shift(8n, R), b)), Nat.add(a, Nat.add(b, C.shift(8n, R))), Nat.add(Nat.add(a, b), C.shift(8n, R)), M.cong_r(a, Nat.add(C.shift(8n, R), b), Nat.add(b, C.shift(8n, R)), NA.add_comm(C.shift(8n, R), b)), Equal.sym(Nat, Nat.add(Nat.add(a, b), C.shift(8n, R)), Nat.add(a, Nat.add(b, C.shift(8n, R))), NA.add_assoc(a, b, C.shift(8n, R)))))
  +e2 = M.cong_l(Nat.add(a, b), WD.sc(8n, c8), C.shift(8n, R), k2)
  +e3 = Equal.trans(Nat, Nat.add(WD.sc(8n, c8), C.shift(8n, R)), WD.sc(8n, Nat.add(c8, R)), WD.sc(8n, Nat.add(R, c8)), M.sc_add(8n, c8, R), M.cong_sc(8n, Nat.add(c8, R), Nat.add(R, c8), NA.add_comm(c8, R)))
  +e4 = M.cong_sc(8n, Nat.add(R, c8), LM.shn(30n, t), run8(one, 30n, Con{1016, Nil{}}))
  +k3 = Equal.trans(Nat, t, Nat.add(Nat.mul(one, v(1016)), c8), Nat.mul(one, Nat.add(v(1016), 8n)), M.cong_l(valo(one, Con{1016, Nil{}}), Nat.mul(one, v(1016)), c8, N.add_zero(Nat.mul(one, v(1016)))), Equal.sym(Nat, Nat.mul(one, Nat.add(v(1016), 8n)), Nat.add(Nat.mul(one, v(1016)), c8), NA.mul_add_left(one, v(1016), 8n)))
  +k4 = L.subst(Nat, o => {Nat.mul(o, Nat.add(v(1016), 8n)) == WD.sc(10n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +e5 = M.cong_sc(8n, LM.shn(30n, t), LM.shn(30n, WD.sc(10n, one)), Equal.cong(Nat, Nat, z => LM.shn(30n, z), t, WD.sc(10n, one), Equal.trans(Nat, t, Nat.mul(one, Nat.add(v(1016), 8n)), WD.sc(10n, one), k3, k4)))
  +tot = Equal.trans(Nat, Nat.add(Nat.add(a, C.shift(8n, R)), b), Nat.add(Nat.add(a, b), C.shift(8n, R)), WD.sc(258n, one), e1,
    Equal.trans(Nat, Nat.add(Nat.add(a, b), C.shift(8n, R)), Nat.add(WD.sc(8n, c8), C.shift(8n, R)), WD.sc(258n, one), e2,
      Equal.trans(Nat, Nat.add(WD.sc(8n, c8), C.shift(8n, R)), WD.sc(8n, Nat.add(R, c8)), WD.sc(258n, one), e3,
        Equal.trans(Nat, WD.sc(8n, Nat.add(R, c8)), C.shift(8n, LM.shn(30n, t)), WD.sc(258n, one), e4, e5))))
  +V = valo(one, Con{1896, rep(30n, 2040, Con{1016, Nil{}})})
  +tot2 = Equal.trans(Nat, Nat.add(V, 152n), Nat.add(V, b), Nat.add(Nat.mul(8n, 1n+pp), 152n), M.cong_r(V, 152n, b, Equal.sym(Nat, b, 152n, one_k(one, h1, 152n))), Equal.trans(Nat, Nat.add(V, b), WD.sc(258n, one), Nat.add(Nat.mul(8n, 1n+pp), 152n), tot, s258(one, h1, pp, hP)))
  +tot3 = Equal.trans(Nat, Nat.add(152n, V), Nat.add(V, 152n), Nat.add(152n, Nat.mul(8n, 1n+pp)), NA.add_comm(152n, V), Equal.trans(Nat, Nat.add(V, 152n), Nat.add(Nat.mul(8n, 1n+pp), 152n), Nat.add(152n, Nat.mul(8n, 1n+pp)), tot2, NA.add_comm(Nat.mul(8n, 1n+pp), 152n)))
  NR.add_cancel(152n, V, Nat.mul(8n, 1n+pp), tot3)

# valo guarded on one: kept folded by the checker (see FS.gdigits)
def vg(+one: Nat, xs: List<&2, U32>) -> Nat:
  match one:
    case 0n:
      0n
    case 1n+z:
      valo(1n+z, xs)

def vg_valo(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {vg(one, xs) == valo(one, xs) : Nat}:
  L.subst(Nat, o => {vg(o, xs) == valo(o, xs) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
