import Base
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./pw.bend as PW
import ./ops.bend as OP

# The public-exponent powers of src/crypto/curve25519/fe.bend (the same
# chains as field.bend's, proofs/crypto/curve25519/pow.bend, over the fast
# field): p250(x) = x^(2^250 - 1) by ref10's addition chain (sqn, cat;
# 249 squarings, 10 multiplications) and pow_bits (square, multiply on a
# one bit), hence inv(x) = x^(p - 2) and pow_p58(x) = x^((p - 5) / 8),
# mod p.

def one_k(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.mul(one, k) == k : Nat}:
  L.subst(Nat, o => {Nat.mul(o, k) == k : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), AR.one_mul(k))

def sq_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.ok(one, FE.sq(R, a)) == True{} : Bool}:
  OP.mul_ok(one, h1, R, hR, a, a, ha, ha)

# 2^n - 1
def Fo(+one: Nat, +n: Nat) -> Nat:
  Nat.sub(WD.sc(n, one), one)

def one_le_sc(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.is_le(one, WD.sc(n, one)) == True{} : Bool}:
  +a = N.lt_succ_le_succ(0n, WD.sc(n, one), PW.sc_pos(n, one, h1))
  L.subst(Nat, o => {Nat.is_le(o, WD.sc(n, one)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), a)

def fo_sum(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.add(Fo(one, n), one) == WD.sc(n, one) : Nat}:
  Equal.trans(Nat, Nat.add(Fo(one, n), one), Nat.add(one, Fo(one, n)), WD.sc(n, one), NA.add_comm(Fo(one, n), one), N.sub_add(WD.sc(n, one), one, one_le_sc(one, h1, n)))

def bexp(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def blen(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, bt}:
      1n+blen(bt)

# the exponent of x contributed by the bits
def eb(+one: Nat, bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, +bt}:
      Nat.add(Nat.mul(bexp(b), WD.sc(blen(bt), one)), eb(one, bt))

# ---- unfolding (the loops inspect x first) ----

def pbs_nil(+R: Nat, +x: FE.Fe, +acc: FE.Fe) -> {FE.pow_bits(R, x, Nil{}, acc) == acc : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def pbs_con(+R: Nat, +x: FE.Fe, +b: Bool, +bt: List<&2, Bool>, +acc: FE.Fe) -> {FE.pow_bits(R, x, Con{b, bt}, acc) == FE.pow_bits(R, x, bt, FE.pow_bit(R, b, x, acc)) : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

# ---- shapes ----

def pb_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +b: Bool, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> {FV.ok(one, FE.pow_bit(R, b, x, acc)) == True{} : Bool}:
  match b:
    case True{}:
      OP.mul_ok(one, h1, R, hR, FE.sq(R, acc), x, sq_ok(one, h1, R, hR, acc, ha), hx)
    case False{}:
      sq_ok(one, h1, R, hR, acc, ha)

def pbs_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +bs: List<&2, Bool>, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> {FV.ok(one, FE.pow_bits(R, x, bs, acc)) == True{} : Bool}:
  match bs:
    case Nil{}:
      %Equal.sym(FE.Fe, FE.pow_bits(R, x, Nil{}, acc), acc, pbs_nil(R, x, acc)) : {FV.ok(one, _) == True{} : Bool}
      ha
    case Con{+b, +bt}:
      %Equal.sym(FE.Fe, FE.pow_bits(R, x, Con{b, bt}, acc), FE.pow_bits(R, x, bt, FE.pow_bit(R, b, x, acc)), pbs_con(R, x, b, bt, acc)) : {FV.ok(one, _) == True{} : Bool}
      pbs_okb(one, h1, R, hR, bt, x, FE.pow_bit(R, b, x, acc), hx, pb_okb(one, h1, R, hR, b, x, acc, hx, ha))

# ---- values ----

# acc^2 x
def step_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +acc: FE.Fe, +x: FE.Fe, +ha: {FV.ok(one, acc) == True{} : Bool}, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.mul(R, FE.sq(R, acc), x)), Nat.mul(Nat.mul(FV.value(acc), FV.value(acc)), FV.value(x))):
  +A = FV.value(acc)
  +X = FV.value(x)
  +e1 = OP.mul_c(one, h1, pp, hP, R, hR, FE.sq(R, acc), x, sq_ok(one, h1, R, hR, acc, ha), hx)
  +e2 = G.c_mul(pp, FV.value(FE.sq(R, acc)), Nat.mul(A, A), X, X, OP.mul_c(one, h1, pp, hP, R, hR, acc, acc, ha, ha), G.c_refl(pp, X))
  G.c_trans(pp, FV.value(FE.mul(R, FE.sq(R, acc), x)), Nat.mul(FV.value(FE.sq(R, acc)), X), Nat.mul(Nat.mul(A, A), X), e1, e2)

# a^one * 1 == a
def pow_one_one(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat) -> {Nat.mul(Nat.pow(a, one), 1n) == a : Nat}:
  +e = L.subst(Nat, o => {Nat.pow(a, o) == a : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), NA.mul_one(a))
  Equal.trans(Nat, Nat.mul(Nat.pow(a, one), 1n), Nat.pow(a, one), a, NA.mul_one(Nat.pow(a, one)), e)

# (a^2 y)^(2^m) z == a^(2^(m+1)) (y^(2^m) z)
def sq_pow(+a: Nat, +y: Nat, +s: Nat, +z: Nat, +s2: Nat, +hs: {Nat.add(s, s) == s2 : Nat}) -> {Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), y), s), z) == Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(y, s), z)) : Nat}:
  +e1 = Equal.cong(Nat, Nat, t => Nat.mul(t, z), Nat.pow(Nat.mul(Nat.mul(a, a), y), s), Nat.mul(Nat.pow(Nat.mul(a, a), s), Nat.pow(y, s)), NR.mul_pow(Nat.mul(a, a), y, s))
  +e2a = Equal.trans(Nat, Nat.pow(Nat.mul(a, a), s), Nat.mul(Nat.pow(a, s), Nat.pow(a, s)), Nat.pow(a, s2), NR.mul_pow(a, a, s), Equal.trans(Nat, Nat.mul(Nat.pow(a, s), Nat.pow(a, s)), Nat.pow(a, Nat.add(s, s)), Nat.pow(a, s2), Equal.sym(Nat, Nat.pow(a, Nat.add(s, s)), Nat.mul(Nat.pow(a, s), Nat.pow(a, s)), NR.pow_add(a, s, s)), Equal.cong(Nat, Nat, t => Nat.pow(a, t), Nat.add(s, s), s2, hs)))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.mul(t, Nat.pow(y, s)), z), Nat.pow(Nat.mul(a, a), s), Nat.pow(a, s2), e2a)
  +e3 = NA.mul_assoc(Nat.pow(a, s2), Nat.pow(y, s), z)
  Equal.trans(Nat, Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), y), s), z), Nat.mul(Nat.mul(Nat.pow(Nat.mul(a, a), s), Nat.pow(y, s)), z), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(y, s), z)), e1, Equal.trans(Nat, Nat.mul(Nat.mul(Nat.pow(Nat.mul(a, a), s), Nat.pow(y, s)), z), Nat.mul(Nat.mul(Nat.pow(a, s2), Nat.pow(y, s)), z), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(y, s), z)), e2, e3))

def pb_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +b: Bool, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_bit(R, b, x, acc)), Nat.mul(Nat.mul(FV.value(acc), FV.value(acc)), Nat.pow(FV.value(x), bexp(b)))):
  match b:
    case True{}:
      +A = FV.value(acc)
      +X = FV.value(x)
      G.c_trans(pp, FV.value(FE.mul(R, FE.sq(R, acc), x)), Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), step_c(one, h1, pp, hP, R, hR, acc, x, ha, hx), G.c_eq(pp, Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), Equal.cong(Nat, Nat, t => Nat.mul(Nat.mul(A, A), t), X, Nat.pow(X, 1n), Equal.sym(Nat, Nat.mul(X, 1n), X, NA.mul_one(X)))))
    case False{}:
      +A = FV.value(acc)
      G.c_trans(pp, FV.value(FE.sq(R, acc)), Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), OP.mul_c(one, h1, pp, hP, R, hR, acc, acc, ha, ha), G.c_eq(pp, Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), Equal.sym(Nat, Nat.mul(Nat.mul(A, A), 1n), Nat.mul(A, A), NA.mul_one(Nat.mul(A, A)))))

# (a^2 x^e)^s y == a^(2 s) x^(e s) y
def bit_pow(+a: Nat, +x: Nat, +e: Nat, +s: Nat, +z: Nat, +s2: Nat, +hs: {Nat.add(s, s) == s2 : Nat}) -> {Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), Nat.pow(x, e)), s), Nat.pow(x, z)) == Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))) : Nat}:
  +e1 = sq_pow(a, Nat.pow(x, e), s, Nat.pow(x, z), s2, hs)
  +e2 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(a, s2), Nat.mul(t, Nat.pow(x, z))), Nat.pow(Nat.pow(x, e), s), Nat.pow(x, Nat.mul(e, s)), G.pow_pow(x, e, s))
  +e3 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(a, s2), t), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z)), Nat.pow(x, Nat.add(Nat.mul(e, s), z)), Equal.sym(Nat, Nat.pow(x, Nat.add(Nat.mul(e, s), z)), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z)), NR.pow_add(x, Nat.mul(e, s), z)))
  Equal.trans(Nat, Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), Nat.pow(x, e)), s), Nat.pow(x, z)), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(Nat.pow(x, e), s), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))), e1, Equal.trans(Nat, Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(Nat.pow(x, e), s), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))), e2, e3))

def pbs_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +bs: List<&2, Bool>, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_bits(R, x, bs, acc)), Nat.mul(Nat.pow(FV.value(acc), WD.sc(blen(bs), one)), Nat.pow(FV.value(x), eb(one, bs)))):
  match bs:
    case Nil{}:
      %Equal.sym(FE.Fe, FE.pow_bits(R, x, Nil{}, acc), acc, pbs_nil(R, x, acc)) : G.ceq(pp, FV.value(_), Nat.mul(Nat.pow(FV.value(acc), one), 1n))
      G.c_eq(pp, FV.value(acc), Nat.mul(Nat.pow(FV.value(acc), one), 1n), Equal.sym(Nat, Nat.mul(Nat.pow(FV.value(acc), one), 1n), FV.value(acc), pow_one_one(one, h1, FV.value(acc))))
    case Con{+b, +bt}:
      +A = FV.value(acc)
      +X = FV.value(x)
      +acc2 = FE.pow_bit(R, b, x, acc)
      +S = WD.sc(blen(bt), one)
      +Z = eb(one, bt)
      +E = bexp(b)
      +ha2 = pb_okb(one, h1, R, hR, b, x, acc, hx, ha)
      +ih = pbs_val(one, h1, pp, hP, R, hR, bt, x, acc2, hx, ha2)
      %Equal.sym(FE.Fe, FE.pow_bits(R, x, Con{b, bt}, acc), FE.pow_bits(R, x, bt, acc2), pbs_con(R, x, b, bt, acc)) : G.ceq(pp, FV.value(_), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))))
      +e1 = G.c_mul(pp, Nat.pow(FV.value(acc2), S), Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z), Nat.pow(X, Z), G.c_pow(pp, FV.value(acc2), Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S, pb_val(one, h1, pp, hP, R, hR, b, x, acc, hx, ha)), G.c_refl(pp, Nat.pow(X, Z)))
      +e2 = bit_pow(A, X, E, S, Z, WD.sc(1n+blen(bt), one), M.sc_dbl(blen(bt), one))
      G.c_trans(pp, FV.value(FE.pow_bits(R, x, bt, acc2)), Nat.mul(Nat.pow(FV.value(acc2), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), ih, G.c_trans(pp, Nat.mul(Nat.pow(FV.value(acc2), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), e1, G.c_eq(pp, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), e2)))

# ---- x^(Fo(250) 2^k + e) ----

def cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  NR.add_cancel(c, a, b, Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(c, b), NA.add_comm(c, a), Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(c, b), e, NA.add_comm(b, c))))

# ---- x^(2^250 - 1) by the addition chain (FE.sqn, FE.cat, FE.p250) ----

def sqn_zero(+R: Nat, +g: FE.Fe, +y: FE.Fe) -> {FE.sqn(R, g, 0n, y) == y : FE.Fe}:
  match g:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def sqn_step(+R: Nat, +g: FE.Fe, +y: FE.Fe, +m: Nat) -> {FE.sqn(R, g, 1n+m, y) == FE.sqn(R, g, m, FE.sq(R, y)) : FE.Fe}:
  match g:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def sqn_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +g: FE.Fe, +n: Nat, +y: FE.Fe, +hy: {FV.ok(one, y) == True{} : Bool}) -> {FV.ok(one, FE.sqn(R, g, n, y)) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(FE.Fe, FE.sqn(R, g, 0n, y), y, sqn_zero(R, g, y)) : {FV.ok(one, _) == True{} : Bool}
      hy
    case 1n+ +m:
      %Equal.sym(FE.Fe, FE.sqn(R, g, 1n+m, y), FE.sqn(R, g, m, FE.sq(R, y)), sqn_step(R, g, y, m)) : {FV.ok(one, _) == True{} : Bool}
      sqn_ok(one, h1, R, hR, g, m, FE.sq(R, y), sq_ok(one, h1, R, hR, y, hy))

# (a a)^s == a^(s + s)
def pow_sq(+a: Nat, +s: Nat) -> {Nat.pow(Nat.mul(a, a), s) == Nat.pow(a, Nat.add(s, s)) : Nat}:
  Equal.trans(Nat, Nat.pow(Nat.mul(a, a), s), Nat.mul(Nat.pow(a, s), Nat.pow(a, s)), Nat.pow(a, Nat.add(s, s)), NR.mul_pow(a, a, s), Equal.sym(Nat, Nat.pow(a, Nat.add(s, s)), Nat.mul(Nat.pow(a, s), Nat.pow(a, s)), NR.pow_add(a, s, s)))

def pow_one(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat) -> {Nat.pow(a, one) == a : Nat}:
  L.subst(Nat, o => {Nat.pow(a, o) == a : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), NA.mul_one(a))

def sqn_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +g: FE.Fe, +n: Nat, +y: FE.Fe, +hy: {FV.ok(one, y) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.sqn(R, g, n, y)), Nat.pow(FV.value(y), WD.sc(n, one))):
  match n:
    case 0n:
      %Equal.sym(FE.Fe, FE.sqn(R, g, 0n, y), y, sqn_zero(R, g, y)) : G.ceq(pp, FV.value(_), Nat.pow(FV.value(y), one))
      G.c_eq(pp, FV.value(y), Nat.pow(FV.value(y), one), Equal.sym(Nat, Nat.pow(FV.value(y), one), FV.value(y), pow_one(one, h1, FV.value(y))))
    case 1n+ +m:
      +Y = FV.value(y)
      +S = WD.sc(m, one)
      +y2 = FE.sq(R, y)
      %Equal.sym(FE.Fe, FE.sqn(R, g, 1n+m, y), FE.sqn(R, g, m, y2), sqn_step(R, g, y, m)) : G.ceq(pp, FV.value(_), Nat.pow(Y, WD.sc(1n+m, one)))
      +ih = sqn_val(one, h1, pp, hP, R, hR, g, m, y2, sq_ok(one, h1, R, hR, y, hy))
      +e1 = G.c_pow(pp, FV.value(y2), Nat.mul(Y, Y), S, OP.mul_c(one, h1, pp, hP, R, hR, y, y, hy, hy))
      +e2 = Equal.trans(Nat, Nat.pow(Nat.mul(Y, Y), S), Nat.pow(Y, Nat.add(S, S)), Nat.pow(Y, WD.sc(1n+m, one)), pow_sq(Y, S), Equal.cong(Nat, Nat, t => Nat.pow(Y, t), Nat.add(S, S), WD.sc(1n+m, one), M.sc_dbl(m, one)))
      G.c_trans(pp, FV.value(FE.sqn(R, g, m, y2)), Nat.pow(FV.value(y2), S), Nat.pow(Y, WD.sc(1n+m, one)), ih, G.c_trans(pp, Nat.pow(FV.value(y2), S), Nat.pow(Nat.mul(Y, Y), S), Nat.pow(Y, WD.sc(1n+m, one)), e1, G.c_eq(pp, Nat.pow(Nat.mul(Y, Y), S), Nat.pow(Y, WD.sc(1n+m, one)), e2)))

# Fo(n) 2^m + Fo(m) == Fo(n + m)
def fo_cat(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +m: Nat) -> {Nat.add(Nat.mul(Fo(one, n), WD.sc(m, one)), Fo(one, m)) == Fo(one, Nat.add(n, m)) : Nat}:
  +S = WD.sc(m, one)
  +F = Fo(one, n)
  +a = Nat.add(Nat.mul(F, S), Fo(one, m))
  +e1 = Equal.trans(Nat, Nat.add(a, one), Nat.add(Nat.mul(F, S), Nat.add(Fo(one, m), one)), Nat.add(Nat.mul(F, S), S), NA.add_assoc(Nat.mul(F, S), Fo(one, m), one), M.cong_r(Nat.mul(F, S), Nat.add(Fo(one, m), one), S, fo_sum(one, h1, m)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.mul(F, S), S), Nat.mul(Nat.add(F, one), S), Nat.mul(WD.sc(n, one), S), Equal.sym(Nat, Nat.mul(Nat.add(F, one), S), Nat.add(Nat.mul(F, S), S), Equal.trans(Nat, Nat.mul(Nat.add(F, one), S), Nat.add(Nat.mul(F, S), Nat.mul(one, S)), Nat.add(Nat.mul(F, S), S), NA.mul_add_right(F, one, S), M.cong_r(Nat.mul(F, S), Nat.mul(one, S), S, one_k(one, h1, S)))), Equal.cong(Nat, Nat, t => Nat.mul(t, S), Nat.add(F, one), WD.sc(n, one), fo_sum(one, h1, n)))
  +e3 = Equal.trans(Nat, Nat.mul(WD.sc(n, one), S), WD.sc(Nat.add(n, m), one), Nat.add(Fo(one, Nat.add(n, m)), one), PW.scsc(n, m, one, h1), Equal.sym(Nat, Nat.add(Fo(one, Nat.add(n, m)), one), WD.sc(Nat.add(n, m), one), fo_sum(one, h1, Nat.add(n, m))))
  cancel_r(a, Fo(one, Nat.add(n, m)), one, Equal.trans(Nat, Nat.add(a, one), Nat.add(Nat.mul(F, S), S), Nat.add(Fo(one, Nat.add(n, m)), one), e1, Equal.trans(Nat, Nat.add(Nat.mul(F, S), S), Nat.mul(WD.sc(n, one), S), Nat.add(Fo(one, Nat.add(n, m)), one), e2, e3)))

def cat_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +g: FE.Fe, +m: Nat, +y: FE.Fe, +z: FE.Fe, +hy: {FV.ok(one, y) == True{} : Bool}, +hz: {FV.ok(one, z) == True{} : Bool}) -> {FV.ok(one, FE.cat(R, g, y, z, m)) == True{} : Bool}:
  OP.mul_ok(one, h1, R, hR, FE.sqn(R, g, m, y), z, sqn_ok(one, h1, R, hR, g, m, y, hy), hz)

# y == x^Fo(n), z == x^Fo(m) -> cat(y, z, m) == x^Fo(n + m)
def cat_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +g: FE.Fe, +n: Nat, +m: Nat, +X: Nat, +y: FE.Fe, +z: FE.Fe, +hy: {FV.ok(one, y) == True{} : Bool}, +hz: {FV.ok(one, z) == True{} : Bool}, +vy: G.ceq(pp, FV.value(y), Nat.pow(X, Fo(one, n))), +vz: G.ceq(pp, FV.value(z), Nat.pow(X, Fo(one, m)))) -> G.ceq(pp, FV.value(FE.cat(R, g, y, z, m)), Nat.pow(X, Fo(one, Nat.add(n, m)))):
  +S = WD.sc(m, one)
  +q = FE.sqn(R, g, m, y)
  +Fn = Fo(one, n)
  +Fm = Fo(one, m)
  +e0 = OP.mul_c(one, h1, pp, hP, R, hR, q, z, sqn_ok(one, h1, R, hR, g, m, y, hy), hz)
  +e1 = G.c_trans(pp, FV.value(q), Nat.pow(FV.value(y), S), Nat.pow(Nat.pow(X, Fn), S), sqn_val(one, h1, pp, hP, R, hR, g, m, y, hy), G.c_pow(pp, FV.value(y), Nat.pow(X, Fn), S, vy))
  +e2 = G.c_mul(pp, FV.value(q), Nat.pow(Nat.pow(X, Fn), S), FV.value(z), Nat.pow(X, Fm), e1, vz)
  +e3 = Equal.trans(Nat, Nat.mul(Nat.pow(Nat.pow(X, Fn), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(X, Nat.mul(Fn, S)), Nat.pow(X, Fm)), Nat.pow(X, Nat.add(Nat.mul(Fn, S), Fm)), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.pow(X, Fm)), Nat.pow(Nat.pow(X, Fn), S), Nat.pow(X, Nat.mul(Fn, S)), G.pow_pow(X, Fn, S)), Equal.sym(Nat, Nat.pow(X, Nat.add(Nat.mul(Fn, S), Fm)), Nat.mul(Nat.pow(X, Nat.mul(Fn, S)), Nat.pow(X, Fm)), NR.pow_add(X, Nat.mul(Fn, S), Fm)))
  +e4 = Equal.cong(Nat, Nat, t => Nat.pow(X, t), Nat.add(Nat.mul(Fn, S), Fm), Fo(one, Nat.add(n, m)), fo_cat(one, h1, n, m))
  G.c_trans(pp, FV.value(FE.cat(R, g, y, z, m)), Nat.mul(FV.value(q), FV.value(z)), Nat.pow(X, Fo(one, Nat.add(n, m))), e0, G.c_trans(pp, Nat.mul(FV.value(q), FV.value(z)), Nat.mul(Nat.pow(Nat.pow(X, Fn), S), Nat.pow(X, Fm)), Nat.pow(X, Fo(one, Nat.add(n, m))), e2, G.c_eq(pp, Nat.mul(Nat.pow(Nat.pow(X, Fn), S), Nat.pow(X, Fm)), Nat.pow(X, Fo(one, Nat.add(n, m))), Equal.trans(Nat, Nat.mul(Nat.pow(Nat.pow(X, Fn), S), Nat.pow(X, Fm)), Nat.pow(X, Nat.add(Nat.mul(Fn, S), Fm)), Nat.pow(X, Fo(one, Nat.add(n, m))), e3, e4))))

# Fo(1) == one
def fo1(+one: Nat, +h1: {one == 1n : Nat}) -> {Fo(one, 1n) == one : Nat}:
  L.subst(Nat, o => {Fo(o, 1n) == o : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

def p250_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> {FV.ok(one, FE.p250(R, x)) == True{} : Bool}:
  +z2 = FE.cat(R, x, x, x, 1n)
  +o2 = cat_ok(one, h1, R, hR, x, 1n, x, x, hx, hx)
  +z4 = FE.cat(R, x, z2, z2, 2n)
  +o4 = cat_ok(one, h1, R, hR, x, 2n, z2, z2, o2, o2)
  +z5 = FE.cat(R, x, z4, x, 1n)
  +o5 = cat_ok(one, h1, R, hR, x, 1n, z4, x, o4, hx)
  +z10 = FE.cat(R, x, z5, z5, 5n)
  +o10 = cat_ok(one, h1, R, hR, x, 5n, z5, z5, o5, o5)
  +z20 = FE.cat(R, x, z10, z10, 10n)
  +o20 = cat_ok(one, h1, R, hR, x, 10n, z10, z10, o10, o10)
  +z40 = FE.cat(R, x, z20, z20, 20n)
  +o40 = cat_ok(one, h1, R, hR, x, 20n, z20, z20, o20, o20)
  +z50 = FE.cat(R, x, z40, z10, 10n)
  +o50 = cat_ok(one, h1, R, hR, x, 10n, z40, z10, o40, o10)
  +z100 = FE.cat(R, x, z50, z50, 50n)
  +o100 = cat_ok(one, h1, R, hR, x, 50n, z50, z50, o50, o50)
  +z200 = FE.cat(R, x, z100, z100, 100n)
  +o200 = cat_ok(one, h1, R, hR, x, 100n, z100, z100, o100, o100)
  cat_ok(one, h1, R, hR, x, 50n, z200, z50, o200, o50)

def p250_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.p250(R, x)), Nat.pow(FV.value(x), Fo(one, 250n))):
  +X = FV.value(x)
  +v1 = G.c_eq(pp, X, Nat.pow(X, Fo(one, 1n)), Equal.trans(Nat, X, Nat.pow(X, one), Nat.pow(X, Fo(one, 1n)), Equal.sym(Nat, Nat.pow(X, one), X, pow_one(one, h1, X)), Equal.cong(Nat, Nat, t => Nat.pow(X, t), one, Fo(one, 1n), Equal.sym(Nat, Fo(one, 1n), one, fo1(one, h1)))))
  +z2 = FE.cat(R, x, x, x, 1n)
  +o2 = cat_ok(one, h1, R, hR, x, 1n, x, x, hx, hx)
  +v2 = cat_val(one, h1, pp, hP, R, hR, x, 1n, 1n, X, x, x, hx, hx, v1, v1)
  +z4 = FE.cat(R, x, z2, z2, 2n)
  +o4 = cat_ok(one, h1, R, hR, x, 2n, z2, z2, o2, o2)
  +v4 = cat_val(one, h1, pp, hP, R, hR, x, 2n, 2n, X, z2, z2, o2, o2, v2, v2)
  +z5 = FE.cat(R, x, z4, x, 1n)
  +o5 = cat_ok(one, h1, R, hR, x, 1n, z4, x, o4, hx)
  +v5 = cat_val(one, h1, pp, hP, R, hR, x, 4n, 1n, X, z4, x, o4, hx, v4, v1)
  +z10 = FE.cat(R, x, z5, z5, 5n)
  +o10 = cat_ok(one, h1, R, hR, x, 5n, z5, z5, o5, o5)
  +v10 = cat_val(one, h1, pp, hP, R, hR, x, 5n, 5n, X, z5, z5, o5, o5, v5, v5)
  +z20 = FE.cat(R, x, z10, z10, 10n)
  +o20 = cat_ok(one, h1, R, hR, x, 10n, z10, z10, o10, o10)
  +v20 = cat_val(one, h1, pp, hP, R, hR, x, 10n, 10n, X, z10, z10, o10, o10, v10, v10)
  +z40 = FE.cat(R, x, z20, z20, 20n)
  +o40 = cat_ok(one, h1, R, hR, x, 20n, z20, z20, o20, o20)
  +v40 = cat_val(one, h1, pp, hP, R, hR, x, 20n, 20n, X, z20, z20, o20, o20, v20, v20)
  +z50 = FE.cat(R, x, z40, z10, 10n)
  +o50 = cat_ok(one, h1, R, hR, x, 10n, z40, z10, o40, o10)
  +v50 = cat_val(one, h1, pp, hP, R, hR, x, 40n, 10n, X, z40, z10, o40, o10, v40, v10)
  +z100 = FE.cat(R, x, z50, z50, 50n)
  +o100 = cat_ok(one, h1, R, hR, x, 50n, z50, z50, o50, o50)
  +v100 = cat_val(one, h1, pp, hP, R, hR, x, 50n, 50n, X, z50, z50, o50, o50, v50, v50)
  +z200 = FE.cat(R, x, z100, z100, 100n)
  +o200 = cat_ok(one, h1, R, hR, x, 100n, z100, z100, o100, o100)
  +v200 = cat_val(one, h1, pp, hP, R, hR, x, 100n, 100n, X, z100, z100, o100, o100, v100, v100)
  cat_val(one, h1, pp, hP, R, hR, x, 200n, 50n, X, z200, z50, o200, o50, v200, v50)

# pow_bits(x, bs, p250(x)) == x^(Fo(250) 2^len + eb)
def chain_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +bs: List<&2, Bool>, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_bits(R, x, bs, FE.p250(R, x))), Nat.pow(FV.value(x), Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(bs), one)), eb(one, bs)))):
  +X = FV.value(x)
  +a1 = FE.p250(R, x)
  +F2 = Fo(one, 250n)
  +S = WD.sc(blen(bs), one)
  +ha1 = p250_ok(one, h1, R, hR, x, hx)
  +v1 = p250_val(one, h1, pp, hP, R, hR, x, hx)
  +e2 = pbs_val(one, h1, pp, hP, R, hR, bs, x, a1, hx, ha1)
  +e3 = G.c_mul(pp, Nat.pow(FV.value(a1), S), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs)), Nat.pow(X, eb(one, bs)), G.c_pow(pp, FV.value(a1), Nat.pow(X, F2), S, v1), G.c_refl(pp, Nat.pow(X, eb(one, bs))))
  +e4 = Equal.trans(Nat, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.pow(X, eb(one, bs))), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, Nat.mul(F2, S)), G.pow_pow(X, F2, S)), Equal.sym(Nat, Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), NR.pow_add(X, Nat.mul(F2, S), eb(one, bs))))
  G.c_trans(pp, FV.value(FE.pow_bits(R, x, bs, a1)), Nat.mul(Nat.pow(FV.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e2, G.c_trans(pp, Nat.mul(Nat.pow(FV.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e3, G.c_eq(pp, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e4)))

# ---- the exponents ----

# 32 Fo(250) + 32 == p + 19
def f32(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(Fo(one, 250n), 32n), 32n) == Nat.add(1n+pp, 19n) : Nat}:
  +F2 = Fo(one, 250n)
  +e1 = Equal.trans(Nat, Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(Nat.mul(F2, 32n), Nat.mul(one, 32n)), Nat.mul(Nat.add(F2, one), 32n), M.cong_r(Nat.mul(F2, 32n), 32n, Nat.mul(one, 32n), Equal.sym(Nat, Nat.mul(one, 32n), 32n, one_k(one, h1, 32n))), Equal.sym(Nat, Nat.mul(Nat.add(F2, one), 32n), Nat.add(Nat.mul(F2, 32n), Nat.mul(one, 32n)), NA.mul_add_right(F2, one, 32n)))
  +e2 = Equal.cong(Nat, Nat, t => Nat.mul(t, 32n), Nat.add(F2, one), WD.sc(250n, one), fo_sum(one, h1, 250n))
  +e3 = AR.mul_sc(5n, WD.sc(250n, one))
  Equal.trans(Nat, Nat.add(Nat.mul(F2, 32n), 32n), Nat.mul(Nat.add(F2, one), 32n), Nat.add(1n+pp, 19n), e1, Equal.trans(Nat, Nat.mul(Nat.add(F2, one), 32n), Nat.mul(WD.sc(250n, one), 32n), Nat.add(1n+pp, 19n), e2, Equal.trans(Nat, Nat.mul(WD.sc(250n, one), 32n), WD.sc(255n, one), Nat.add(1n+pp, 19n), e3, Equal.sym(Nat, Nat.add(1n+pp, 19n), WD.sc(255n, one), hP))))

def small_one(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +a: Nat, +ha: {WD.sc(k, 1n) == a : Nat}) -> {WD.sc(k, one) == a : Nat}:
  L.subst(Nat, o => {WD.sc(k, o) == a : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), ha)

def inv_bits() -> List<&2, Bool>:
  [False{}, True{}, False{}, True{}, True{}]

def p58_bits() -> List<&2, Bool>:
  [False{}, True{}]

def eb_inv(+one: Nat, +h1: {one == 1n : Nat}) -> {eb(one, inv_bits()) == 11n : Nat}:
  L.subst(Nat, o => {eb(o, inv_bits()) == 11n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

def eb_p58(+one: Nat, +h1: {one == 1n : Nat}) -> {eb(one, p58_bits()) == 1n : Nat}:
  L.subst(Nat, o => {eb(o, p58_bits()) == 1n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

# 32 Fo(250) + 11 == p - 2
def inv_exp(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(inv_bits()), one)), eb(one, inv_bits())) == Nat.sub(1n+pp, 2n) : Nat}:
  +F2 = Fo(one, 250n)
  +P = {1n+pp : Nat}
  %Equal.sym(Nat, WD.sc(5n, one), 32n, small_one(one, h1, 5n, 32n, {==})) : {Nat.add(Nat.mul(F2, _), eb(one, inv_bits())) == Nat.sub(P, 2n) : Nat}
  %Equal.sym(Nat, eb(one, inv_bits()), 11n, eb_inv(one, h1)) : {Nat.add(Nat.mul(F2, 32n), _) == Nat.sub(P, 2n) : Nat}
  +x = Nat.add(Nat.mul(F2, 32n), 11n)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(x, 2n), 19n), Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(P, 19n), Equal.trans(Nat, Nat.add(Nat.add(x, 2n), 19n), Nat.add(x, Nat.add(2n, 19n)), Nat.add(Nat.mul(F2, 32n), 32n), NA.add_assoc(x, 2n, 19n), NA.add_assoc(Nat.mul(F2, 32n), 11n, 21n)), f32(one, h1, pp, hP))
  +e2 = cancel_r(Nat.add(x, 2n), P, 19n, e1)
  +e3 = Equal.trans(Nat, P, Nat.add(x, 2n), Nat.add(2n, x), Equal.sym(Nat, Nat.add(x, 2n), P, e2), NA.add_comm(x, 2n))
  %Equal.sym(Nat, P, Nat.add(2n, x), e3) : {x == Nat.sub(_, 2n) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(2n, x), 2n), x, N.add_sub_cancel(2n, x))

# 4 Fo(250) + 1 == (p - 5) / 8
def p58_exp(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(p58_bits()), one)), eb(one, p58_bits())) == Nat.div(Nat.sub(1n+pp, 5n), 8n) : Nat}:
  +F2 = Fo(one, 250n)
  +P = {1n+pp : Nat}
  %Equal.sym(Nat, WD.sc(2n, one), 4n, small_one(one, h1, 2n, 4n, {==})) : {Nat.add(Nat.mul(F2, _), eb(one, p58_bits())) == Nat.div(Nat.sub(P, 5n), 8n) : Nat}
  %Equal.sym(Nat, eb(one, p58_bits()), 1n, eb_p58(one, h1)) : {Nat.add(Nat.mul(F2, 4n), _) == Nat.div(Nat.sub(P, 5n), 8n) : Nat}
  +e = Nat.add(Nat.mul(F2, 4n), 1n)
  +m8 = Equal.trans(Nat, Nat.mul(e, 8n), Nat.add(Nat.mul(Nat.mul(F2, 4n), 8n), Nat.mul(1n, 8n)), Nat.add(Nat.mul(F2, 32n), 8n), NA.mul_add_right(Nat.mul(F2, 4n), 1n, 8n), M.cong_l(Nat.mul(Nat.mul(F2, 4n), 8n), Nat.mul(F2, 32n), Nat.mul(1n, 8n), NA.mul_assoc(F2, 4n, 8n)))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(e, 8n), 5n), 19n), Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 8n), 5n), 19n), Nat.add(P, 19n), M.cong_l(Nat.add(Nat.mul(e, 8n), 5n), Nat.add(Nat.add(Nat.mul(F2, 32n), 8n), 5n), 19n, M.cong_l(Nat.mul(e, 8n), Nat.add(Nat.mul(F2, 32n), 8n), 5n, m8)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 8n), 5n), 19n), Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(P, 19n), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(F2, 32n), 8n), 5n), 19n), Nat.add(Nat.add(Nat.mul(F2, 32n), 8n), Nat.add(5n, 19n)), Nat.add(Nat.mul(F2, 32n), 32n), NA.add_assoc(Nat.add(Nat.mul(F2, 32n), 8n), 5n, 19n), NA.add_assoc(Nat.mul(F2, 32n), 8n, 24n)), f32(one, h1, pp, hP)))
  +e2 = cancel_r(Nat.add(Nat.mul(e, 8n), 5n), P, 19n, e1)
  +e3 = Equal.trans(Nat, P, Nat.add(Nat.mul(e, 8n), 5n), Nat.add(5n, Nat.mul(e, 8n)), Equal.sym(Nat, Nat.add(Nat.mul(e, 8n), 5n), P, e2), NA.add_comm(Nat.mul(e, 8n), 5n))
  %Equal.sym(Nat, P, Nat.add(5n, Nat.mul(e, 8n)), e3) : {e == Nat.div(Nat.sub(_, 5n), 8n) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(5n, Nat.mul(e, 8n)), 5n), Nat.mul(e, 8n), N.add_sub_cancel(5n, Nat.mul(e, 8n))) : {e == Nat.div(_, 8n) : Nat}
  %N.add_zero(Nat.mul(e, 8n)) : {e == Nat.div(_, 8n) : Nat}
  Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(e, 8n), 0n), 8n), e, NR.div_of(e, 7n, 0n, {==}))

# ---- inv and pow_p58 ----

def inv_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> {FV.ok(one, FE.inv(R, x)) == True{} : Bool}:
  pbs_okb(one, h1, R, hR, inv_bits(), x, FE.p250(R, x), hx, p250_ok(one, h1, R, hR, x, hx))

def p58_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> {FV.ok(one, FE.pow_p58(R, x)) == True{} : Bool}:
  pbs_okb(one, h1, R, hR, p58_bits(), x, FE.p250(R, x), hx, p250_ok(one, h1, R, hR, x, hx))

def inv_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.inv(R, x)), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(inv_bits()), one)), eb(one, inv_bits()))
  G.c_trans(pp, FV.value(FE.inv(R, x)), Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n)), chain_val(one, h1, pp, hP, R, hR, inv_bits(), x, hx), G.c_eq(pp, Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n)), Equal.cong(Nat, Nat, t => Nat.pow(FV.value(x), t), ex, Nat.sub(1n+pp, 2n), inv_exp(one, h1, pp, hP))))

def p58_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_p58(R, x)), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(p58_bits()), one)), eb(one, p58_bits()))
  G.c_trans(pp, FV.value(FE.pow_p58(R, x)), Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), chain_val(one, h1, pp, hP, R, hR, p58_bits(), x, hx), G.c_eq(pp, Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), Equal.cong(Nat, Nat, t => Nat.pow(FV.value(x), t), ex, Nat.div(Nat.sub(1n+pp, 5n), 8n), p58_exp(one, h1, pp, hP))))
