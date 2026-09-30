import Base
import ../../../spec/lib/common.bend as C
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
# field): pow_ones(n, x, acc) = acc^(2^n) x^(2^n - 1) and pow_bits (square,
# multiply on a one bit), hence inv(x) = x^(p - 2) and
# pow_p58(x) = x^((p - 5) / 8), mod p.

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

# (a + c) - b == a + (c - b) for b <= c
def sub_add_r(+a: Nat, +c: Nat, +b: Nat, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.sub(Nat.add(a, c), b) == Nat.add(a, Nat.sub(c, b)) : Nat}:
  +d = Nat.sub(c, b)
  +e1 = Equal.cong(Nat, Nat, t => Nat.sub(Nat.add(a, t), b), c, Nat.add(b, d), Equal.sym(Nat, Nat.add(b, d), c, N.sub_add(c, b, h)))
  +e2 = Equal.cong(Nat, Nat, t => Nat.sub(t, b), Nat.add(a, Nat.add(b, d)), Nat.add(b, Nat.add(a, d)), NA.add_swap(a, b, d))
  Equal.trans(Nat, Nat.sub(Nat.add(a, c), b), Nat.sub(Nat.add(a, Nat.add(b, d)), b), Nat.add(a, d), e1, Equal.trans(Nat, Nat.sub(Nat.add(a, Nat.add(b, d)), b), Nat.sub(Nat.add(b, Nat.add(a, d)), b), Nat.add(a, d), e2, N.add_sub_cancel(b, Nat.add(a, d))))

# 2^m + (2^m - 1) == 2^(m+1) - 1
def fo_step(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat) -> {Nat.add(WD.sc(m, one), Fo(one, m)) == Fo(one, 1n+m) : Nat}:
  +S = WD.sc(m, one)
  +e1 = Equal.cong(Nat, Nat, t => Nat.sub(t, one), Nat.double(S), Nat.add(S, S), NA.double_self(S))
  Equal.sym(Nat, Nat.sub(Nat.double(S), one), Nat.add(S, Nat.sub(S, one)), Equal.trans(Nat, Nat.sub(Nat.double(S), one), Nat.sub(Nat.add(S, S), one), Nat.add(S, Nat.sub(S, one)), e1, sub_add_r(S, S, one, one_le_sc(one, h1, m))))

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

def po_zero(+R: Nat, +x: FE.Fe, +acc: FE.Fe) -> {FE.pow_ones(R, x, 0n, acc) == acc : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def po_step(+R: Nat, +x: FE.Fe, +m: Nat, +acc: FE.Fe) -> {FE.pow_ones(R, x, 1n+m, acc) == FE.pow_ones(R, x, m, FE.mul(R, FE.sq(R, acc), x)) : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def pbs_nil(+R: Nat, +x: FE.Fe, +acc: FE.Fe) -> {FE.pow_bits(R, x, Nil{}, acc) == acc : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

def pbs_con(+R: Nat, +x: FE.Fe, +b: Bool, +bt: List<&2, Bool>, +acc: FE.Fe) -> {FE.pow_bits(R, x, Con{b, bt}, acc) == FE.pow_bits(R, x, bt, FE.pow_bit(R, b, x, acc)) : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

# ---- shapes ----

def po_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +n: Nat, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> {FV.ok(one, FE.pow_ones(R, x, n, acc)) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(FE.Fe, FE.pow_ones(R, x, 0n, acc), acc, po_zero(R, x, acc)) : {FV.ok(one, _) == True{} : Bool}
      ha
    case 1n+ +m:
      %Equal.sym(FE.Fe, FE.pow_ones(R, x, 1n+m, acc), FE.pow_ones(R, x, m, FE.mul(R, FE.sq(R, acc), x)), po_step(R, x, m, acc)) : {FV.ok(one, _) == True{} : Bool}
      po_okb(one, h1, R, hR, m, x, FE.mul(R, FE.sq(R, acc), x), hx, OP.mul_ok(one, h1, R, hR, FE.sq(R, acc), x, sq_ok(one, h1, R, hR, acc, ha), hx))

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
  +e1 = OP.mul_c(one, h1, pp, hP, R, hR, FE.sq(R, acc), x)
  +e2 = G.c_mul(pp, FV.value(FE.sq(R, acc)), Nat.mul(A, A), X, X, OP.mul_c(one, h1, pp, hP, R, hR, acc, acc), G.c_refl(pp, X))
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

def po_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +n: Nat, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_ones(R, x, n, acc)), Nat.mul(Nat.pow(FV.value(acc), WD.sc(n, one)), Nat.pow(FV.value(x), Fo(one, n)))):
  match n:
    case 0n:
      +A = FV.value(acc)
      +Rv = Nat.mul(Nat.pow(A, one), Nat.pow(FV.value(x), Fo(one, 0n)))
      %Equal.sym(FE.Fe, FE.pow_ones(R, x, 0n, acc), acc, po_zero(R, x, acc)) : G.ceq(pp, FV.value(_), Rv)
      +e0 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, one), Nat.pow(FV.value(x), t)), Fo(one, 0n), 0n, N.sub_self(one))
      G.c_eq(pp, A, Rv, Equal.sym(Nat, Rv, A, Equal.trans(Nat, Rv, Nat.mul(Nat.pow(A, one), 1n), A, e0, pow_one_one(one, h1, A))))
    case 1n+ +m:
      +A = FV.value(acc)
      +X = FV.value(x)
      +acc2 = FE.mul(R, FE.sq(R, acc), x)
      +S = WD.sc(m, one)
      +Fm = Fo(one, m)
      +ha2 = OP.mul_ok(one, h1, R, hR, FE.sq(R, acc), x, sq_ok(one, h1, R, hR, acc, ha), hx)
      +ih = po_val(one, h1, pp, hP, R, hR, m, x, acc2, hx, ha2)
      %Equal.sym(FE.Fe, FE.pow_ones(R, x, 1n+m, acc), FE.pow_ones(R, x, m, acc2), po_step(R, x, m, acc)) : G.ceq(pp, FV.value(_), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))))
      +e1 = G.c_mul(pp, Nat.pow(FV.value(acc2), S), Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm), Nat.pow(X, Fm), G.c_pow(pp, FV.value(acc2), Nat.mul(Nat.mul(A, A), X), S, step_c(one, h1, pp, hP, R, hR, acc, x, ha, hx)), G.c_refl(pp, Nat.pow(X, Fm)))
      +e2 = sq_pow(A, X, S, Nat.pow(X, Fm), WD.sc(1n+m, one), M.sc_dbl(m, one))
      +e3 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), t), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm)), Nat.pow(X, Nat.add(S, Fm)), Equal.sym(Nat, Nat.pow(X, Nat.add(S, Fm)), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm)), NR.pow_add(X, S, Fm)))
      +fin = G.c_trans(pp, FV.value(FE.pow_ones(R, x, m, acc2)), Nat.mul(Nat.pow(FV.value(acc2), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), ih,
        G.c_trans(pp, Nat.mul(Nat.pow(FV.value(acc2), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), e1, G.c_eq(pp, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Equal.trans(Nat, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), e2, e3))))
      G.c_trans(pp, FV.value(FE.pow_ones(R, x, m, acc2)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))), fin, G.c_eq(pp, Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))), Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, t)), Nat.add(S, Fm), Fo(one, 1n+m), fo_step(one, h1, m))))

def pb_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +b: Bool, +x: FE.Fe, +acc: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}, +ha: {FV.ok(one, acc) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_bit(R, b, x, acc)), Nat.mul(Nat.mul(FV.value(acc), FV.value(acc)), Nat.pow(FV.value(x), bexp(b)))):
  match b:
    case True{}:
      +A = FV.value(acc)
      +X = FV.value(x)
      G.c_trans(pp, FV.value(FE.mul(R, FE.sq(R, acc), x)), Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), step_c(one, h1, pp, hP, R, hR, acc, x, ha, hx), G.c_eq(pp, Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), Equal.cong(Nat, Nat, t => Nat.mul(Nat.mul(A, A), t), X, Nat.pow(X, 1n), Equal.sym(Nat, Nat.mul(X, 1n), X, NA.mul_one(X)))))
    case False{}:
      +A = FV.value(acc)
      G.c_trans(pp, FV.value(FE.sq(R, acc)), Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), OP.mul_c(one, h1, pp, hP, R, hR, acc, acc), G.c_eq(pp, Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), Equal.sym(Nat, Nat.mul(Nat.mul(A, A), 1n), Nat.mul(A, A), NA.mul_one(Nat.mul(A, A)))))

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

# pow_bits(x, bs, pow_ones(x, n, x)) == x^(Fo(n + 1) 2^len + eb)
def chain_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +n: Nat, +bs: List<&2, Bool>, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_bits(R, x, bs, FE.pow_ones(R, x, n, x))), Nat.pow(FV.value(x), Nat.add(Nat.mul(Fo(one, 1n+n), WD.sc(blen(bs), one)), eb(one, bs)))):
  +X = FV.value(x)
  +a1 = FE.pow_ones(R, x, n, x)
  +F2 = Fo(one, 1n+n)
  +S = WD.sc(blen(bs), one)
  +ha1 = po_okb(one, h1, R, hR, n, x, x, hx, hx)
  +e1 = po_val(one, h1, pp, hP, R, hR, n, x, x, hx, hx)
  +e1b = Equal.trans(Nat, Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, Nat.add(WD.sc(n, one), Fo(one, n))), Nat.pow(X, F2), Equal.sym(Nat, Nat.pow(X, Nat.add(WD.sc(n, one), Fo(one, n))), Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), NR.pow_add(X, WD.sc(n, one), Fo(one, n))), Equal.cong(Nat, Nat, t => Nat.pow(X, t), Nat.add(WD.sc(n, one), Fo(one, n)), F2, fo_step(one, h1, n)))
  +v1 = G.c_trans(pp, FV.value(a1), Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, F2), e1, G.c_eq(pp, Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, F2), e1b))
  +e2 = pbs_val(one, h1, pp, hP, R, hR, bs, x, a1, hx, ha1)
  +e3 = G.c_mul(pp, Nat.pow(FV.value(a1), S), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs)), Nat.pow(X, eb(one, bs)), G.c_pow(pp, FV.value(a1), Nat.pow(X, F2), S, v1), G.c_refl(pp, Nat.pow(X, eb(one, bs))))
  +e4 = Equal.trans(Nat, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.pow(X, eb(one, bs))), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, Nat.mul(F2, S)), G.pow_pow(X, F2, S)), Equal.sym(Nat, Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), NR.pow_add(X, Nat.mul(F2, S), eb(one, bs))))
  G.c_trans(pp, FV.value(FE.pow_bits(R, x, bs, a1)), Nat.mul(Nat.pow(FV.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e2, G.c_trans(pp, Nat.mul(Nat.pow(FV.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e3, G.c_eq(pp, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e4)))

# ---- the exponents ----

def cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  NR.add_cancel(c, a, b, Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(c, b), NA.add_comm(c, a), Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(c, b), e, NA.add_comm(b, c))))

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
  pbs_okb(one, h1, R, hR, inv_bits(), x, FE.pow_ones(R, x, 249n, x), hx, po_okb(one, h1, R, hR, 249n, x, x, hx, hx))

def p58_okb(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> {FV.ok(one, FE.pow_p58(R, x)) == True{} : Bool}:
  pbs_okb(one, h1, R, hR, p58_bits(), x, FE.pow_ones(R, x, 249n, x), hx, po_okb(one, h1, R, hR, 249n, x, x, hx, hx))

def inv_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.inv(R, x)), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(inv_bits()), one)), eb(one, inv_bits()))
  G.c_trans(pp, FV.value(FE.inv(R, x)), Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n)), chain_val(one, h1, pp, hP, R, hR, 249n, inv_bits(), x, hx), G.c_eq(pp, Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.sub(1n+pp, 2n)), Equal.cong(Nat, Nat, t => Nat.pow(FV.value(x), t), ex, Nat.sub(1n+pp, 2n), inv_exp(one, h1, pp, hP))))

def p58_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: FE.Fe, +hx: {FV.ok(one, x) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.pow_p58(R, x)), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(p58_bits()), one)), eb(one, p58_bits()))
  G.c_trans(pp, FV.value(FE.pow_p58(R, x)), Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), chain_val(one, h1, pp, hP, R, hR, 249n, p58_bits(), x, hx), G.c_eq(pp, Nat.pow(FV.value(x), ex), Nat.pow(FV.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), Equal.cong(Nat, Nat, t => Nat.pow(FV.value(x), t), ex, Nat.div(Nat.sub(1n+pp, 5n), 8n), p58_exp(one, h1, pp, hP))))
