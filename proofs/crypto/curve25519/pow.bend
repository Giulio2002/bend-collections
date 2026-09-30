import Base
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
import ./consts.bend as K
import ./mulw.bend as MW
import ./cong.bend as G

# The public-exponent powers of src/crypto/curve25519/field.bend:
# pow_ones(n, x, acc) = acc^(2^n) x^(2^n - 1) and pow_bits (square, multiply
# on a one bit), hence inv(x) = x^(p - 2) (250 one bits, then 0 1 0 1 1)
# and pow_p58(x) = x^((p - 5) / 8) (250 one bits, then 0 1), mod p. The
# exponents stay open in the symbolic one (Fo(one, n) + one == 2^n).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# 2^n - 1
def Fo(+one: Nat, +n: Nat) -> Nat:
  Nat.sub(WD.sc(n, one), one)

def one_le_sc(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.is_le(one, WD.sc(n, one)) == True{} : Bool}:
  +a = N.lt_succ_le_succ(0n, WD.sc(n, one), LM.sc_pos1(n, one, h1))
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

def po_zero(+x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {F.pow_ones(x, 0n, acc) == acc : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def po_step(+x: List<&2, U32>, +m: Nat, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {F.pow_ones(x, 1n+m, acc) == F.pow_ones(x, m, F.mul(F.sq(acc), x)) : List<&2, U32>}:
  match x:
    case Nil{}:
      Empty.absurd({acc == F.pow_ones(Nil{}, m, F.mul(F.sq(acc), Nil{})) : List<&2, U32>}, L.false_true(hx))
    case Con{h, t}:
      {==}

def pbs_nil(+x: List<&2, U32>, +acc: List<&2, U32>) -> {F.pow_bits(x, Nil{}, acc) == acc : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def pbs_con(+x: List<&2, U32>, +b: Bool, +bt: List<&2, Bool>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {F.pow_bits(x, Con{b, bt}, acc) == F.pow_bits(x, bt, F.pow_bit(b, x, acc)) : List<&2, U32>}:
  match x:
    case Nil{}:
      Empty.absurd({acc == F.pow_bits(Nil{}, bt, F.pow_bit(b, Nil{}, acc)) : List<&2, U32>}, L.false_true(hx))
    case Con{h, t}:
      {==}

# ---- shapes ----

def po_okb(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> {LM.okb(32n, F.pow_ones(x, n, acc), 255n) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(List<&2, U32>, F.pow_ones(x, 0n, acc), acc, po_zero(x, acc, hx)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      ha
    case 1n+ +m:
      %Equal.sym(List<&2, U32>, F.pow_ones(x, 1n+m, acc), F.pow_ones(x, m, F.mul(F.sq(acc), x)), po_step(x, m, acc, hx)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      po_okb(one, h1, m, x, F.mul(F.sq(acc), x), hx, MW.mul_okb(one, h1, F.sq(acc), x, MW.sq_okb(one, h1, acc, ha), hx))

def pb_okb(+one: Nat, +h1: {one == 1n : Nat}, +b: Bool, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> {LM.okb(32n, F.pow_bit(b, x, acc), 255n) == True{} : Bool}:
  match b:
    case True{}:
      MW.mul_okb(one, h1, F.sq(acc), x, MW.sq_okb(one, h1, acc, ha), hx)
    case False{}:
      MW.sq_okb(one, h1, acc, ha)

def pbs_okb(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, Bool>, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> {LM.okb(32n, F.pow_bits(x, bs, acc), 255n) == True{} : Bool}:
  match bs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, F.pow_bits(x, Nil{}, acc), acc, pbs_nil(x, acc)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      ha
    case Con{+b, +bt}:
      %Equal.sym(List<&2, U32>, F.pow_bits(x, Con{b, bt}, acc), F.pow_bits(x, bt, F.pow_bit(b, x, acc)), pbs_con(x, b, bt, acc, hx)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      pbs_okb(one, h1, bt, x, F.pow_bit(b, x, acc), hx, pb_okb(one, h1, b, x, acc, hx, ha))

# ---- values ----

# acc^2 x
def step_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +acc: List<&2, U32>, +x: List<&2, U32>, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.mul(F.sq(acc), x)), Nat.mul(Nat.mul(FS.value(acc), FS.value(acc)), FS.value(x))):
  +A = FS.value(acc)
  +X = FS.value(x)
  +e1 = MW.mul_mod(one, h1, pp, hP, F.sq(acc), x, MW.sq_okb(one, h1, acc, ha), hx)
  +e2 = G.c_mul(pp, FS.value(F.sq(acc)), Nat.mul(A, A), X, X, MW.sq_mod(one, h1, pp, hP, acc, ha), G.c_refl(pp, X))
  G.c_trans(pp, FS.value(F.mul(F.sq(acc), x)), Nat.mul(FS.value(F.sq(acc)), X), Nat.mul(Nat.mul(A, A), X), e1, e2)

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

def po_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.pow_ones(x, n, acc)), Nat.mul(Nat.pow(FS.value(acc), WD.sc(n, one)), Nat.pow(FS.value(x), Fo(one, n)))):
  match n:
    case 0n:
      +A = FS.value(acc)
      +R = Nat.mul(Nat.pow(A, one), Nat.pow(FS.value(x), Fo(one, 0n)))
      %Equal.sym(List<&2, U32>, F.pow_ones(x, 0n, acc), acc, po_zero(x, acc, hx)) : G.ceq(pp, FS.value(_), R)
      +e0 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, one), Nat.pow(FS.value(x), t)), Fo(one, 0n), 0n, N.sub_self(one))
      G.c_eq(pp, A, R, Equal.sym(Nat, R, A, Equal.trans(Nat, R, Nat.mul(Nat.pow(A, one), 1n), A, e0, pow_one_one(one, h1, A))))
    case 1n+ +m:
      +A = FS.value(acc)
      +X = FS.value(x)
      +acc2 = F.mul(F.sq(acc), x)
      +S = WD.sc(m, one)
      +Fm = Fo(one, m)
      +ha2 = MW.mul_okb(one, h1, F.sq(acc), x, MW.sq_okb(one, h1, acc, ha), hx)
      +ih = po_val(one, h1, pp, hP, m, x, acc2, hx, ha2)
      %Equal.sym(List<&2, U32>, F.pow_ones(x, 1n+m, acc), F.pow_ones(x, m, acc2), po_step(x, m, acc, hx)) : G.ceq(pp, FS.value(_), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))))
      +e1 = G.c_mul(pp, Nat.pow(FS.value(acc2), S), Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm), Nat.pow(X, Fm), G.c_pow(pp, FS.value(acc2), Nat.mul(Nat.mul(A, A), X), S, step_c(one, h1, pp, hP, acc, x, ha, hx)), G.c_refl(pp, Nat.pow(X, Fm)))
      +e2 = sq_pow(A, X, S, Nat.pow(X, Fm), WD.sc(1n+m, one), M.sc_dbl(m, one))
      +e3 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), t), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm)), Nat.pow(X, Nat.add(S, Fm)), Equal.sym(Nat, Nat.pow(X, Nat.add(S, Fm)), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm)), NR.pow_add(X, S, Fm)))
      +fin = G.c_trans(pp, FS.value(F.pow_ones(x, m, acc2)), Nat.mul(Nat.pow(FS.value(acc2), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), ih,
        G.c_trans(pp, Nat.mul(Nat.pow(FS.value(acc2), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), e1, G.c_eq(pp, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Equal.trans(Nat, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), X), S), Nat.pow(X, Fm)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.mul(Nat.pow(X, S), Nat.pow(X, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), e2, e3))))
      G.c_trans(pp, FS.value(F.pow_ones(x, m, acc2)), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))), fin, G.c_eq(pp, Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Nat.add(S, Fm))), Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, Fo(one, 1n+m))), Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(A, WD.sc(1n+m, one)), Nat.pow(X, t)), Nat.add(S, Fm), Fo(one, 1n+m), fo_step(one, h1, m))))

def pb_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +b: Bool, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.pow_bit(b, x, acc)), Nat.mul(Nat.mul(FS.value(acc), FS.value(acc)), Nat.pow(FS.value(x), bexp(b)))):
  match b:
    case True{}:
      +A = FS.value(acc)
      +X = FS.value(x)
      G.c_trans(pp, FS.value(F.mul(F.sq(acc), x)), Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), step_c(one, h1, pp, hP, acc, x, ha, hx), G.c_eq(pp, Nat.mul(Nat.mul(A, A), X), Nat.mul(Nat.mul(A, A), Nat.pow(X, 1n)), Equal.cong(Nat, Nat, t => Nat.mul(Nat.mul(A, A), t), X, Nat.pow(X, 1n), Equal.sym(Nat, Nat.mul(X, 1n), X, NA.mul_one(X)))))
    case False{}:
      +A = FS.value(acc)
      G.c_trans(pp, FS.value(F.sq(acc)), Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), MW.sq_mod(one, h1, pp, hP, acc, ha), G.c_eq(pp, Nat.mul(A, A), Nat.mul(Nat.mul(A, A), 1n), Equal.sym(Nat, Nat.mul(Nat.mul(A, A), 1n), Nat.mul(A, A), NA.mul_one(Nat.mul(A, A)))))

# (a^2 x^e)^s y == a^(2 s) x^(e s) y
def bit_pow(+a: Nat, +x: Nat, +e: Nat, +s: Nat, +z: Nat, +s2: Nat, +hs: {Nat.add(s, s) == s2 : Nat}) -> {Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), Nat.pow(x, e)), s), Nat.pow(x, z)) == Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))) : Nat}:
  +e1 = sq_pow(a, Nat.pow(x, e), s, Nat.pow(x, z), s2, hs)
  +e2 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(a, s2), Nat.mul(t, Nat.pow(x, z))), Nat.pow(Nat.pow(x, e), s), Nat.pow(x, Nat.mul(e, s)), G.pow_pow(x, e, s))
  +e3 = Equal.cong(Nat, Nat, t => Nat.mul(Nat.pow(a, s2), t), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z)), Nat.pow(x, Nat.add(Nat.mul(e, s), z)), Equal.sym(Nat, Nat.pow(x, Nat.add(Nat.mul(e, s), z)), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z)), NR.pow_add(x, Nat.mul(e, s), z)))
  Equal.trans(Nat, Nat.mul(Nat.pow(Nat.mul(Nat.mul(a, a), Nat.pow(x, e)), s), Nat.pow(x, z)), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(Nat.pow(x, e), s), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))), e1, Equal.trans(Nat, Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(Nat.pow(x, e), s), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.mul(Nat.pow(x, Nat.mul(e, s)), Nat.pow(x, z))), Nat.mul(Nat.pow(a, s2), Nat.pow(x, Nat.add(Nat.mul(e, s), z))), e2, e3))

def pbs_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +bs: List<&2, Bool>, +x: List<&2, U32>, +acc: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.pow_bits(x, bs, acc)), Nat.mul(Nat.pow(FS.value(acc), WD.sc(blen(bs), one)), Nat.pow(FS.value(x), eb(one, bs)))):
  match bs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, F.pow_bits(x, Nil{}, acc), acc, pbs_nil(x, acc)) : G.ceq(pp, FS.value(_), Nat.mul(Nat.pow(FS.value(acc), one), 1n))
      G.c_eq(pp, FS.value(acc), Nat.mul(Nat.pow(FS.value(acc), one), 1n), Equal.sym(Nat, Nat.mul(Nat.pow(FS.value(acc), one), 1n), FS.value(acc), pow_one_one(one, h1, FS.value(acc))))
    case Con{+b, +bt}:
      +A = FS.value(acc)
      +X = FS.value(x)
      +acc2 = F.pow_bit(b, x, acc)
      +S = WD.sc(blen(bt), one)
      +Z = eb(one, bt)
      +E = bexp(b)
      +ha2 = pb_okb(one, h1, b, x, acc, hx, ha)
      +ih = pbs_val(one, h1, pp, hP, bt, x, acc2, hx, ha2)
      %Equal.sym(List<&2, U32>, F.pow_bits(x, Con{b, bt}, acc), F.pow_bits(x, bt, acc2), pbs_con(x, b, bt, acc, hx)) : G.ceq(pp, FS.value(_), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))))
      +e1 = G.c_mul(pp, Nat.pow(FS.value(acc2), S), Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z), Nat.pow(X, Z), G.c_pow(pp, FS.value(acc2), Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S, pb_val(one, h1, pp, hP, b, x, acc, hx, ha)), G.c_refl(pp, Nat.pow(X, Z)))
      +e2 = bit_pow(A, X, E, S, Z, WD.sc(1n+blen(bt), one), M.sc_dbl(blen(bt), one))
      G.c_trans(pp, FS.value(F.pow_bits(x, bt, acc2)), Nat.mul(Nat.pow(FS.value(acc2), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), ih, G.c_trans(pp, Nat.mul(Nat.pow(FS.value(acc2), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), e1, G.c_eq(pp, Nat.mul(Nat.pow(Nat.mul(Nat.mul(A, A), Nat.pow(X, E)), S), Nat.pow(X, Z)), Nat.mul(Nat.pow(A, WD.sc(1n+blen(bt), one)), Nat.pow(X, Nat.add(Nat.mul(E, S), Z))), e2)))

# ---- x^(Fo(250) 2^k + e) ----

# pow_bits(x, bs, pow_ones(x, n, x)) == x^(Fo(n + 1) 2^len + eb)
def chain_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +n: Nat, +bs: List<&2, Bool>, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.pow_bits(x, bs, F.pow_ones(x, n, x))), Nat.pow(FS.value(x), Nat.add(Nat.mul(Fo(one, 1n+n), WD.sc(blen(bs), one)), eb(one, bs)))):
  +X = FS.value(x)
  +a1 = F.pow_ones(x, n, x)
  +F2 = Fo(one, 1n+n)
  +S = WD.sc(blen(bs), one)
  +ha1 = po_okb(one, h1, n, x, x, hx, hx)
  +e1 = po_val(one, h1, pp, hP, n, x, x, hx, hx)
  +e1b = Equal.trans(Nat, Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, Nat.add(WD.sc(n, one), Fo(one, n))), Nat.pow(X, F2), Equal.sym(Nat, Nat.pow(X, Nat.add(WD.sc(n, one), Fo(one, n))), Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), NR.pow_add(X, WD.sc(n, one), Fo(one, n))), Equal.cong(Nat, Nat, t => Nat.pow(X, t), Nat.add(WD.sc(n, one), Fo(one, n)), F2, fo_step(one, h1, n)))
  +v1 = G.c_trans(pp, FS.value(a1), Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, F2), e1, G.c_eq(pp, Nat.mul(Nat.pow(X, WD.sc(n, one)), Nat.pow(X, Fo(one, n))), Nat.pow(X, F2), e1b))
  +e2 = pbs_val(one, h1, pp, hP, bs, x, a1, hx, ha1)
  +e3 = G.c_mul(pp, Nat.pow(FS.value(a1), S), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs)), Nat.pow(X, eb(one, bs)), G.c_pow(pp, FS.value(a1), Nat.pow(X, F2), S, v1), G.c_refl(pp, Nat.pow(X, eb(one, bs))))
  +e4 = Equal.trans(Nat, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Equal.cong(Nat, Nat, t => Nat.mul(t, Nat.pow(X, eb(one, bs))), Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, Nat.mul(F2, S)), G.pow_pow(X, F2, S)), Equal.sym(Nat, Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), Nat.mul(Nat.pow(X, Nat.mul(F2, S)), Nat.pow(X, eb(one, bs))), NR.pow_add(X, Nat.mul(F2, S), eb(one, bs))))
  G.c_trans(pp, FS.value(F.pow_bits(x, bs, a1)), Nat.mul(Nat.pow(FS.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e2, G.c_trans(pp, Nat.mul(Nat.pow(FS.value(a1), S), Nat.pow(X, eb(one, bs))), Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e3, G.c_eq(pp, Nat.mul(Nat.pow(Nat.pow(X, F2), S), Nat.pow(X, eb(one, bs))), Nat.pow(X, Nat.add(Nat.mul(F2, S), eb(one, bs))), e4)))

# ---- the exponents ----

def cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  NR.add_cancel(c, a, b, Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(c, b), NA.add_comm(c, a), Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(c, b), e, NA.add_comm(b, c))))

# 32 Fo(250) + 32 == p + 19
def f32(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {Nat.add(Nat.mul(Fo(one, 250n), 32n), 32n) == Nat.add(1n+pp, 19n) : Nat}:
  +F2 = Fo(one, 250n)
  +e1 = Equal.trans(Nat, Nat.add(Nat.mul(F2, 32n), 32n), Nat.add(Nat.mul(F2, 32n), Nat.mul(one, 32n)), Nat.mul(Nat.add(F2, one), 32n), M.cong_r(Nat.mul(F2, 32n), 32n, Nat.mul(one, 32n), Equal.sym(Nat, Nat.mul(one, 32n), 32n, K.one_k(one, h1, 32n))), Equal.sym(Nat, Nat.mul(Nat.add(F2, one), 32n), Nat.add(Nat.mul(F2, 32n), Nat.mul(one, 32n)), NA.mul_add_right(F2, one, 32n)))
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

def inv_okb(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {LM.okb(32n, F.inv(x), 255n) == True{} : Bool}:
  pbs_okb(one, h1, inv_bits(), x, F.pow_ones(x, 249n, x), hx, po_okb(one, h1, 249n, x, x, hx, hx))

def p58_okb(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> {LM.okb(32n, F.pow_p58(x), 255n) == True{} : Bool}:
  pbs_okb(one, h1, p58_bits(), x, F.pow_ones(x, 249n, x), hx, po_okb(one, h1, 249n, x, x, hx, hx))

def inv_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.inv(x)), Nat.pow(FS.value(x), Nat.sub(1n+pp, 2n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(inv_bits()), one)), eb(one, inv_bits()))
  G.c_trans(pp, FS.value(F.inv(x)), Nat.pow(FS.value(x), ex), Nat.pow(FS.value(x), Nat.sub(1n+pp, 2n)), chain_val(one, h1, pp, hP, 249n, inv_bits(), x, hx), G.c_eq(pp, Nat.pow(FS.value(x), ex), Nat.pow(FS.value(x), Nat.sub(1n+pp, 2n)), Equal.cong(Nat, Nat, t => Nat.pow(FS.value(x), t), ex, Nat.sub(1n+pp, 2n), inv_exp(one, h1, pp, hP))))

def p58_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +x: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}) -> G.ceq(pp, FS.value(F.pow_p58(x)), Nat.pow(FS.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n))):
  +ex = Nat.add(Nat.mul(Fo(one, 250n), WD.sc(blen(p58_bits()), one)), eb(one, p58_bits()))
  G.c_trans(pp, FS.value(F.pow_p58(x)), Nat.pow(FS.value(x), ex), Nat.pow(FS.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), chain_val(one, h1, pp, hP, 249n, p58_bits(), x, hx), G.c_eq(pp, Nat.pow(FS.value(x), ex), Nat.pow(FS.value(x), Nat.div(Nat.sub(1n+pp, 5n), 8n)), Equal.cong(Nat, Nat, t => Nat.pow(FS.value(x), t), ex, Nat.div(Nat.sub(1n+pp, 5n), 8n), p58_exp(one, h1, pp, hP))))
