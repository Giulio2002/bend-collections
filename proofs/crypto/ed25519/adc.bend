import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/poly.bend as PL
import ../curve25519/consts.bend as K

# Certified additions of constant digit strings: adc_ok checks, digit by
# digit, x + y + c == z + 256 c' (small numbers the checker computes), and
# then valo(xs) + valo(ys) + c == valo(zs) + 2^(8 n) c_out holds with every
# side kept open in the symbolic one (the constants' values are never formed).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def adc_ok(xs: List<&2, U32>, ys: List<&2, U32>, zs: List<&2, U32>, +c: Nat, +co: Nat) -> Bool:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      Nat.is_eq(c, co)
    case Con{x, xt} Con{y, yt} Con{z, zt}:
      +s = Nat.add(Nat.add(U32.to_nat(x), U32.to_nat(y)), c)
      Bool.and(Nat.is_eq(Nat.mod(s, 256n), U32.to_nat(z)), adc_ok(xt, yt, zt, Nat.div(s, 256n), co))
    case _ _ _:
      False{}

# one digit: x + y + c == z + 256 c' scaled by one
def digit(+one: Nat, +x: Nat, +y: Nat, +c: Nat, +z: Nat, +hz: {Nat.mod(Nat.add(Nat.add(x, y), c), 256n) == z : Nat}) -> {Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)) == Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, Nat.div(Nat.add(Nat.add(x, y), c), 256n)))) : Nat}:
  +s = Nat.add(Nat.add(x, y), c)
  +q = Nat.div(s, 256n)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)), Nat.add(Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c)), Nat.mul(one, s), M.cong_l(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c), Equal.sym(Nat, Nat.mul(one, Nat.add(x, y)), Nat.add(Nat.mul(one, x), Nat.mul(one, y)), NA.mul_add_left(one, x, y))), Equal.sym(Nat, Nat.mul(one, s), Nat.add(Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c)), NA.mul_add_left(one, Nat.add(x, y), c)))
  +e2 = Equal.trans(Nat, s, Nat.add(Nat.mod(s, 256n), C.shift(8n, q)), Nat.add(z, C.shift(8n, q)), Equal.sym(Nat, Nat.add(Nat.mod(s, 256n), C.shift(8n, q)), s, LM.dm256(s)), M.cong_l(Nat.mod(s, 256n), z, C.shift(8n, q), hz))
  +e3 = Equal.trans(Nat, Nat.mul(one, s), Nat.mul(one, Nat.add(z, C.shift(8n, q))), Nat.add(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q))), Equal.cong(Nat, Nat, t => Nat.mul(one, t), s, Nat.add(z, C.shift(8n, q)), e2), NA.mul_add_left(one, z, C.shift(8n, q)))
  +e4 = M.cong_r(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q)), C.shift(8n, Nat.mul(one, q)), Equal.sym(Nat, WD.sc(8n, Nat.mul(one, q)), Nat.mul(one, WD.sc(8n, q)), PL.sc_mul_l(8n, one, q)))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)), Nat.mul(one, s), Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, q))), e1, Equal.trans(Nat, Nat.mul(one, s), Nat.add(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q))), Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, q))), e3, e4))

# (a + A') + (b + B') + c == (a + b + c) + (A' + B') rearranged
def swap5(+a: Nat, +b: Nat, +c: Nat, +X: Nat, +Y: Nat) -> {Nat.add(Nat.add(Nat.add(a, X), Nat.add(b, Y)), c) == Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)) : Nat}:
  +e1 = M.cong_l(Nat.add(Nat.add(a, X), Nat.add(b, Y)), Nat.add(Nat.add(a, b), Nat.add(X, Y)), c, M.add4(a, X, b, Y))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, b), Nat.add(X, Y)), c), Nat.add(Nat.add(a, b), Nat.add(Nat.add(X, Y), c)), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), NA.add_assoc(Nat.add(a, b), Nat.add(X, Y), c), Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(Nat.add(X, Y), c)), Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(X, Y))), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), M.cong_r(Nat.add(a, b), Nat.add(Nat.add(X, Y), c), Nat.add(c, Nat.add(X, Y)), NA.add_comm(Nat.add(X, Y), c)), Equal.sym(Nat, Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(X, Y))), NA.add_assoc(Nat.add(a, b), c, Nat.add(X, Y)))))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, X), Nat.add(b, Y)), c), Nat.add(Nat.add(Nat.add(a, b), Nat.add(X, Y)), c), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), e1, e2)

def adc_val(+one: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>, +c: Nat, +co: Nat, +h: {adc_ok(xs, ys, zs, c, co) == True{} : Bool}) -> {Nat.add(Nat.add(K.valo(one, xs), K.valo(one, ys)), Nat.mul(one, c)) == Nat.add(K.valo(one, zs), LM.sh(xs, Nat.mul(one, co))) : Nat}:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      %N.eq_from_is_eq(c, co, h) : {Nat.add(Nat.add(0n, 0n), Nat.mul(one, c)) == Nat.add(0n, Nat.mul(one, _)) : Nat}
      {==}
    case Con{+x, +xt} Con{+y, +yt} Con{+z, +zt}:
      +s = Nat.add(Nat.add(v(x), v(y)), c)
      +q = Nat.div(s, 256n)
      +hz = N.eq_from_is_eq(Nat.mod(s, 256n), v(z), L.and_left(Nat.is_eq(Nat.mod(s, 256n), v(z)), adc_ok(xt, yt, zt, q, co), h))
      +ih = adc_val(one, xt, yt, zt, q, co, L.and_right(Nat.is_eq(Nat.mod(s, 256n), v(z)), adc_ok(xt, yt, zt, q, co), h))
      +X = K.valo(one, xt)
      +Y = K.valo(one, yt)
      +Z = K.valo(one, zt)
      +a = Nat.mul(one, v(x))
      +b = Nat.mul(one, v(y))
      +cc = Nat.mul(one, c)
      +e1 = swap5(a, b, cc, C.shift(8n, X), C.shift(8n, Y))
      +e2 = M.cong_add(Nat.add(Nat.add(a, b), cc), Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.mul(one, q))), Nat.add(C.shift(8n, X), C.shift(8n, Y)), C.shift(8n, Nat.add(X, Y)), digit(one, v(x), v(y), c, v(z), hz), M.sc_add(8n, X, Y))
      +e3 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.mul(one, v(z)), Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y)))), Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), NA.add_assoc(Nat.mul(one, v(z)), C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), M.cong_r(Nat.mul(one, v(z)), Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), Equal.trans(Nat, Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.mul(one, q), Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), M.sc_add(8n, Nat.mul(one, q), Nat.add(X, Y)), M.cong_sc(8n, Nat.add(Nat.mul(one, q), Nat.add(X, Y)), Nat.add(Nat.add(X, Y), Nat.mul(one, q)), NA.add_comm(Nat.mul(one, q), Nat.add(X, Y))))))
      +e4 = M.cong_r(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), M.cong_sc(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)), Nat.add(Z, LM.sh(xt, Nat.mul(one, co))), ih))
      +e5 = Equal.trans(Nat, Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.mul(one, v(z)), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), M.cong_r(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), Equal.sym(Nat, Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), M.sc_add(8n, Z, LM.sh(xt, Nat.mul(one, co))))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), Nat.add(Nat.mul(one, v(z)), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))), NA.add_assoc(Nat.mul(one, v(z)), C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))))
      Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, C.shift(8n, X)), Nat.add(b, C.shift(8n, Y))), cc), Nat.add(Nat.add(Nat.add(a, b), cc), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e1,
        Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, b), cc), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e2,
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e3,
            Equal.trans(Nat, Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), Nat.add(Nat.mul(one, v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.add(Nat.mul(one, v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e4, e5))))
    case Nil{} Nil{} Con{z, zt}:
      Empty.absurd({Nat.add(Nat.add(0n, 0n), Nat.mul(one, c)) == Nat.add(K.valo(one, Con{z, zt}), Nat.mul(one, co)) : Nat}, L.false_true(h))
    case Nil{} Con{y, yt} _:
      Empty.absurd({Nat.add(Nat.add(0n, K.valo(one, Con{y, yt})), Nat.mul(one, c)) == Nat.add(K.valo(one, zs), Nat.mul(one, co)) : Nat}, L.false_true(h))
    case Con{x, xt} Nil{} _:
      Empty.absurd({Nat.add(Nat.add(K.valo(one, Con{x, xt}), 0n), Nat.mul(one, c)) == Nat.add(K.valo(one, zs), LM.sh(Con{x, xt}, Nat.mul(one, co))) : Nat}, L.false_true(h))
    case Con{x, xt} Con{y, yt} Nil{}:
      Empty.absurd({Nat.add(Nat.add(K.valo(one, Con{x, xt}), K.valo(one, Con{y, yt})), Nat.mul(one, c)) == Nat.add(0n, LM.sh(Con{x, xt}, Nat.mul(one, co))) : Nat}, L.false_true(h))

# a limb list and a digit list agree
def digs_eq(xs: List<&2, U32>, ds: List<&2, Nat>) -> Bool:
  match xs ds:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{d, dt}:
      Bool.and(Nat.is_eq(U32.to_nat(x), d), digs_eq(xt, dt))
    case _ _:
      False{}

def valo_digits(+one: Nat, +xs: List<&2, U32>, +ds: List<&2, Nat>, +h: {digs_eq(xs, ds) == True{} : Bool}) -> {K.valo(one, xs) == FS.digits(one, ds) : Nat}:
  match xs ds:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xt} Con{+d, +dt}:
      +e1 = N.eq_from_is_eq(v(x), d, L.and_left(Nat.is_eq(v(x), d), digs_eq(xt, dt), h))
      +e2 = valo_digits(one, xt, dt, L.and_right(Nat.is_eq(v(x), d), digs_eq(xt, dt), h))
      M.cong_add(Nat.mul(one, v(x)), Nat.mul(one, d), C.shift(8n, K.valo(one, xt)), C.shift(8n, FS.digits(one, dt)), Equal.cong(Nat, Nat, z => Nat.mul(one, z), v(x), d, e1), M.cong_sc(8n, K.valo(one, xt), FS.digits(one, dt), e2))
    case Nil{} Con{d, dt}:
      Empty.absurd({0n == FS.digits(one, Con{d, dt}) : Nat}, L.false_true(h))
    case Con{x, xt} Nil{}:
      Empty.absurd({K.valo(one, Con{x, xt}) == 0n : Nat}, L.false_true(h))

def valo_u(+one: Nat, +xs: List<&2, U32>) -> {K.valo(one, xs) == FS.uvalue(one, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(Nat.mul(one, v(x)), C.shift(8n, K.valo(one, xt)), C.shift(8n, FS.uvalue(one, xt)), M.cong_sc(8n, K.valo(one, xt), FS.uvalue(one, xt), valo_u(one, xt)))

