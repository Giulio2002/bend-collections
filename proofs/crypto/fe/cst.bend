import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ./pw.bend as PW

# The radix of the callers of src/crypto/curve25519/fe.bend: FE.radix(one)
# is 2^17 in the symbolic one, and the run-time one X.one_of(xs) (a match
# on an input list, which keeps the checker from evaluating a closed 2^17)
# is 1.

def rad(+n: Nat, +x: Nat) -> {FE.pow2(n, x) == WD.sc(n, x) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => Nat.double(t), FE.pow2(m, x), WD.sc(m, x), rad(m, x))

def rad17(+one: Nat) -> {FE.radix(one) == WD.sc(17n, one) : Nat}:
  rad(17n, one)

def one_of_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {X.one_of(xs) == one : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, one, 1n, h1)
    case Con{h, t}:
      Equal.sym(Nat, one, 1n, h1)

def radix_of_eq(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {X.radix_of(xs) == WD.sc(17n, one) : Nat}:
  Equal.trans(Nat, FE.radix(X.one_of(xs)), FE.radix(one), WD.sc(17n, one), Equal.cong(Nat, Nat, t => FE.radix(t), X.one_of(xs), one, one_of_eq(one, h1, xs)), rad17(one))

# ---- small constants given by base-256 digits of the symbolic one ----

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def digits_eq(+one: Nat, +ds: List<&2, Nat>) -> {X.digits(one, ds) == FS.digits(one, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +dt}:
      M.cong_r(Nat.mul(one, d), FE.pow2(8n, X.digits(one, dt)), C.shift(8n, FS.digits(one, dt)), Equal.cong(Nat, Nat, t => FE.pow2(8n, t), X.digits(one, dt), FS.digits(one, dt), digits_eq(one, dt)))

# one d < 2^8 for a digit d < 256
def dig_lt(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(one, d), WD.sc(8n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(Nat.mul(o, d), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, t => {Nat.is_lt(t, WD.sc(8n, 1n)) == True{} : Bool}, d, Nat.mul(1n, d), sy(Nat.mul(1n, d), d, AR.one_mul(d)), hd))

# (a + b) + c == (a + c) + b
def swap_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  tr(Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b), NA.add_assoc(a, b, c), tr(Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), M.cong_r(a, Nat.add(b, c), Nat.add(c, b), NA.add_comm(b, c)), sy(Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), NA.add_assoc(a, c, b))))

# d0 + 2^8 (d1 + 2^8 1) < 2^17 for digits d0, d1 < 256
def dig3_lt(+one: Nat, +h1: {one == 1n : Nat}, +d0: Nat, +d1: Nat, +h0: {Nat.is_lt(d0, 256n) == True{} : Bool}, +hd1: {Nat.is_lt(d1, 256n) == True{} : Bool}) -> {Nat.is_lt(X.digits(one, [d0, d1, 1n]), WD.sc(17n, one)) == True{} : Bool}:
  +m0 = Nat.mul(one, d0)
  +m1 = Nat.mul(one, d1)
  +m2 = Nat.mul(one, 1n)
  +s8 = WD.sc(8n, one)
  +z = FE.pow2(8n, 0n)
  +e2 = tr(Nat.add(m2, z), m2, one, tr(Nat.add(m2, z), Nat.add(m2, 0n), m2, M.cong_r(m2, z, 0n, {==}), N.add_zero(m2)), NA.mul_one(one))
  +inner = Nat.add(m1, WD.sc(8n, Nat.add(m2, z)))
  +ei = M.cong_r(m1, WD.sc(8n, Nat.add(m2, z)), s8, M.cong_sc(8n, Nat.add(m2, z), one, e2))
  +l1 = L.subst(Nat, t => {Nat.is_le(Nat.add(t, one), WD.sc(9n, one)) == True{} : Bool}, Nat.add(m1, s8), inner, sy(inner, Nat.add(m1, s8), ei), L.subst(Nat, t => {Nat.is_le(t, WD.sc(9n, one)) == True{} : Bool}, Nat.add(Nat.add(m1, one), s8), Nat.add(Nat.add(m1, s8), one), swap_r(m1, one, s8), PW.add_le_dbl(Nat.add(m1, one), s8, 8n, one, PW.succ_le(one, h1, m1, s8, dig_lt(one, h1, d1, hd1)), N.le_refl(s8))))
  +l2 = L.subst(Nat, t => {Nat.is_le(t, WD.sc(17n, one)) == True{} : Bool}, WD.sc(8n, Nat.add(inner, one)), Nat.add(WD.sc(8n, inner), s8), sy(Nat.add(WD.sc(8n, inner), s8), WD.sc(8n, Nat.add(inner, one)), M.sc_add(8n, inner, one)), L.subst(Nat, t => {Nat.is_le(WD.sc(8n, Nat.add(inner, one)), t) == True{} : Bool}, WD.sc(8n, WD.sc(9n, one)), WD.sc(17n, one), M.sc_sc(8n, 9n, one), M.le_sc(8n, Nat.add(inner, one), WD.sc(9n, one), l1)))
  N.lt_le_trans(Nat.add(m0, WD.sc(8n, inner)), Nat.add(s8, WD.sc(8n, inner)), WD.sc(17n, one), N.lt_add_r2(m0, s8, WD.sc(8n, inner), dig_lt(one, h1, d0, h0)), L.subst(Nat, t => {Nat.is_le(t, WD.sc(17n, one)) == True{} : Bool}, Nat.add(WD.sc(8n, inner), s8), Nat.add(s8, WD.sc(8n, inner)), NA.add_comm(WD.sc(8n, inner), s8), l2))

# the constant k as an element: value k
def small_val(+k: Nat) -> {FV.value(FE.small(k)) == k : Nat}:
  N.add_zero(k)
