import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/instances.bend as SI
import ../../../spec/math/generic.bend as SG
import ../../../src/math/instances.bend as I
import ../../../src/math/num.bend as NM
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/u32half.bend as UH
import ../../lib/u32alg.bend as A
import ../../lib/word.bend as WD
import ../../lib/logic.bend as L
import ../../lib/lemmas/spec/numeric.bend as S
import ../u64/u64.bend as P64
import ./u32.bend as U32P
import ./width.bend as WW
import ../u64/u64div.bend as PD
import ../natural/arith.bend as NA
import ../../lib/arith.bend as AR
import ./w64mul.bend as W64M
import ./w64div.bend as W64D
import ./w64sqrt.bend as W64S
import ../../../src/math/w64.bend as X
import ../../../spec/math/w64.bend as SW

# The U32 instance (src/math/instances.bend) against spec/math/instances.bend:
# the model (value below 2^32, round trip) and the laws of every operation
# and test that do not go through w64.bend (those are in u32w64.bend).
# Width 32 stays symbolic (k with k == 32) inside the proofs: the checker
# cannot expand 2^32.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- the model ----

def vb_k(+k: Nat, +hk: {k == 32n : Nat}, +x: U32) -> {C.fits(k, v(x)) == True{} : Bool}:
  %Equal.sym(Bool, C.fits(k, v(x)), Nat.is_lt(v(x), C.pow2(k)), WW.fits_lt(k, v(x))) : {_ == True{} : Bool}
  U32P.val_lt(1n, {==}, k, hk, x)

# every U32 value fits 32 bits
def vb(+x: U32) -> {C.fits(32n, v(x)) == True{} : Bool}:
  vb_k(32n, {==}, x)

def lt_k(+k: Nat, +n: Nat, +h: {C.fits(k, n) == True{} : Bool}) -> {Nat.is_lt(n, C.pow2(k)) == True{} : Bool}:
  %WW.fits_lt(k, n) : {_ == True{} : Bool}
  h

def vo_k(+k: Nat, +hk: {k == 32n : Nat}, +n: Nat, +h: {C.fits(k, n) == True{} : Bool}) -> {v(U32.from_nat(n)) == n : Nat}:
  U.to_nat_from_nat(n, k, U32P.le_k(k, hk), lt_k(k, n, h))

# a value that fits is the value of its U32
def vo(+n: Nat, +h: {C.fits(32n, n) == True{} : Bool}) -> {v(U32.from_nat(n)) == n : Nat}:
  vo_k(32n, {==}, n, h)

def rt(+x: U32) -> {U32.from_nat(v(x)) == x : U32}:
  U32P.round_trip(x)

# ---- tests ----

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  U32P.true_ne_false(h)

def is_zero_c(+a: U32, +c: Bool, +hc: {U32.is_zero(a) == c : Bool}, +n: Nat, +hn: {v(a) == n : Nat}) -> {c == Nat.is_eq(v(a), 0n) : Bool}:
  match c:
    case True{}:
      %Equal.sym(U32, a, 0, A.eq_of(a, 0, hc)) : {True{} == Nat.is_eq(v(_), 0n) : Bool}
      {==}
    case False{}:
      match n:
        case 0n:
          +hz = L.subst(U32, z => {U32.is_zero(z) == True{} : Bool}, 0, a, Equal.sym(U32, a, 0, U.injective(a, 0, hn)), {==})
          Empty.absurd({False{} == Nat.is_eq(v(a), 0n) : Bool}, true_ne_false(Equal.trans(Bool, True{}, U32.is_zero(a), False{}, Equal.sym(Bool, U32.is_zero(a), True{}, hz), hc)))
        case 1n+ +p:
          %Equal.sym(Nat, v(a), 1n+p, hn) : {False{} == Nat.is_eq(_, 0n) : Bool}
          {==}

# U32.is_zero is the zero test on the value
def zero_nat(+a: U32) -> {U32.is_zero(a) == Nat.is_eq(v(a), 0n) : Bool}:
  is_zero_c(a, U32.is_zero(a), {==}, v(a), {==})

# U32 equality is equality of the values
def eq_c(+x: U32, +y: U32, +c: Bool, +hc: {U32.is_eq(x, y) == c : Bool}, +d: Bool, +hd: {Nat.is_eq(v(x), v(y)) == d : Bool}) -> {c == d : Bool}:
  match c d:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      +e = A.eq_of(x, y, hc)
      +hd2 = L.subst(U32, z => {Nat.is_eq(v(x), v(z)) == False{} : Bool}, y, x, Equal.sym(U32, x, y, e), hd)
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_eq(v(x), v(x)), False{}, Equal.sym(Bool, Nat.is_eq(v(x), v(x)), True{}, N.is_eq_refl(v(x))), hd2)))
    case False{} True{}:
      +e = U.injective(x, y, N.eq_from_is_eq(v(x), v(y), hd))
      +hc2 = L.subst(U32, z => {U32.is_eq(x, z) == False{} : Bool}, y, x, Equal.sym(U32, x, y, e), hc)
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, U32.is_eq(x, x), False{}, Equal.sym(Bool, U32.is_eq(x, x), True{}, A.eq_refl(x)), hc2)))

def eq_nat(+x: U32, +y: U32) -> {U32.is_eq(x, y) == Nat.is_eq(v(x), v(y)) : Bool}:
  eq_c(x, y, U32.is_eq(x, y), {==}, Nat.is_eq(v(x), v(y)), {==})

# the carry of an addition is "the sum does not fit"
def carry_fits(+k: Nat, +s: Nat, +n: Nat, +c: Bool, +e: {Nat.add(s, WD.sc(k, S.bit_value(c))) == n : Nat}, +hs: {Nat.is_lt(s, C.pow2(k)) == True{} : Bool}) -> {c == Bool.not(C.fits(k, n)) : Bool}:
  match c:
    case False{}:
      %Equal.sym(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), WW.fits_lt(k, n)) : {False{} == Bool.not(_) : Bool}
      %e : {False{} == Bool.not(Nat.is_lt(_, C.pow2(k))) : Bool}
      %Equal.sym(Nat, WD.sc(k, 0n), 0n, A.sc_zero(k)) : {False{} == Bool.not(Nat.is_lt(Nat.add(s, _), C.pow2(k))) : Bool}
      %Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)) : {False{} == Bool.not(Nat.is_lt(_, C.pow2(k))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(s, C.pow2(k)), True{}, hs) : {False{} == Bool.not(_) : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), WW.fits_lt(k, n)) : {True{} == Bool.not(_) : Bool}
      %e : {True{} == Bool.not(Nat.is_lt(_, C.pow2(k))) : Bool}
      %U.pow2_scale(k) : {True{} == Bool.not(Nat.is_lt(Nat.add(s, _), C.pow2(k))) : Bool}
      +le = L.subst(Nat, z => {Nat.is_le(C.pow2(k), z) == True{} : Bool}, Nat.add(C.pow2(k), s), Nat.add(s, C.pow2(k)), N.add_comm(C.pow2(k), s), N.le_add_right(C.pow2(k), s))
      %Equal.sym(Bool, Nat.is_lt(Nat.add(s, C.pow2(k)), C.pow2(k)), False{}, N.le_not_lt(Nat.add(s, C.pow2(k)), C.pow2(k), le)) : {True{} == Bool.not(_) : Bool}
      {==}

# ---- the instance laws of spec/math/instances.bend at U32 ----

def ops_zero() -> SI.Ops.zero(~U32, ~I.u32_op, ~SG.u32_val):
  {==}

def ops_one() -> SI.Ops.one(~U32, ~I.u32_op, ~SG.u32_val):
  {==}

def ops_abs(+a: U32) -> SI.Ops.abs(~U32, ~I.u32_op, a):
  {==}

def tests_lt(+a: U32, +b: U32) -> SI.Tests.lt(~U32, ~I.u32_is, ~SG.u32_val, a, b):
  U.is_lt_nat(a, b)

def tests_is_zero(+a: U32) -> SI.Tests.is_zero(~U32, ~I.u32_is, ~SG.u32_val, a):
  zero_nat(a)

def ops_sub(+a: U32, +b: U32, +h: {Nat.is_le(SG.u32_val(b), SG.u32_val(a)) == True{} : Bool}) -> SI.Ops.sub(~U32, ~I.u32_op, ~SG.u32_val, a, b, h):
  U.sub_nat(a, b, h)

def nz(+b: U32, +h: {Nat.is_eq(SG.u32_val(b), 0n) == False{} : Bool}) -> {U32.is_zero(b) == False{} : Bool}:
  Equal.trans(Bool, U32.is_zero(b), Nat.is_eq(v(b), 0n), False{}, zero_nat(b), h)

def ops_quot(+a: U32, +b: U32, +h: {Nat.is_eq(SG.u32_val(b), 0n) == False{} : Bool}) -> SI.Ops.quot(~U32, ~I.u32_op, ~SG.u32_val, a, b, h):
  UD.div_nat(a, b, nz(b, h))

def ops_rem(+a: U32, +b: U32, +h: {Nat.is_eq(SG.u32_val(b), 0n) == False{} : Bool}) -> SI.Ops.rem(~U32, ~I.u32_op, ~SG.u32_val, a, b, h):
  UD.mod_nat(a, b, nz(b, h))

def hlf_div2(+n: Nat) -> {UH.hlf(n) == Nat.div(n, 2n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      %Equal.sym(Nat, Nat.div(Nat.add(2n, q), 2n), 1n+Nat.div(q, 2n), N.div2_step(q)) : {1n+UH.hlf(q) == _ : Nat}
      N.succ_cong(UH.hlf(q), Nat.div(q, 2n), hlf_div2(q))

def ops_half(+a: U32) -> SI.Ops.half(~U32, ~I.u32_op, ~SG.u32_val, a):
  Equal.trans(Nat, v(U32.shr(a)), UH.hlf(v(a)), Nat.div(v(a), 2n), UH.shr_value(a), hlf_div2(v(a)))

def carry_of(+a: U32, +b: U32, +h: {I.u32_is(NM.AddOver{a, b}) == False{} : Bool}) -> {P64.carry32(a, b) == False{} : Bool}:
  Equal.trans(Bool, P64.carry32(a, b), U32.is_lt(U32.add(a, b), a), False{}, Equal.sym(Bool, U32.is_lt(U32.add(a, b), a), P64.carry32(a, b), P64.add_lt(a, b)), h)

def ops_add(+a: U32, +b: U32, +h: {I.u32_is(NM.AddOver{a, b}) == False{} : Bool}) -> SI.Ops.add(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, a, b, h):
  +e = L.subst(Bool, c => {Nat.add(UD.v(U32.add(a, b)), WD.sc(32n, S.bit_value(c))) == Nat.add(UD.v(a), UD.v(b)) : Nat}, P64.carry32(a, b), False{}, carry_of(a, b, h), P64.add_cons(a, b))
  Equal.trans(Nat, v(U32.add(a, b)), Nat.add(v(U32.add(a, b)), 0n), Nat.add(v(a), v(b)), Equal.sym(Nat, Nat.add(v(U32.add(a, b)), 0n), v(U32.add(a, b)), N.add_zero(v(U32.add(a, b)))), e)

def add_over_k(+k: Nat, +hk: {k == 32n : Nat}, +a: U32, +b: U32) -> {P64.carry32(a, b) == Bool.not(C.fits(k, Nat.add(v(a), v(b)))) : Bool}:
  +e = L.subst(Nat, z => {Nat.add(UD.v(U32.add(a, b)), WD.sc(z, S.bit_value(P64.carry32(a, b)))) == Nat.add(UD.v(a), UD.v(b)) : Nat}, 32n, k, Equal.sym(Nat, k, 32n, hk), P64.add_cons(a, b))
  carry_fits(k, v(U32.add(a, b)), Nat.add(v(a), v(b)), P64.carry32(a, b), e, U32P.val_lt(1n, {==}, k, hk, U32.add(a, b)))

def tests_add_over(+a: U32, +b: U32) -> SI.Tests.add_over(~U32, ~I.u32_is, ~SG.u32_val, 32n, a, b):
  %Equal.sym(Bool, U32.is_lt(U32.add(a, b), a), P64.carry32(a, b), P64.add_lt(a, b)) : {_ == Bool.not(C.fits(32n, Nat.add(v(a), v(b)))) : Bool}
  add_over_k(32n, {==}, a, b)

# ---- odd: the low bit ----

def dbl(+h: Nat) -> {Nat.mul(h, 2n) == Nat.double(h) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.mul(p, 2n), Nat.double(p), dbl(p)) : {Nat.add(2n, _) == Nat.double(1n+p) : Nat}
      {==}

# r + 2h mod 2 is the bit r
def mod2_bit(+r: Nat, +h: Nat, +hr: {Nat.is_lt(r, 2n) == True{} : Bool}) -> {r == Nat.mod(Nat.add(r, Nat.double(h)), 2n) : Nat}:
  match r:
    case 0n:
      %dbl(h) : {0n == Nat.mod(_, 2n) : Nat}
      %N.add_zero(Nat.mul(h, 2n)) : {0n == Nat.mod(_, 2n) : Nat}
      Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(h, 2n), 0n), 2n), 0n, NA.absorb(1n, h, 0n))
    case 1n:
      %dbl(h) : {1n == Nat.mod(1n+_, 2n) : Nat}
      %N.add_zero(Nat.mul(h, 2n)) : {1n == Nat.mod(1n+_, 2n) : Nat}
      %N.add_succ(Nat.mul(h, 2n), 0n) : {1n == Nat.mod(_, 2n) : Nat}
      Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(h, 2n), 1n), 2n), 1n, NA.absorb(1n, h, 1n))
    case 2n+ +q:
      Empty.absurd({2n+q == Nat.mod(Nat.add(2n+q, Nat.double(h)), 2n) : Nat}, N.lt_zero_absurd(q, hr))

def odd_val(+a: U32) -> {v(U32.and(a, 1)) == Nat.mod(v(a), 2n) : Nat}:
  +e = PD.and32(1n, a, 1, {==})
  %Equal.sym(Nat, v(a), Nat.add(v(U32.and(a, 1)), Nat.double(PD.hp32(1n, a))), e) : {v(U32.and(a, 1)) == Nat.mod(_, 2n) : Nat}
  mod2_bit(v(U32.and(a, 1)), PD.hp32(1n, a), PD.and32_lt(1n, 1n, {==}, a, 1, {==}))

def tests_odd(+a: U32) -> SI.Tests.odd(~U32, ~I.u32_is, ~SG.u32_val, a):
  %Equal.sym(Bool, U32.is_eq(U32.and(a, 1), 1), Nat.is_eq(v(U32.and(a, 1)), v(1)), eq_nat(U32.and(a, 1), 1)) : {_ == Nat.is_eq(Nat.mod(v(a), 2n), 1n) : Bool}
  %Equal.sym(Nat, v(U32.and(a, 1)), Nat.mod(v(a), 2n), odd_val(a)) : {Nat.is_eq(_, 1n) == Nat.is_eq(Nat.mod(v(a), 2n), 1n) : Bool}
  {==}

# ---- multiplication through the full product ----

def not_false(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(h))

# fits(k, lo + 2^k hi) exactly when hi == 0 (lo < 2^k)
def fits_split(+k: Nat, +lo: Nat, +hi: Nat, +hl: {Nat.is_lt(lo, C.pow2(k)) == True{} : Bool}) -> {C.fits(k, Nat.add(lo, WD.sc(k, hi))) == Nat.is_eq(hi, 0n) : Bool}:
  match hi:
    case 0n:
      %Equal.sym(Nat, WD.sc(k, 0n), 0n, A.sc_zero(k)) : {C.fits(k, Nat.add(lo, _)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(lo, 0n), lo, N.add_zero(lo)) : {C.fits(k, _) == True{} : Bool}
      %Equal.sym(Bool, C.fits(k, lo), Nat.is_lt(lo, C.pow2(k)), WW.fits_lt(k, lo)) : {_ == True{} : Bool}
      hl
    case 1n+ +h:
      %Equal.sym(Bool, C.fits(k, Nat.add(lo, WD.sc(k, 1n+h))), Nat.is_lt(Nat.add(lo, WD.sc(k, 1n+h)), C.pow2(k)), WW.fits_lt(k, Nat.add(lo, WD.sc(k, 1n+h)))) : {_ == False{} : Bool}
      +p1 = L.subst(Nat, z => {Nat.is_le(z, WD.sc(k, 1n+h)) == True{} : Bool}, WD.sc(k, 1n), C.pow2(k), Equal.sym(Nat, C.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)), AR.sc_le(k, 1n, 1n+h, N.zero_le(h)))
      +p2 = L.subst(Nat, z => {Nat.is_le(WD.sc(k, 1n+h), z) == True{} : Bool}, Nat.add(WD.sc(k, 1n+h), lo), Nat.add(lo, WD.sc(k, 1n+h)), N.add_comm(WD.sc(k, 1n+h), lo), N.le_add_right(WD.sc(k, 1n+h), lo))
      N.le_not_lt(Nat.add(lo, WD.sc(k, 1n+h)), C.pow2(k), N.le_trans(C.pow2(k), WD.sc(k, 1n+h), Nat.add(lo, WD.sc(k, 1n+h)), p1, p2))

def hi_zero(+a: U32, +b: U32, +h: {I.u32_is(NM.MulOver{a, b}) == False{} : Bool}) -> {v(X.hi(X.mul32(a, b))) == 0n : Nat}:
  +z = not_false(U32.is_zero(X.hi(X.mul32(a, b))), h)
  N.eq_from_is_eq(v(X.hi(X.mul32(a, b))), 0n, Equal.trans(Bool, Nat.is_eq(v(X.hi(X.mul32(a, b))), 0n), U32.is_zero(X.hi(X.mul32(a, b))), True{}, Equal.sym(Bool, U32.is_zero(X.hi(X.mul32(a, b))), Nat.is_eq(v(X.hi(X.mul32(a, b))), 0n), zero_nat(X.hi(X.mul32(a, b)))), z))

# the product value as the two limbs of the full product
def prod_limbs(+a: U32, +b: U32) -> {Nat.add(v(X.lo(X.mul32(a, b))), WD.sc(32n, v(X.hi(X.mul32(a, b))))) == Nat.mul(v(a), v(b)) : Nat}:
  e = W64M.mul32_value(a, b)
  +lo = X.lo(X.mul32(a, b))
  +hi = X.hi(X.mul32(a, b))
  Equal.trans(Nat, Nat.add(v(lo), WD.sc(32n, v(hi))), Nat.add(v(lo), C.shift(32n, v(hi))), Nat.mul(v(a), v(b)), W64M.cong_r(v(lo), WD.sc(32n, v(hi)), C.shift(32n, v(hi)), Equal.sym(Nat, C.shift(32n, v(hi)), WD.sc(32n, v(hi)), W64M.shift_sc(32n, v(hi)))), e)

def ops_mul_one(+one: Nat, +h1: {one == 1n : Nat}, +a: U32, +b: U32, +h: {I.u32_is(NM.MulOver{a, b}) == False{} : Bool}) -> {v(U32.mul(a, b)) == Nat.mul(v(a), v(b)) : Nat}:
  +lo = X.lo(X.mul32(a, b))
  +hi = X.hi(X.mul32(a, b))
  +e0 = Equal.trans(Nat, v(lo), Nat.add(v(lo), 0n), Nat.add(v(lo), WD.sc(32n, v(hi))), Equal.sym(Nat, Nat.add(v(lo), 0n), v(lo), N.add_zero(v(lo))), W64M.cong_r(v(lo), 0n, WD.sc(32n, v(hi)), Equal.trans(Nat, 0n, WD.sc(32n, 0n), WD.sc(32n, v(hi)), Equal.sym(Nat, WD.sc(32n, 0n), 0n, A.sc_zero(32n)), W64M.cong_sc(32n, 0n, v(hi), Equal.sym(Nat, v(hi), 0n, hi_zero(a, b, h))))))
  +ep = Equal.trans(Nat, v(lo), Nat.add(v(lo), WD.sc(32n, v(hi))), Nat.mul(v(a), v(b)), e0, prod_limbs(a, b))
  +lt = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, v(lo), Nat.mul(v(a), v(b)), ep, UD.vb(one, h1, lo))
  PD.mul32(one, h1, a, b, lt)

def ops_mul(+a: U32, +b: U32, +h: {I.u32_is(NM.MulOver{a, b}) == False{} : Bool}) -> SI.Ops.mul(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, a, b, h):
  ops_mul_one(1n, {==}, a, b, h)

def mul_over_k(+k: Nat, +hk: {k == 32n : Nat}, +a: U32, +b: U32) -> {U32.is_zero(X.hi(X.mul32(a, b))) == C.fits(k, Nat.mul(v(a), v(b))) : Bool}:
  +lo = X.lo(X.mul32(a, b))
  +hi = X.hi(X.mul32(a, b))
  +ek = L.subst(Nat, z => {Nat.add(v(lo), WD.sc(z, v(hi))) == Nat.mul(v(a), v(b)) : Nat}, 32n, k, Equal.sym(Nat, k, 32n, hk), prod_limbs(a, b))
  %ek : {U32.is_zero(hi) == C.fits(k, _) : Bool}
  %Equal.sym(Bool, C.fits(k, Nat.add(v(lo), WD.sc(k, v(hi)))), Nat.is_eq(v(hi), 0n), fits_split(k, v(lo), v(hi), U32P.val_lt(1n, {==}, k, hk, lo))) : {U32.is_zero(hi) == _ : Bool}
  zero_nat(hi)

def tests_mul_over(+a: U32, +b: U32) -> SI.Tests.mul_over(~U32, ~I.u32_is, ~SG.u32_val, 32n, a, b):
  Equal.cong(Bool, Bool, t => Bool.not(t), U32.is_zero(X.hi(X.mul32(a, b))), C.fits(32n, Nat.mul(v(a), v(b))), mul_over_k(32n, {==}, a, b))

# ---- mulmod: the product reduced by the 64 / 32 remainder ----

def pos_nz(+x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_eq(y, 0n) == False{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, N.lt_zero_absurd(x, h))
    case 1n+yp:
      {==}

def ops_mulmod(+a: U32, +b: U32, +m: U32, +ha: {Nat.is_lt(SG.u32_val(a), SG.u32_val(m)) == True{} : Bool}, +hb: {Nat.is_lt(SG.u32_val(b), SG.u32_val(m)) == True{} : Bool}) -> SI.Ops.mulmod(~U32, ~I.u32_op, ~SG.u32_val, a, b, m, ha, hb):
  e1 = W64D.mod32_value(X.mul32(a, b), m, nz(m, pos_nz(v(a), v(m), ha)))
  e2 = W64M.mul32_value(a, b)
  Equal.trans(Nat, v(X.mod32(X.mul32(a, b), m)), Nat.mod(SW.value(X.mul32(a, b)), v(m)), Nat.mod(Nat.mul(v(a), v(b)), v(m)), e1, Equal.cong(Nat, Nat, t => Nat.mod(t, v(m)), SW.value(X.mul32(a, b)), Nat.mul(v(a), v(b)), e2))

# ---- pow2: the table is the words with one bit set ----

def pw_table(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {X.pow2(k) == U32{WD.pw(32n, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n+ +j:
      Empty.absurd({X.pow2(32n+j) == U32{WD.pw(32n, 32n+j)} : U32}, N.lt_zero_absurd(j, hk))

def ops_pow2(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> SI.Ops.pow2(~U32, ~I.u32_op, ~SG.u32_val, 32n, k, hk):
  %Equal.sym(U32, X.pow2(k), U32{WD.pw(32n, k)}, pw_table(k, hk)) : {v(_) == C.pow2(k) : Nat}
  %Equal.sym(Nat, C.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)) : {v(U32{WD.pw(32n, k)}) == _ : Nat}
  PD.pow32(k, hk, 1n, {==}, U32{WD.pw(32n, k)}, {==})

# ---- sqrt: the exact integer square root from any F32 estimate ----

def ops_sqrt(+a: U32) -> SI.Ops.sqrt(~U32, ~I.u32_op, ~SG.u32_val, a):
  W64S.isqrt32_value(a)
