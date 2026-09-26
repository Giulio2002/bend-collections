import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./natcmp.bend as NC
import ./w64add.bend as WA
import ./w64dm.bend as DM
import ./f64cmp.bend as FC
import ./f64mul.bend as MU
import ./f64sqa.bend as AQ

# SoftFloat's f64_sqrt root search on 128 bits: the r * r > n * 2^64 test,
# the exactness test, and the final count-down to floor(sqrt(n * 2^64)).

def ltz(+l: Nat) -> {Nat.is_lt(0n, l) == Bool.not(Nat.is_eq(l, 0n)) : Bool}:
  match l:
    case 0n:
      {==}
    case 1n+ +lp:
      {==}

def eq_comm(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  Equal.trans(Bool, Nat.is_eq(a, b), Cmp.is_eq(SF.flip(Nat.cmp(a, b))), Nat.is_eq(b, a), FC.eqflip(Nat.cmp(a, b)), Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), SF.flip(Nat.cmp(a, b)), Nat.cmp(b, a), NC.cmp_flip(a, b)))

def and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# r * r > n * 2^64
def sqo(+nh: WU.U64, +r: WU.U64) -> {F.sq_over(nh, X.mul128(r, r)) == Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))) : Bool}:
  lt = WA.lt_value(nh, X.psnd(X.mul128(r, r)))
  eq = WA.eq_value(nh, X.psnd(X.mul128(r, r)))
  iz = WA.is_zero_value(X.pfst(X.mul128(r, r)))
  +e1 = Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(X.eq(nh, X.psnd(X.mul128(r, r))), F.nz(X.pfst(X.mul128(r, r))))), X.lt(nh, X.psnd(X.mul128(r, r))), Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), lt)
  +e2 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(t, F.nz(X.pfst(X.mul128(r, r))))), X.eq(nh, X.psnd(X.mul128(r, r))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), eq)
  +e3 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.not(t))), X.is_zero(X.pfst(X.mul128(r, r))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n), iz)
  +e4 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), t)), Bool.not(Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n)), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))), Equal.sym(Bool, Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))), Bool.not(Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n)), ltz(SW.value(X.pfst(X.mul128(r, r))))))
  +e5 = WW.lt_limbs(64n, 0n, SW.value(nh), SW.value(X.pfst(X.mul128(r, r))), SW.value(X.psnd(X.mul128(r, r))), {==}, DM.fit64(X.pfst(X.mul128(r, r))))
  +e6 = Equal.cong(Nat, Bool, z => Nat.is_lt(C.shift(64n, SW.value(nh)), z), Nat.add(SW.value(X.pfst(X.mul128(r, r))), C.shift(64n, SW.value(X.psnd(X.mul128(r, r))))), Nat.mul(SW.value(r), SW.value(r)), MU.m128g(r, r))
  Equal.trans(Bool, F.sq_over(nh, X.mul128(r, r)), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))))), Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))), Equal.trans(Bool, F.sq_over(nh, X.mul128(r, r)), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(X.eq(nh, X.psnd(X.mul128(r, r))), F.nz(X.pfst(X.mul128(r, r))))), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))))), e1, Equal.trans(Bool, Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(X.eq(nh, X.psnd(X.mul128(r, r))), F.nz(X.pfst(X.mul128(r, r))))), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), F.nz(X.pfst(X.mul128(r, r))))), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))))), e2, Equal.trans(Bool, Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), F.nz(X.pfst(X.mul128(r, r))))), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.not(Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n)))), Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))))), e3, e4))), Equal.trans(Bool, Bool.or(Nat.is_lt(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_lt(0n, SW.value(X.pfst(X.mul128(r, r)))))), Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.add(SW.value(X.pfst(X.mul128(r, r))), C.shift(64n, SW.value(X.psnd(X.mul128(r, r)))))), Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))), e5, e6))

# r * r == n * 2^64
def sqx(+nh: WU.U64, +r: WU.U64) -> {F.sq_exact(nh, X.mul128(r, r)) == Nat.is_eq(Nat.mul(SW.value(r), SW.value(r)), C.shift(64n, SW.value(nh))) : Bool}:
  eq = WA.eq_value(nh, X.psnd(X.mul128(r, r)))
  iz = WA.is_zero_value(X.pfst(X.mul128(r, r)))
  +e1 = Equal.cong(Bool, Bool, t => Bool.and(t, X.is_zero(X.pfst(X.mul128(r, r)))), X.eq(nh, X.psnd(X.mul128(r, r))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), eq)
  +e2 = Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), t), X.is_zero(X.pfst(X.mul128(r, r))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n), iz)
  +e3 = and_comm(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n))
  +e4 = Equal.cong(Bool, Bool, t => Bool.and(t, Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n), Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), eq_comm(SW.value(X.pfst(X.mul128(r, r))), 0n))
  +e5 = WW.eq_limbs(64n, 0n, SW.value(nh), SW.value(X.pfst(X.mul128(r, r))), SW.value(X.psnd(X.mul128(r, r))), {==}, DM.fit64(X.pfst(X.mul128(r, r))))
  +e6 = Equal.cong(Nat, Bool, z => Nat.is_eq(C.shift(64n, SW.value(nh)), z), Nat.add(SW.value(X.pfst(X.mul128(r, r))), C.shift(64n, SW.value(X.psnd(X.mul128(r, r))))), Nat.mul(SW.value(r), SW.value(r)), MU.m128g(r, r))
  +e7 = eq_comm(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r)))
  Equal.trans(Bool, F.sq_exact(nh, X.mul128(r, r)), Bool.and(Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), Nat.is_eq(Nat.mul(SW.value(r), SW.value(r)), C.shift(64n, SW.value(nh))), Equal.trans(Bool, F.sq_exact(nh, X.mul128(r, r)), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), X.is_zero(X.pfst(X.mul128(r, r)))), Bool.and(Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), e1, Equal.trans(Bool, Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), X.is_zero(X.pfst(X.mul128(r, r)))), Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n)), Bool.and(Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), e2, Equal.trans(Bool, Bool.and(Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r)))), Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n)), Bool.and(Nat.is_eq(SW.value(X.pfst(X.mul128(r, r))), 0n), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), Bool.and(Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), e3, e4))), Equal.trans(Bool, Bool.and(Nat.is_eq(0n, SW.value(X.pfst(X.mul128(r, r)))), Nat.is_eq(SW.value(nh), SW.value(X.psnd(X.mul128(r, r))))), Nat.is_eq(C.shift(64n, SW.value(nh)), Nat.add(SW.value(X.pfst(X.mul128(r, r))), C.shift(64n, SW.value(X.psnd(X.mul128(r, r)))))), Nat.is_eq(Nat.mul(SW.value(r), SW.value(r)), C.shift(64n, SW.value(nh))), e5, Equal.trans(Bool, Nat.is_eq(C.shift(64n, SW.value(nh)), Nat.add(SW.value(X.pfst(X.mul128(r, r))), C.shift(64n, SW.value(X.psnd(X.mul128(r, r)))))), Nat.is_eq(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))), Nat.is_eq(Nat.mul(SW.value(r), SW.value(r)), C.shift(64n, SW.value(nh))), e6, e7)))

# counting down from r in [S, S + fuel] stops at S
def sqd(fuel: Nat, +nh: WU.U64, +r: WU.U64, over: Bool, +ho: {over == Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))) : Bool}, +hge: {Nat.is_le(M.isqrt(C.shift(64n, SW.value(nh))), SW.value(r)) == True{} : Bool}, +hf: {Nat.is_le(SW.value(r), Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), fuel)) == True{} : Bool}) -> {SW.value(F.sq_down(fuel, nh, r, over)) == M.isqrt(C.shift(64n, SW.value(nh))) : Nat}:
  match fuel over:
    case 0n _:
      N.le_antisym(SW.value(r), M.isqrt(C.shift(64n, SW.value(nh))), L.subst(Nat, z => {Nat.is_le(SW.value(r), z) == True{} : Bool}, Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), 0n), M.isqrt(C.shift(64n, SW.value(nh))), N.add_zero(M.isqrt(C.shift(64n, SW.value(nh)))), hf), hge)
    case 1n+ +f False{}:
      +h1 = N.not_lt_le(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r)), Equal.sym(Bool, False{}, Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))), ho))
      N.le_antisym(SW.value(r), M.isqrt(C.shift(64n, SW.value(nh))), AQ.isqrt_ge(C.shift(64n, SW.value(nh)), SW.value(r), h1), hge)
    case 1n+ +f True{}:
      +h1 = Equal.sym(Bool, True{}, Nat.is_lt(C.shift(64n, SW.value(nh)), Nat.mul(SW.value(r), SW.value(r))), ho)
      +hl = AQ.isqrt_lt(C.shift(64n, SW.value(nh)), SW.value(r), h1)
      +h0 = N.le_trans(1n, 1n+M.isqrt(C.shift(64n, SW.value(nh))), SW.value(r), N.zero_le(M.isqrt(C.shift(64n, SW.value(nh)))), N.lt_succ_le_succ(M.isqrt(C.shift(64n, SW.value(nh))), SW.value(r), hl))
      sv = WA.sub_value(r, WU.U64{1, 0}, h0)
      +es = Equal.trans(Nat, SW.value(X.sub(r, WU.U64{1, 0})), Nat.sub(SW.value(r), 1n), Nat.sub(SW.value(r), 1n), sv, {==})
      +eR = Equal.trans(Nat, 1n+SW.value(X.sub(r, WU.U64{1, 0})), 1n+Nat.sub(SW.value(r), 1n), SW.value(r), N.succ_cong(SW.value(X.sub(r, WU.U64{1, 0})), Nat.sub(SW.value(r), 1n), es), N.sub_add(SW.value(r), 1n, h0))
      +hge2 = N.lt_succ_le(M.isqrt(C.shift(64n, SW.value(nh))), SW.value(X.sub(r, WU.U64{1, 0})), L.subst(Nat, z => {Nat.is_lt(M.isqrt(C.shift(64n, SW.value(nh))), z) == True{} : Bool}, SW.value(r), 1n+SW.value(X.sub(r, WU.U64{1, 0})), Equal.sym(Nat, 1n+SW.value(X.sub(r, WU.U64{1, 0})), SW.value(r), eR), hl))
      +hf1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), 1n+f)) == True{} : Bool}, SW.value(r), 1n+SW.value(X.sub(r, WU.U64{1, 0})), Equal.sym(Nat, 1n+SW.value(X.sub(r, WU.U64{1, 0})), SW.value(r), eR), hf)
      +hf2 = L.subst(Nat, z => {Nat.is_le(1n+SW.value(X.sub(r, WU.U64{1, 0})), z) == True{} : Bool}, Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), 1n+f), 1n+Nat.add(M.isqrt(C.shift(64n, SW.value(nh))), f), N.add_succ(M.isqrt(C.shift(64n, SW.value(nh))), f), hf1)
      sqd(f, nh, X.sub(r, WU.U64{1, 0}), F.sq_over(nh, X.mul128(X.sub(r, WU.U64{1, 0}), X.sub(r, WU.U64{1, 0}))), sqo(nh, X.sub(r, WU.U64{1, 0})), hge2, hf2)
