import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../../spec/lib/common.bend as SC
import ../../lib/word.bend as WD
import ../../lib/u32div.bend as UD
import ./cyc.bend as CY
import ./probe_all.bend as PA
import ../../lib/words32.bend as W32

# U32 facts for insertion: links and slots, the load test, counters.


# x < 2^d with d + 1 < 32 leaves room for one more


# THEOREM: the slot of the link of s is s


# THEOREM: a link is never 0

# ---- comparisons ----

def is_gt_nat(+a: U32, +b: U32) -> {U32.is_gt(a, b) == Nat.is_gt(UD.v(a), UD.v(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), U32.cmp(a, b), Nat.cmp(UD.v(a), UD.v(b)), U.u32_cmp(a, b))

def gt_le_c(+a: Nat, +b: Nat, +c: Cmp, +hc: {Nat.cmp(a, b) == c : Cmp}, +h: {Cmp.is_gt(c) == False{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, L.true_false(h))

def gt_false_le(+a: Nat, +b: Nat, +h: {Nat.is_gt(a, b) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  gt_le_c(a, b, Nat.cmp(a, b), {==}, h)

def gt_le_t(+a: Nat, +b: Nat, +c: Cmp, +h: {Cmp.is_gt(c) == True{} : Bool}) -> {Cmp.is_le(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(LT{}) == False{} : Bool}, L.false_true(h))
    case EQ{}:
      Empty.absurd({Cmp.is_le(EQ{}) == False{} : Bool}, L.false_true(h))
    case GT{}:
      {==}

# a > b: not a <= b
def gt_true_nle(+a: Nat, +b: Nat, +h: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == False{} : Bool}:
  gt_le_t(a, b, Nat.cmp(a, b), h)

# ---- the load test ----

def dle_c(+x: Nat, +y: Nat, +h: {Nat.is_le(Nat.double(x), Nat.double(y)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(x, y) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.double(x), Nat.double(y)), False{}, Equal.sym(Bool, Nat.is_le(Nat.double(x), Nat.double(y)), True{}, h), N.lt_not_le(Nat.double(y), Nat.double(x), N.double_lt(y, x, N.not_le_lt(x, y, hc))))))

def dbl_le_inv(+x: Nat, +y: Nat, +h: {Nat.is_le(Nat.double(x), Nat.double(y)) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  dle_c(x, y, h, Nat.is_le(x, y), {==})

# 2x <= 2^(p+1): x + 1 <= 2^(p+1)
def succ_le_pow(+x: Nat, +p: Nat, +h: {Nat.is_le(Nat.double(x), SC.pow2(1n+p)) == True{} : Bool}) -> {Nat.is_le(1n+x, SC.pow2(1n+p)) == True{} : Bool}:
  N.le_trans(1n+x, 1n+SC.pow2(p), SC.pow2(1n+p), dbl_le_inv(x, SC.pow2(p), h), N.double_succ_le(SC.pow2(p), N.pow2_pos(p)))

def over_c(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +hk0: {Nat.is_lt(0n, k) == True{} : Bool}, +x: Nat, +h: {Nat.is_le(Nat.double(x), SC.pow2(k)) == True{} : Bool}) -> {Nat.is_le(1n+x, SC.pow2(k)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(1n+x, SC.pow2(0n)) == True{} : Bool}, L.false_true(hk0))
    case 1n+p:
      succ_le_pow(x, p, h)

# THEOREM: with at most half the buckets full, one more entry is n + 1 and
# the load test compares 2(n + 1) with the bucket count
def inc_n(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +hk0: {Nat.is_lt(0n, k) == True{} : Bool}, +n: U32, +hl: {Nat.is_le(Nat.double(UD.v(n)), SC.pow2(k)) == True{} : Bool}) -> {UD.v(U32.inc(n)) == 1n+UD.v(n) : Nat}:
  W32.inc_val(one, h1, n, N.le_lt_trans(1n+UD.v(n), SC.pow2(k), WD.sc(32n, one), over_c(one, h1, k, hk31, hk0, UD.v(n), hl), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), W32.pow_le32(one, h1, 1n+k, hk31))))

def over_val(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +hk0: {Nat.is_lt(0n, k) == True{} : Bool}, +n: U32, +hl: {Nat.is_le(Nat.double(UD.v(n)), SC.pow2(k)) == True{} : Bool}) -> {U32.is_gt(U32.shl(U32.inc(n)), U32.inc(CY.msk(k))) == Nat.is_gt(Nat.double(1n+UD.v(n)), SC.pow2(k)) : Bool}:
  +ei = inc_n(one, h1, k, hk31, hk0, n, hl)
  +d1 = N.double_le(1n+UD.v(n), SC.pow2(k), over_c(one, h1, k, hk31, hk0, UD.v(n), hl))
  +d2 = L.subst(Nat, z => {Nat.is_lt(Nat.double(z), SC.pow2(2n+k)) == True{} : Bool}, 1n+UD.v(n), UD.v(U32.inc(n)), Equal.sym(Nat, UD.v(U32.inc(n)), 1n+UD.v(n), ei), N.le_lt_trans(Nat.double(1n+UD.v(n)), SC.pow2(1n+k), SC.pow2(2n+k), d1, N.pow2_lt_succ(1n+k)))
  +es = Equal.trans(Nat, UD.v(U32.shl(U32.inc(n))), Nat.double(UD.v(U32.inc(n))), Nat.double(1n+UD.v(n)), U.shl_value(U32.inc(n), 2n+k, N.lt_succ_le(k, 30n, hk31), d2), Equal.cong(Nat, Nat, z => Nat.double(z), UD.v(U32.inc(n)), 1n+UD.v(n), ei))
  Equal.trans(Bool, U32.is_gt(U32.shl(U32.inc(n)), U32.inc(CY.msk(k))), Nat.is_gt(UD.v(U32.shl(U32.inc(n))), UD.v(U32.inc(CY.msk(k)))), Nat.is_gt(Nat.double(1n+UD.v(n)), SC.pow2(k)), is_gt_nat(U32.shl(U32.inc(n)), U32.inc(CY.msk(k))),
    Equal.trans(Bool, Nat.is_gt(UD.v(U32.shl(U32.inc(n))), UD.v(U32.inc(CY.msk(k)))), Nat.is_gt(Nat.double(1n+UD.v(n)), UD.v(U32.inc(CY.msk(k)))), Nat.is_gt(Nat.double(1n+UD.v(n)), SC.pow2(k)), Equal.cong(Nat, Bool, z => Nat.is_gt(z, UD.v(U32.inc(CY.msk(k)))), UD.v(U32.shl(U32.inc(n))), Nat.double(1n+UD.v(n)), es), Equal.cong(Nat, Bool, z => Nat.is_gt(Nat.double(1n+UD.v(n)), z), UD.v(U32.inc(CY.msk(k))), SC.pow2(k), PA.fuel_eq(one, h1, k, hk31))))
