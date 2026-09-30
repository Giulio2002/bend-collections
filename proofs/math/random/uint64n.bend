import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/rand.bend as SR
import ../../../spec/math/random/source.bend as SRC
import ../../../src/math/u64.bend as WU
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as LA
import ../typed/width.bend as WI
import ../typed/w64add.bend as WA
import ../typed/w64m128.bend as M128
import ../typed/w64dmrem.bend as DMR
import ../natural/arith.bend as AR
import ./bits.bend as BI
import ./lemire.bend as LE
import ../../../spec/math/random.bend as SRM
import ../../lib/u32alg.bend as UA

# rand.bend's uint64n computes the specification's bounded draw
# (spec/math/random/rand.bend below: the first draw Go's uint64n accepts,
# among at most 128) for every source and bound, and so is below n.

def Z() -> WU.U64:
  WU.U64{0, 0}

def one64() -> WU.U64:
  WU.U64{1, 0}

# ---- the threshold 2^64 mod n ----

def q_one(+q: Nat, +one: Nat, +h1: {one == 1n : Nat}, +c: Bool, +hc: {Nat.is_eq(q, 0n) == c : Bool}, +hq0: {c == False{} : Bool}, +hq1: {C.fits(1n, q) == True{} : Bool}) -> {q == one : Nat}:
  match q:
    case 0n:
      Empty.absurd({0n == one : Nat}, L.true_false(Equal.trans(Bool, True{}, c, False{}, hc, hq0)))
    case 1n:
      Equal.sym(Nat, one, 1n, h1)
    case 2n+r:
      Empty.absurd({2n+r == one : Nat}, L.false_true(hq1))

def add_eq0_r(+a: Nat, +b: Nat, +h: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      h
    case 1n+p:
      Empty.absurd({b == 0n : Nat}, N.succ_zero(Nat.add(p, b), h))

def q_nz_c(+q: Nat, +s: Nat, +vn: Nat, +hn: {Nat.is_eq(vn, 0n) == False{} : Bool}, +e: {Nat.add(s, vn) == C.shift(64n, q) : Nat}, +c: Bool, +hc: {Nat.is_eq(q, 0n) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +hq = N.eq_from_is_eq(q, 0n, hc)
      +sum0 = Equal.trans(Nat, Nat.add(s, vn), C.shift(64n, q), 0n, e, Equal.trans(Nat, C.shift(64n, q), C.shift(64n, 0n), 0n, Equal.cong(Nat, Nat, z => C.shift(64n, z), q, 0n, hq), WI.shift_zero(64n)))
      +v0 = add_eq0_r(s, vn, sum0)
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(vn, 0n), False{}, Equal.sym(Bool, Nat.is_eq(vn, 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), vn, 0n, v0)), hn)))

def q_nz(+q: Nat, +s: Nat, +vn: Nat, +hn: {Nat.is_eq(vn, 0n) == False{} : Bool}, +e: {Nat.add(s, vn) == C.shift(64n, q) : Nat}) -> {Nat.is_eq(q, 0n) == False{} : Bool}:
  q_nz_c(q, s, vn, hn, e, Nat.is_eq(q, 0n), {==})

# a nonzero word and its negation add up to 2^64
def neg_sum(+one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +hn: {Nat.is_eq(SW.value(n), 0n) == False{} : Bool}) -> {Nat.add(SW.value(X.sub(Z(), n)), SW.value(n)) == C.shift(64n, one) : Nat}:
  +s = SW.value(X.sub(Z(), n))
  +vn = SW.value(n)
  +q = M128.QSUB(one, Z(), n)
  +e = M128.sub_eq(one, h1, Z(), n)
  +hs = Equal.trans(Bool, C.fits(65n, C.shift(64n, q)), C.fits(65n, Nat.add(s, vn)), True{}, Equal.cong(Nat, Bool, z => C.fits(65n, z), C.shift(64n, q), Nat.add(s, vn), Equal.sym(Nat, Nat.add(s, vn), C.shift(64n, q), e)), M128.sum_fits(64n, s, vn, M128.fit64(X.sub(Z(), n)), M128.fit64(n)))
  +hq1 = Equal.trans(Bool, C.fits(1n, q), C.fits(1n, C.high(64n, C.shift(64n, q))), True{}, Equal.cong(Nat, Bool, z => C.fits(1n, z), q, C.high(64n, C.shift(64n, q)), Equal.sym(Nat, C.high(64n, C.shift(64n, q)), q, WI.high_u(64n, 0n, q, {==}))), M128.fits_hi(C.shift(64n, q), hs))
  +hq = q_nz(q, s, vn, hn, e)
  %q_one(q, one, h1, Nat.is_eq(q, 0n), {==}, hq, hq1) : {Nat.add(s, vn) == C.shift(64n, _) : Nat}
  e

# pow2mod through a symbolic one (2^64 is never a closed term)
def pm_one(+w: Nat, +m: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {SR.pow2mod(w, 1n+m) == Nat.mod(C.shift(w, one), 1n+m) : Nat}:
  %Equal.sym(Nat, one, 1n, h1) : {SR.pow2mod(w, 1n+m) == Nat.mod(C.shift(w, _), 1n+m) : Nat}
  LE.pm(w, m)

def thresh_m(+one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}, +hz: {X.is_zero(n) == False{} : Bool}) -> {SW.value(R.thresh(n)) == SR.pow2mod(64n, 1n+m) : Nat}:
  +s = SW.value(X.sub(Z(), n))
  +hn = Equal.trans(Bool, Nat.is_eq(SW.value(n), 0n), X.is_zero(n), False{}, Equal.sym(Bool, X.is_zero(n), Nat.is_eq(SW.value(n), 0n), WA.is_zero_value(n)), hz)
  +ns = Equal.trans(Nat, Nat.add(s, 1n+m), Nat.add(s, SW.value(n)), C.shift(64n, one), Equal.cong(Nat, Nat, z => Nat.add(s, z), 1n+m, SW.value(n), Equal.sym(Nat, SW.value(n), 1n+m, hv)), neg_sum(one, h1, n, hn))
  Equal.trans(Nat, SW.value(R.thresh(n)), Nat.mod(s, SW.value(n)), SR.pow2mod(64n, 1n+m),
    DMR.divmod_rem(X.sub(Z(), n), n, hz),
    %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {Nat.mod(s, _) == SR.pow2mod(64n, 1n+m) : Nat}
    Equal.trans(Nat, Nat.mod(s, 1n+m), Nat.mod(Nat.add(Nat.mul(1n, 1n+m), s), 1n+m), SR.pow2mod(64n, 1n+m),
      Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(1n, 1n+m), s), 1n+m), Nat.mod(s, 1n+m), AR.absorb(m, 1n, s)),
      %Equal.sym(Nat, Nat.mul(1n, 1n+m), 1n+m, LA.one_mul(1n+m)) : {Nat.mod(Nat.add(_, s), 1n+m) == SR.pow2mod(64n, 1n+m) : Nat}
      %N.add_comm(s, 1n+m) : {Nat.mod(_, 1n+m) == SR.pow2mod(64n, 1n+m) : Nat}
      %Equal.sym(Nat, Nat.add(s, 1n+m), C.shift(64n, one), ns) : {Nat.mod(_, 1n+m) == SR.pow2mod(64n, 1n+m) : Nat}
      Equal.sym(Nat, SR.pow2mod(64n, 1n+m), Nat.mod(C.shift(64n, one), 1n+m), pm_one(64n, m, one, h1))))

# n - 1 for a nonzero n
def pred_value(+n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}) -> {SW.value(X.sub(n, one64())) == m : Nat}:
  +hle = Equal.trans(Bool, Nat.is_le(1n, SW.value(n)), Nat.is_le(1n, 1n+m), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n, z), SW.value(n), 1n+m, hv), N.zero_le(m))
  Equal.trans(Nat, SW.value(X.sub(n, one64())), Nat.sub(SW.value(n), 1n), m, WA.sub_value(n, one64(), hle),
    %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {Nat.sub(_, 1n) == m : Nat}
    N.sub_zero(m))

# the power-of-two test is n & (n - 1) == 0
def pow2_value(+n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}) -> {R.is_pow2(n) == Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) : Bool}:
  Equal.trans(Bool, R.is_pow2(n), Nat.is_eq(SW.value(R.and64(n, X.sub(n, one64()))), 0n), Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n),
    WA.is_zero_value(R.and64(n, X.sub(n, one64()))),
    %Equal.sym(Nat, SW.value(R.and64(n, X.sub(n, one64()))), SR.and_bits(64n, SW.value(n), SW.value(X.sub(n, one64()))), BI.and64_value(n, X.sub(n, one64()))) : {Nat.is_eq(_, 0n) == Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) : Bool}
    %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {Nat.is_eq(SR.and_bits(64n, _, SW.value(X.sub(n, one64()))), 0n) == Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) : Bool}
    %Equal.sym(Nat, SW.value(X.sub(n, one64())), m, pred_value(n, m, hv)) : {Nat.is_eq(SR.and_bits(64n, 1n+m, _), 0n) == Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) : Bool}
    {==})

# the mask is x & (n - 1)
def mask_value(+x: WU.U64, +n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}) -> {SW.value(R.and64(x, X.sub(n, one64()))) == SR.and_bits(64n, SW.value(x), m) : Nat}:
  %Equal.sym(Nat, SW.value(R.and64(x, X.sub(n, one64()))), SR.and_bits(64n, SW.value(x), SW.value(X.sub(n, one64()))), BI.and64_value(x, X.sub(n, one64()))) : {_ == SR.and_bits(64n, SW.value(x), m) : Nat}
  %Equal.sym(Nat, SW.value(X.sub(n, one64())), m, pred_value(n, m, hv)) : {SR.and_bits(64n, SW.value(x), _) == SR.and_bits(64n, SW.value(x), m) : Nat}
  {==}

# the halves of the 128-bit product
def m128_lo(+x: WU.U64, +n: WU.U64) -> {SW.value(X.pfst(X.mul128(x, n))) == C.low(64n, Nat.mul(SW.value(x), SW.value(n))) : Nat}:
  match x n:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +r = SW.value(X.pfst(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))
      +q = SW.value(X.psnd(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))
      %M128.m128_value(al, ah, bl, bh) : {r == C.low(64n, _) : Nat}
      Equal.sym(Nat, C.low(64n, Nat.add(r, C.shift(64n, q))), r, WI.low_u(64n, r, q, M128.fit64(X.pfst(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))))

def m128_hi(+x: WU.U64, +n: WU.U64) -> {SW.value(X.psnd(X.mul128(x, n))) == C.high(64n, Nat.mul(SW.value(x), SW.value(n))) : Nat}:
  match x n:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +r = SW.value(X.pfst(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))
      +q = SW.value(X.psnd(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))
      %M128.m128_value(al, ah, bl, bh) : {q == C.high(64n, _) : Nat}
      Equal.sym(Nat, C.high(64n, Nat.add(r, C.shift(64n, q))), q, WI.high_u(64n, r, q, M128.fit64(X.pfst(X.mul128(WU.U64{al, ah}, WU.U64{bl, bh})))))

# ---- the draws ----

# the specification's bounded draw after a draw of x with state s
def cont(~S: Data, ~next: S -> WU.U64 & S, f: Nat, +n: Nat, +x: Nat, +s: S) -> Nat & S:
  SR.below_go(~S, ~next, f, n, SR.draw(64n, x, n), x, s)

def below_cont(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: Nat, +s: S) -> {SR.below(~S, ~next, f, n, s) == cont(~S, ~next, f, n, SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s))) : Nat & S}:
  {==}

def fixpoint(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: WU.U64, +t: WU.U64, +hi: WU.U64, +lo: WU.U64, +s: S, +h: {X.lt(lo, t) == False{} : Bool}) -> {R.retry(~S, ~next, f, n, t, R.D{hi, lo, s}) == R.D{hi, lo, s} : R.Draw<S>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(Bool, X.lt(lo, t), False{}, h) : {R.retry(~S, ~next, g, n, t, R.again(~S, ~next, n, hi, lo, s, _)) == R.D{hi, lo, s} : R.Draw<S>}
      fixpoint(~S, ~next, g, n, t, hi, lo, s, h)

# retry_fast (the early exit) is retry
def fast_c(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: WU.U64, +t: WU.U64, +d: R.Draw<S>, +c: Bool, +hc: {R.rejects(S, t, d) == c : Bool}) -> {R.retry_fast(~S, ~next, f, n, t, d, c) == R.retry(~S, ~next, f, n, t, d) : R.Draw<S>}:
  match f d c:
    case _ R.D{+hi, +lo, +s} False{}:
      Equal.sym(R.Draw<S>, R.retry(~S, ~next, f, n, t, R.D{hi, lo, s}), R.D{hi, lo, s}, fixpoint(~S, ~next, f, n, t, hi, lo, s, hc))
    case 0n R.D{+hi, +lo, +s} True{}:
      {==}
    case 1n+g R.D{+hi, +lo, +s} True{}:
      %Equal.sym(Bool, X.lt(lo, t), True{}, hc) : {R.retry_fast(~S, ~next, 1n+g, n, t, R.D{hi, lo, s}, True{}) == R.retry(~S, ~next, g, n, t, R.again(~S, ~next, n, hi, lo, s, _)) : R.Draw<S>}
      fast_c(~S, ~next, g, n, t, R.draw(S, n, next(s)), R.rejects(S, t, R.draw(S, n, next(s))), {==})

# Lemire's decision of the specification: accept unless lo < 2^64 mod n
def dec(+x: Nat, +m: Nat, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(C.low(64n, Nat.mul(x, 1n+m)), SR.pow2mod(64n, 1n+m)) == c : Bool}) -> {SR.draw(64n, x, 1n+m) == SR.accept(C.high(64n, Nat.mul(x, 1n+m)), Bool.not(c)) : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, x, 1n+m), SR.lemire(64n, 1n+m, C.high(64n, Nat.mul(x, 1n+m)), C.low(64n, Nat.mul(x, 1n+m))), LE.draw_lemire(64n, m, x, hp)) : {_ == SR.accept(C.high(64n, Nat.mul(x, 1n+m)), Bool.not(c)) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(Nat.is_lt(C.low(64n, Nat.mul(x, 1n+m)), 1n+m), Nat.is_lt(C.low(64n, Nat.mul(x, 1n+m)), SR.pow2mod(64n, 1n+m))), c, LE.and_lt(C.low(64n, Nat.mul(x, 1n+m)), 1n+m, SR.pow2mod(64n, 1n+m), htn, c, hc)) : {SR.accept(C.high(64n, Nat.mul(x, 1n+m)), Bool.not(_)) == SR.accept(C.high(64n, Nat.mul(x, 1n+m)), Bool.not(c)) : Maybe<&2, Nat>}
  {==}

def last_acc(~S: Data, ~next: S -> WU.U64 & S, +h: Nat, +ok: Bool, +x: Nat, +n: Nat, +s: S, +hh: {h == C.high(64n, Nat.mul(x, n)) : Nat}) -> {SR.below_go(~S, ~next, 0n, n, SR.accept(h, ok), x, s) == (h, s) : Nat & S}:
  match ok:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, h, C.high(64n, Nat.mul(x, n)), hh) : {(C.high(64n, Nat.mul(x, n)), s) == (_, s) : Nat & S}
      {==}

def pm_lt(+m: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m), Nat.is_lt(Nat.mod(C.shift(64n, one), 1n+m), 1n+m), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, 1n+m), SR.pow2mod(64n, 1n+m), Nat.mod(C.shift(64n, one), 1n+m), pm_one(64n, m, one, h1)),
    AR.dm_lt(m, C.shift(64n, one)))

# the implementation's rejection test is the specification's
def lt_low(+x: WU.U64, +n: WU.U64, +m: Nat, +t: WU.U64, +hv: {SW.value(n) == 1n+m : Nat}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}) -> {X.lt(X.pfst(X.mul128(x, n)), t) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)) : Bool}:
  Equal.trans(Bool, X.lt(X.pfst(X.mul128(x, n)), t), Nat.is_lt(SW.value(X.pfst(X.mul128(x, n))), SW.value(t)), Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)),
    WA.lt_value(X.pfst(X.mul128(x, n)), t),
    %Equal.sym(Nat, SW.value(X.pfst(X.mul128(x, n))), C.low(64n, Nat.mul(SW.value(x), SW.value(n))), m128_lo(x, n)) : {Nat.is_lt(_, SW.value(t)) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)) : Bool}
    %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), _)), SW.value(t)) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)) : Bool}
    %Equal.sym(Nat, SW.value(t), SR.pow2mod(64n, 1n+m), ht) : {Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), _) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)) : Bool}
    {==})

def hi_value(+x: WU.U64, +n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}) -> {SW.value(X.psnd(X.mul128(x, n))) == C.high(64n, Nat.mul(SW.value(x), 1n+m)) : Nat}:
  %hv : {SW.value(X.psnd(X.mul128(x, n))) == C.high(64n, Nat.mul(SW.value(x), _)) : Nat}
  m128_hi(x, n)

def hd_of(+x: WU.U64, +n: WU.U64, +m: Nat, +t: WU.U64, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}, +c: Bool, +hc: {X.lt(X.pfst(X.mul128(x, n)), t) == c : Bool}) -> {SR.draw(64n, SW.value(x), 1n+m) == SR.accept(C.high(64n, Nat.mul(SW.value(x), 1n+m)), Bool.not(c)) : Maybe<&2, Nat>}:
  dec(SW.value(x), m, hp, htn, c, Equal.trans(Bool, Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)), X.lt(X.pfst(X.mul128(x, n)), t), c, Equal.sym(Bool, X.lt(X.pfst(X.mul128(x, n)), t), Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), SR.pow2mod(64n, 1n+m)), lt_low(x, n, m, t, hv, ht)), hc))

# one retry step, accepted
def step_false(~S: Data, ~next: S -> WU.U64 & S, +g: Nat, +n: WU.U64, +m: Nat, +t: WU.U64, +x: WU.U64, +s1: S, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}, +hc: {X.lt(X.pfst(X.mul128(x, n)), t) == False{} : Bool}) -> {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.again(~S, ~next, n, X.psnd(X.mul128(x, n)), X.pfst(X.mul128(x, n)), s1, False{})))) == cont(~S, ~next, 1n+g, 1n+m, SW.value(x), s1) : Nat & S}:
  +hi = X.psnd(X.mul128(x, n))
  +lo = X.pfst(X.mul128(x, n))
  +H = C.high(64n, Nat.mul(SW.value(x), 1n+m))
  %Equal.sym(R.Draw<S>, R.retry(~S, ~next, g, n, t, R.D{hi, lo, s1}), R.D{hi, lo, s1}, fixpoint(~S, ~next, g, n, t, hi, lo, s1, hc)) : {SRM.val_pair(S, R.result(S, _)) == cont(~S, ~next, 1n+g, 1n+m, SW.value(x), s1) : Nat & S}
  %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, SW.value(x), 1n+m), SR.accept(H, True{}), hd_of(x, n, m, t, hv, hp, htn, ht, False{}, hc)) : {(SW.value(hi), s1) == SR.below_go(~S, ~next, 1n+g, 1n+m, _, SW.value(x), s1) : Nat & S}
  Equal.cong(Nat, Nat & S, z => (z, s1), SW.value(hi), H, hi_value(x, n, m, hv))

# one retry step, rejected: the next draw
def step_true(~S: Data, ~next: S -> WU.U64 & S, +g: Nat, +n: WU.U64, +m: Nat, +t: WU.U64, +x: WU.U64, +s1: S, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}, +hc: {X.lt(X.pfst(X.mul128(x, n)), t) == True{} : Bool}, +rec: {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.draw(S, n, next(s1))))) == cont(~S, ~next, g, 1n+m, SW.value(SRC.fst64(S, next(s1))), SRC.snd64(S, next(s1))) : Nat & S}) -> {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.again(~S, ~next, n, X.psnd(X.mul128(x, n)), X.pfst(X.mul128(x, n)), s1, True{})))) == cont(~S, ~next, 1n+g, 1n+m, SW.value(x), s1) : Nat & S}:
  +H = C.high(64n, Nat.mul(SW.value(x), 1n+m))
  %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, SW.value(x), 1n+m), SR.accept(H, False{}), hd_of(x, n, m, t, hv, hp, htn, ht, True{}, hc)) : {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.draw(S, n, next(s1))))) == SR.below_go(~S, ~next, 1n+g, 1n+m, _, SW.value(x), s1) : Nat & S}
  rec

def step_case(~S: Data, ~next: S -> WU.U64 & S, +g: Nat, +n: WU.U64, +m: Nat, +t: WU.U64, +x: WU.U64, +s1: S, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}, +c: Bool, +hc: {X.lt(X.pfst(X.mul128(x, n)), t) == c : Bool}, +rec: {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.draw(S, n, next(s1))))) == cont(~S, ~next, g, 1n+m, SW.value(SRC.fst64(S, next(s1))), SRC.snd64(S, next(s1))) : Nat & S}) -> {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, g, n, t, R.again(~S, ~next, n, X.psnd(X.mul128(x, n)), X.pfst(X.mul128(x, n)), s1, c)))) == cont(~S, ~next, 1n+g, 1n+m, SW.value(x), s1) : Nat & S}:
  match c:
    case False{}:
      step_false(~S, ~next, g, n, m, t, x, s1, hv, hp, htn, ht, hc)
    case True{}:
      step_true(~S, ~next, g, n, m, t, x, s1, hv, hp, htn, ht, hc, rec)

# THEOREM (the rejection loop): f retries from the draw p follow the
# specification's draws
def loop(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: WU.U64, +m: Nat, +t: WU.U64, p: WU.U64 & S, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +ht: {SW.value(t) == SR.pow2mod(64n, 1n+m) : Nat}) -> {SRM.val_pair(S, R.result(S, R.retry(~S, ~next, f, n, t, R.draw(S, n, p)))) == cont(~S, ~next, f, 1n+m, SW.value(SRC.fst64(S, p)), SRC.snd64(S, p)) : Nat & S}:
  match f p:
    case 0n Tuple{+x, +s1}:
      +H = C.high(64n, Nat.mul(SW.value(x), 1n+m))
      +c0 = X.lt(X.pfst(X.mul128(x, n)), t)
      %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, SW.value(x), 1n+m), SR.accept(H, Bool.not(c0)), hd_of(x, n, m, t, hv, hp, htn, ht, c0, {==})) : {(SW.value(X.psnd(X.mul128(x, n))), s1) == SR.below_go(~S, ~next, 0n, 1n+m, _, SW.value(x), s1) : Nat & S}
      %Equal.sym(Nat & S, SR.below_go(~S, ~next, 0n, 1n+m, SR.accept(H, Bool.not(c0)), SW.value(x), s1), (H, s1), last_acc(~S, ~next, H, Bool.not(c0), SW.value(x), 1n+m, s1, {==})) : {(SW.value(X.psnd(X.mul128(x, n))), s1) == _ : Nat & S}
      Equal.cong(Nat, Nat & S, z => (z, s1), SW.value(X.psnd(X.mul128(x, n))), H, hi_value(x, n, m, hv))
    case 1n+g Tuple{+x, +s1}:
      step_case(~S, ~next, g, n, m, t, x, s1, hv, hp, htn, ht, X.lt(X.pfst(X.mul128(x, n)), t), {==}, loop(~S, ~next, g, n, m, t, next(s1), hv, hp, htn, ht))

def lt_low_n(+x: WU.U64, +n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}) -> {X.lt(X.pfst(X.mul128(x, n)), n) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), 1n+m) : Bool}:
  Equal.trans(Bool, X.lt(X.pfst(X.mul128(x, n)), n), Nat.is_lt(SW.value(X.pfst(X.mul128(x, n))), SW.value(n)), Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), 1n+m),
    WA.lt_value(X.pfst(X.mul128(x, n)), n),
    %Equal.sym(Nat, SW.value(X.pfst(X.mul128(x, n))), C.low(64n, Nat.mul(SW.value(x), SW.value(n))), m128_lo(x, n)) : {Nat.is_lt(_, SW.value(n)) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), 1n+m) : Bool}
    %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), _)), _) == Nat.is_lt(C.low(64n, Nat.mul(SW.value(x), 1n+m)), 1n+m) : Bool}
    {==})

# lo >= n: the first draw is accepted by the specification too
def first_false(~S: Data, ~next: S -> WU.U64 & S, +n: WU.U64, +m: Nat, +x: WU.U64, +s1: S, +hv: {SW.value(n) == 1n+m : Nat}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +hc: {X.lt(X.pfst(X.mul128(x, n)), n) == False{} : Bool}) -> {SRM.val_pair(S, R.lemire_small(~S, ~next, n, X.psnd(X.mul128(x, n)), X.pfst(X.mul128(x, n)), s1, False{})) == cont(~S, ~next, 127n, 1n+m, SW.value(x), s1) : Nat & S}:
  +L = C.low(64n, Nat.mul(SW.value(x), 1n+m))
  +H = C.high(64n, Nat.mul(SW.value(x), 1n+m))
  +pm = SR.pow2mod(64n, 1n+m)
  +hn = Equal.trans(Bool, Nat.is_lt(L, 1n+m), X.lt(X.pfst(X.mul128(x, n)), n), False{},
    Equal.sym(Bool, X.lt(X.pfst(X.mul128(x, n)), n), Nat.is_lt(L, 1n+m), lt_low_n(x, n, m, hv)),
    hc)
  +hl = N.le_not_lt(L, pm, N.le_trans(pm, 1n+m, L, N.lt_le(pm, 1n+m, htn), N.not_lt_le(L, 1n+m, hn)))
  %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, SW.value(x), 1n+m), SR.accept(H, True{}), dec(SW.value(x), m, hp, htn, False{}, hl)) : {(SW.value(X.psnd(X.mul128(x, n))), s1) == SR.below_go(~S, ~next, 127n, 1n+m, _, SW.value(x), s1) : Nat & S}
  Equal.cong(Nat, Nat & S, z => (z, s1), SW.value(X.psnd(X.mul128(x, n))), H, hi_value(x, n, m, hv))

# the first draw: accepted at once when lo >= n, else the loop
def first_case(~S: Data, ~next: S -> WU.U64 & S, +one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +m: Nat, +x: WU.U64, +s1: S, +hv: {SW.value(n) == 1n+m : Nat}, +hz: {X.is_zero(n) == False{} : Bool}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}, +htn: {Nat.is_lt(SR.pow2mod(64n, 1n+m), 1n+m) == True{} : Bool}, +c: Bool, +hc: {X.lt(X.pfst(X.mul128(x, n)), n) == c : Bool}) -> {SRM.val_pair(S, R.lemire_small(~S, ~next, n, X.psnd(X.mul128(x, n)), X.pfst(X.mul128(x, n)), s1, c)) == cont(~S, ~next, 127n, 1n+m, SW.value(x), s1) : Nat & S}:
  match c:
    case True{}:
      +t = R.thresh(n)
      +hi = X.psnd(X.mul128(x, n))
      +lo = X.pfst(X.mul128(x, n))
      Equal.trans(Nat & S, SRM.val_pair(S, R.result(S, R.retry_fast(~S, ~next, 127n, n, t, R.D{hi, lo, s1}, X.lt(lo, t)))), SRM.val_pair(S, R.result(S, R.retry(~S, ~next, 127n, n, t, R.D{hi, lo, s1}))), cont(~S, ~next, 127n, 1n+m, SW.value(x), s1),
        Equal.cong(R.Draw<S>, Nat & S, z => SRM.val_pair(S, R.result(S, z)), R.retry_fast(~S, ~next, 127n, n, t, R.D{hi, lo, s1}, X.lt(lo, t)), R.retry(~S, ~next, 127n, n, t, R.D{hi, lo, s1}), fast_c(~S, ~next, 127n, n, t, R.D{hi, lo, s1}, X.lt(lo, t), {==})),
        loop(~S, ~next, 127n, n, m, t, (x, s1), hv, hp, htn, thresh_m(one, h1, n, m, hv, hz)))
    case False{}:
      first_false(~S, ~next, n, m, x, s1, hv, hp, htn, hc)

# ---- the mask branch and n == 0 ----

def mask_pair(-S: Data, +n: WU.U64, +m: Nat, p: WU.U64 & S, +hv: {SW.value(n) == 1n+m : Nat}) -> {SRM.val_pair(S, R.mask(S, n, p)) == (SR.and_bits(64n, SW.value(SRC.fst64(S, p)), m), SRC.snd64(S, p)) : Nat & S}:
  match p:
    case Tuple{+x, +s1}:
      Equal.cong(Nat, Nat & S, z => (z, s1), SW.value(R.and64(x, X.sub(n, one64()))), SR.and_bits(64n, SW.value(x), m), mask_value(x, n, m, hv))

def all1(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, all1(p)}

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_all1(+n: Nat, +w: Word(n)) -> {Word.and(n, w, all1(n)) == w : Word(n)}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{+x, +t}:
      %Equal.sym(Bool, Bool.and(x, True{}), x, and_true(x)) : {WCon{_, Word.and(p, t, all1(p))} == WCon{x, t} : Word(1n+p)}
      Equal.cong(Word(p), Word(1n+p), z => WCon{x, z}, Word.and(p, t, all1(p)), t, and_all1(p, t))

def uand_all(+y: U32, +M: U32, +hM: {M == U32{all1(32n)} : U32}) -> {U32.and(y, M) == y : U32}:
  match y:
    case U32{+w}:
      %Equal.sym(U32, M, U32{all1(32n)}, hM) : {U32.and(U32{w}, _) == U32{w} : U32}
      Equal.cong(Word(32n), U32, z => U32{z}, Word.and(32n, w, all1(32n)), w, and_all1(32n, w))

# n == 0 is read as 2^64: the whole word
def zero_pair(-S: Data, p: WU.U64 & S) -> {SRM.val_pair(S, R.mask(S, Z(), p)) == (SW.value(SRC.fst64(S, p)), SRC.snd64(S, p)) : Nat & S}:
  match p:
    case Tuple{+x, +s1}:
      match x:
        case WU.U64{+l, +h}:
          %Equal.sym(U32, U32.and(l, X.lo(X.sub(Z(), one64()))), l, uand_all(l, X.lo(X.sub(Z(), one64())), {==})) : {(Nat.add(U32.to_nat(_), C.shift(32n, U32.to_nat(U32.and(h, X.hi(X.sub(Z(), one64())))))), s1) == (SW.value(WU.U64{l, h}), s1) : Nat & S}
          %Equal.sym(U32, U32.and(h, X.hi(X.sub(Z(), one64()))), h, uand_all(h, X.hi(X.sub(Z(), one64())), {==})) : {(Nat.add(U32.to_nat(l), C.shift(32n, U32.to_nat(_))), s1) == (SW.value(WU.U64{l, h}), s1) : Nat & S}
          {==}

# ---- uint64n ----

def top_first(~S: Data, ~next: S -> WU.U64 & S, +one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +m: Nat, p: WU.U64 & S, +hv: {SW.value(n) == 1n+m : Nat}, +hz: {X.is_zero(n) == False{} : Bool}, +hp: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == False{} : Bool}) -> {SRM.val_pair(S, R.lemire_first(~S, ~next, n, R.draw(S, n, p))) == cont(~S, ~next, 127n, 1n+m, SW.value(SRC.fst64(S, p)), SRC.snd64(S, p)) : Nat & S}:
  match p:
    case Tuple{+x, +s1}:
      first_case(~S, ~next, one, h1, n, m, x, s1, hv, hz, hp, pm_lt(m, one, h1), X.lt(X.pfst(X.mul128(x, n)), n), {==})

def value_nz(~S: Data, ~next: S -> WU.U64 & S, +one: Nat, +h1: {one == 1n : Nat}, +s: S, +n: WU.U64, +m: Nat, +hv: {SW.value(n) == 1n+m : Nat}, +hz: {X.is_zero(n) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n) == c : Bool}) -> {SRM.val_pair(S, R.uint64n_pick(~S, ~next, s, n, c)) == SR.below(~S, ~next, 127n, 1n+m, s) : Nat & S}:
  match c:
    case True{}:
      +x = SW.value(SRC.fst64(S, next(s)))
      Equal.trans(Nat & S, SRM.val_pair(S, R.mask(S, n, next(s))), (SR.and_bits(64n, x, m), SRC.snd64(S, next(s))), SR.below(~S, ~next, 127n, 1n+m, s),
        mask_pair(S, n, m, next(s), hv),
        %Equal.sym(Maybe<&2, Nat>, SR.draw(64n, x, 1n+m), Some{SR.and_bits(64n, x, m)}, LE.draw_mask(64n, m, x, hc)) : {(SR.and_bits(64n, x, m), SRC.snd64(S, next(s))) == SR.below_go(~S, ~next, 127n, 1n+m, _, x, SRC.snd64(S, next(s))) : Nat & S}
        {==})
    case False{}:
      Equal.trans(Nat & S, SRM.val_pair(S, R.lemire_first(~S, ~next, n, R.draw(S, n, next(s)))), cont(~S, ~next, 127n, 1n+m, SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s))), SR.below(~S, ~next, 127n, 1n+m, s),
        top_first(~S, ~next, one, h1, n, m, next(s), hv, hz, hc),
        Equal.sym(Nat & S, SR.below(~S, ~next, 127n, 1n+m, s), cont(~S, ~next, 127n, 1n+m, SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s))), below_cont(~S, ~next, 127n, 1n+m, s)))

def zero_word(+n: WU.U64, +h: {X.is_zero(n) == True{} : Bool}) -> {n == Z() : WU.U64}:
  match n:
    case WU.U64{+l, +hh}:
      +el = UA.eq_of(l, 0, L.and_left(U32.is_zero(l), U32.is_zero(hh), h))
      +eh = UA.eq_of(hh, 0, L.and_right(U32.is_zero(l), U32.is_zero(hh), h))
      %Equal.sym(U32, l, 0, el) : {WU.U64{_, hh} == Z() : WU.U64}
      %Equal.sym(U32, hh, 0, eh) : {WU.U64{0, _} == Z() : WU.U64}
      {==}

def value_vn(~S: Data, ~next: S -> WU.U64 & S, +s: S, +n: WU.U64, +vn: Nat, +hv: {SW.value(n) == vn : Nat}) -> {SRM.val_pair(S, R.uint64n(~S, ~next, s, n)) == SR.below(~S, ~next, 127n, SW.value(n), s) : Nat & S}:
  match vn:
    case 0n:
      +hz = Equal.trans(Bool, X.is_zero(n), Nat.is_eq(SW.value(n), 0n), True{}, WA.is_zero_value(n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(n), 0n, hv))
      %Equal.sym(WU.U64, n, Z(), zero_word(n, hz)) : {SRM.val_pair(S, R.uint64n(~S, ~next, s, _)) == SR.below(~S, ~next, 127n, SW.value(_), s) : Nat & S}
      zero_pair(S, next(s))
    case 1n+m:
      +hz = Equal.trans(Bool, X.is_zero(n), Nat.is_eq(SW.value(n), 0n), False{}, WA.is_zero_value(n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(n), 1n+m, hv))
      %Equal.sym(Bool, R.is_pow2(n), Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n), pow2_value(n, m, hv)) : {SRM.val_pair(S, R.uint64n_pick(~S, ~next, s, n, _)) == SR.below(~S, ~next, 127n, SW.value(n), s) : Nat & S}
      %Equal.sym(Nat, SW.value(n), 1n+m, hv) : {SRM.val_pair(S, R.uint64n_pick(~S, ~next, s, n, Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n))) == SR.below(~S, ~next, 127n, _, s) : Nat & S}
      value_nz(~S, ~next, 1n, {==}, s, n, m, hv, hz, Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n), {==})

# THEOREM (Uint64n.value)
def uint64n_value(~S: Data, ~next: S -> WU.U64 & S, +s: S, +n: WU.U64) -> SRM.Uint64n.value(~S, ~next, s, n):
  value_vn(~S, ~next, s, n, SW.value(n), {==})
