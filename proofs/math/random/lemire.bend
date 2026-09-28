import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/random/rand.bend as SR
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../typed/width.bend as WI
import ../natural/arith.bend as AR
import ../../lib/arith.bend as LA
import ../../lib/u32alg.bend as UA
import ../../lib/lemmas/proofs/nat_algebra.bend as NA

# Lemire's rejection is exactly unbiased (Lemire, "Fast Random Integer
# Generation in an Interval", ACM TOMACS 2019, section 4): for every width w,
# bound 0 < n < 2^w and k < n, exactly floor(2^w / n) of the 2^w source
# outputs x draw k under Go's uint64n decision (spec/math/random/rand.bend
# draw), in both of its branches.
#
# Lemire's branch: x draws k exactly when k 2^w + t <= x n < (k + 1) 2^w,
# t = 2^w mod n. Counting x < N with x n < c gives min(N, ceil(c / n)), and
# (k + 1) 2^w - (k 2^w + t) = 2^w - t = n floor(2^w / n), so the two ceilings
# differ by floor(2^w / n).
# The mask branch (n = 2^j, Go's n & (n - 1) == 0): x & (n - 1) is the low j
# bits of x, and splitting x = 2y + b halves the width and the bound.

def b2n(b: Bool) -> Nat:
  SR.b2n(b)

# ---- Bool helpers ----

def and_false(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# lo < n and lo < t is lo < t, when t < n
def and_lt(+lo: Nat, +n: Nat, +t: Nat, +ht: {Nat.is_lt(t, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(lo, t) == c : Bool}) -> {Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t)) == c : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(lo, n), True{}, N.lt_trans(lo, t, n, hc, ht)) : {Bool.and(_, Nat.is_lt(lo, t)) == True{} : Bool}
      hc
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(lo, t), False{}, hc) : {Bool.and(Nat.is_lt(lo, n), _) == False{} : Bool}
      and_false(Nat.is_lt(lo, n))

# the hit of an accepted or rejected hi
def hit_acc(+hi: Nat, +k: Nat, +ok: Bool) -> Nat:
  SR.hit(SR.accept(hi, ok), k)

# s <= t + s
def le_plus(+t: Nat, +s: Nat) -> {Nat.is_le(s, Nat.add(t, s)) == True{} : Bool}:
  %N.add_comm(s, t) : {Nat.is_le(s, _) == True{} : Bool}
  N.le_add_right(s, t)

# ---- one output ----

def fin_lt(+hi: Nat, +k: Nat, +ok: Bool, +h: {Nat.is_lt(hi, k) == True{} : Bool}) -> {Nat.add(hit_acc(hi, k, ok), 1n) == 1n : Nat}:
  match ok:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(hi, k), False{}, N.is_eq_lt(hi, k, h)) : {Nat.add(b2n(_), 1n) == 1n : Nat}
      {==}
    case False{}:
      {==}

# hi < k: rejected or not, x n lies below both thresholds
def term_lt(+w: Nat, +k: Nat, +t: Nat, +lo: Nat, +hi: Nat, +ok: Bool, +hlo: {C.fits(w, lo) == True{} : Bool}, +hab: {Nat.is_le(Nat.add(t, C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}, +h: {Nat.is_lt(hi, k) == True{} : Bool}) -> {Nat.add(hit_acc(hi, k, ok), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), C.shift(w, 1n+k))) : Nat}:
  +y = Nat.add(lo, C.shift(w, hi))
  +a = Nat.add(t, C.shift(w, k))
  +ya = N.lt_le_trans(y, C.shift(w, 1n+hi), a, WI.lt_hi(w, lo, hi, 0n, 1n+hi, hlo, N.lt_succ(hi)), N.le_trans(C.shift(w, 1n+hi), C.shift(w, k), a, WI.shift_mono(w, 1n+hi, k, N.lt_succ_le_succ(hi, k, h)), le_plus(t, C.shift(w, k))))
  +yb = N.lt_le_trans(y, a, C.shift(w, 1n+k), ya, hab)
  %Equal.sym(Bool, Nat.is_lt(y, a), True{}, ya) : {Nat.add(hit_acc(hi, k, ok), b2n(_)) == b2n(Nat.is_lt(y, C.shift(w, 1n+k))) : Nat}
  %Equal.sym(Bool, Nat.is_lt(y, C.shift(w, 1n+k)), True{}, yb) : {Nat.add(hit_acc(hi, k, ok), 1n) == b2n(_) : Nat}
  fin_lt(hi, k, ok, h)

def fin_eq(+k: Nat, +c: Bool) -> {Nat.add(hit_acc(k, k, Bool.not(c)), b2n(c)) == 1n : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, N.is_eq_refl(k)) : {Nat.add(b2n(_), 0n) == 1n : Nat}
      {==}

# hi == k: x n is below the upper threshold, and below the lower one exactly
# when it is rejected
def term_eq(+w: Nat, +k: Nat, +t: Nat, +lo: Nat, +hlo: {C.fits(w, lo) == True{} : Bool}) -> {Nat.add(hit_acc(k, k, Bool.not(Nat.is_lt(lo, t))), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, k)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, k)), C.shift(w, 1n+k))) : Nat}:
  %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, C.shift(w, k)), Nat.add(t, C.shift(w, k))), Nat.is_lt(lo, t), WI.lt_cancel_r(lo, t, C.shift(w, k))) : {Nat.add(hit_acc(k, k, Bool.not(Nat.is_lt(lo, t))), b2n(_)) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, k)), C.shift(w, 1n+k))) : Nat}
  %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, C.shift(w, k)), C.shift(w, 1n+k)), True{}, WI.lt_hi(w, lo, k, 0n, 1n+k, hlo, N.lt_succ(k))) : {Nat.add(hit_acc(k, k, Bool.not(Nat.is_lt(lo, t))), b2n(Nat.is_lt(lo, t))) == b2n(_) : Nat}
  fin_eq(k, Nat.is_lt(lo, t))

def fin_gt(+hi: Nat, +k: Nat, +ok: Bool, +h: {Nat.is_lt(k, hi) == True{} : Bool}) -> {Nat.add(hit_acc(hi, k, ok), 0n) == 0n : Nat}:
  match ok:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(hi, k), False{}, N.is_eq_sym_false(k, hi, N.is_eq_lt(k, hi, h))) : {Nat.add(b2n(_), 0n) == 0n : Nat}
      {==}
    case False{}:
      {==}

# hi > k: x n is at or above both thresholds
def term_gt(+w: Nat, +k: Nat, +t: Nat, +lo: Nat, +hi: Nat, +ok: Bool, +hab: {Nat.is_le(Nat.add(t, C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}, +h: {Nat.is_lt(k, hi) == True{} : Bool}) -> {Nat.add(hit_acc(hi, k, ok), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), C.shift(w, 1n+k))) : Nat}:
  +y = Nat.add(lo, C.shift(w, hi))
  +a = Nat.add(t, C.shift(w, k))
  +by = N.le_trans(C.shift(w, 1n+k), C.shift(w, hi), y, WI.shift_mono(w, 1n+k, hi, N.lt_succ_le_succ(k, hi, h)), le_plus(lo, C.shift(w, hi)))
  %Equal.sym(Bool, Nat.is_lt(y, a), False{}, N.le_not_lt(y, a, N.le_trans(a, C.shift(w, 1n+k), y, hab, by))) : {Nat.add(hit_acc(hi, k, ok), b2n(_)) == b2n(Nat.is_lt(y, C.shift(w, 1n+k))) : Nat}
  %Equal.sym(Bool, Nat.is_lt(y, C.shift(w, 1n+k)), False{}, N.le_not_lt(y, C.shift(w, 1n+k), by)) : {Nat.add(hit_acc(hi, k, ok), 0n) == b2n(_) : Nat}
  fin_gt(hi, k, ok, h)

def term_cases(+w: Nat, +n: Nat, +k: Nat, +t: Nat, +lo: Nat, +hi: Nat, +hlo: {C.fits(w, lo) == True{} : Bool}, +ht: {Nat.is_lt(t, n) == True{} : Bool}, +hab: {Nat.is_le(Nat.add(t, C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}, +lt: Bool, +eq: Bool, +hlt: {Nat.is_lt(hi, k) == lt : Bool}, +heq: {Nat.is_eq(hi, k) == eq : Bool}) -> {Nat.add(hit_acc(hi, k, Bool.not(Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t)))), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, hi)), C.shift(w, 1n+k))) : Nat}:
  match lt eq:
    case True{} _:
      term_lt(w, k, t, lo, hi, Bool.not(Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t))), hlo, hab, hlt)
    case False{} True{}:
      %Equal.sym(Nat, hi, k, N.eq_from_is_eq(hi, k, heq)) : {Nat.add(hit_acc(_, k, Bool.not(Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t)))), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, _)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, _)), C.shift(w, 1n+k))) : Nat}
      %Equal.sym(Bool, Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t)), Nat.is_lt(lo, t), and_lt(lo, n, t, ht, Nat.is_lt(lo, t), {==})) : {Nat.add(hit_acc(k, k, Bool.not(_)), b2n(Nat.is_lt(Nat.add(lo, C.shift(w, k)), Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(Nat.add(lo, C.shift(w, k)), C.shift(w, 1n+k))) : Nat}
      term_eq(w, k, t, lo, hlo)
    case False{} False{}:
      term_gt(w, k, t, lo, hi, Bool.not(Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, t))), hab, N.lt_or_eq(k, hi, N.not_lt_le(hi, k, hlt), N.is_eq_sym_false(hi, k, heq)))

# THEOREM (one output, Lemire's branch): with t = 2^w mod n < n and
# k 2^w + t <= (k + 1) 2^w, y = x n draws k exactly when
# k 2^w + t <= y < (k + 1) 2^w
def term(+w: Nat, +n: Nat, +k: Nat, +y: Nat, +ht: {Nat.is_lt(SR.pow2mod(w, n), n) == True{} : Bool}, +hab: {Nat.is_le(Nat.add(SR.pow2mod(w, n), C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}) -> {Nat.add(SR.hit(SR.lemire(w, n, C.high(w, y), C.low(w, y)), k), b2n(Nat.is_lt(y, Nat.add(SR.pow2mod(w, n), C.shift(w, k))))) == b2n(Nat.is_lt(y, C.shift(w, 1n+k))) : Nat}:
  +lo = C.low(w, y)
  +hi = C.high(w, y)
  +t = SR.pow2mod(w, n)
  %Equal.sym(Nat, y, Nat.add(lo, C.shift(w, hi)), WI.low_high(w, y)) : {Nat.add(SR.hit(SR.lemire(w, n, hi, lo), k), b2n(Nat.is_lt(_, Nat.add(t, C.shift(w, k))))) == b2n(Nat.is_lt(_, C.shift(w, 1n+k))) : Nat}
  term_cases(w, n, k, t, lo, hi, WI.low_fits(w, y), ht, hab, Nat.is_lt(hi, k), Nat.is_eq(hi, k), {==}, {==})

# ---- summing over the outputs x < N ----

# #{x < N : x n < c}
def cnt_lt(+n: Nat, +c: Nat, N: Nat) -> Nat:
  match N:
    case 0n:
      0n
    case 1n+ +x:
      Nat.add(cnt_lt(n, c, x), b2n(Nat.is_lt(Nat.mul(x, n), c)))

# the draw is Lemire's when n is not a power of two
def draw_lemire(+w: Nat, +m: Nat, +x: Nat, +hp: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == False{} : Bool}) -> {SR.draw(w, x, 1n+m) == SR.lemire(w, 1n+m, C.high(w, Nat.mul(x, 1n+m)), C.low(w, Nat.mul(x, 1n+m))) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n), False{}, hp) : {SR.draw_pos(w, x, 1n+m, m, _) == SR.lemire(w, 1n+m, C.high(w, Nat.mul(x, 1n+m)), C.low(w, Nat.mul(x, 1n+m))) : Maybe<&2, Nat>}
  {==}

# (a + h) + (b + e) == (a + b) + (h + e)
def add4(+a: Nat, +h: Nat, +b: Nat, +e: Nat) -> {Nat.add(Nat.add(a, h), Nat.add(b, e)) == Nat.add(Nat.add(a, b), Nat.add(h, e)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, h), Nat.add(b, e)), Nat.add(a, Nat.add(h, Nat.add(b, e))), Nat.add(Nat.add(a, b), Nat.add(h, e)),
    N.add_assoc(a, h, Nat.add(b, e)),
    Equal.trans(Nat, Nat.add(a, Nat.add(h, Nat.add(b, e))), Nat.add(a, Nat.add(b, Nat.add(h, e))), Nat.add(Nat.add(a, b), Nat.add(h, e)),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(h, Nat.add(b, e)), Nat.add(b, Nat.add(h, e)),
        Equal.trans(Nat, Nat.add(h, Nat.add(b, e)), Nat.add(Nat.add(h, b), e), Nat.add(b, Nat.add(h, e)),
          Equal.sym(Nat, Nat.add(Nat.add(h, b), e), Nat.add(h, Nat.add(b, e)), N.add_assoc(h, b, e)),
          Equal.trans(Nat, Nat.add(Nat.add(h, b), e), Nat.add(Nat.add(b, h), e), Nat.add(b, Nat.add(h, e)),
            Equal.cong(Nat, Nat, z => Nat.add(z, e), Nat.add(h, b), Nat.add(b, h), N.add_comm(h, b)),
            N.add_assoc(b, h, e)))),
      Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(h, e)), Nat.add(a, Nat.add(b, Nat.add(h, e))), N.add_assoc(a, b, Nat.add(h, e)))))

# the Lemire outputs below N plus those with x n below the lower threshold
# are those with x n below the upper one
def sum_lemire(+w: Nat, +m: Nat, +k: Nat, +N: Nat, +hp: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == False{} : Bool}, +ht: {Nat.is_lt(SR.pow2mod(w, 1n+m), 1n+m) == True{} : Bool}, +hab: {Nat.is_le(Nat.add(SR.pow2mod(w, 1n+m), C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}) -> {Nat.add(SR.count(w, 1n+m, k, N), cnt_lt(1n+m, Nat.add(SR.pow2mod(w, 1n+m), C.shift(w, k)), N)) == cnt_lt(1n+m, C.shift(w, 1n+k), N) : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +x:
      +a = Nat.add(SR.pow2mod(w, 1n+m), C.shift(w, k))
      +b = C.shift(w, 1n+k)
      +h = SR.hit(SR.draw(w, x, 1n+m), k)
      +ea = b2n(Nat.is_lt(Nat.mul(x, 1n+m), a))
      Equal.trans(Nat, Nat.add(Nat.add(SR.count(w, 1n+m, k, x), h), Nat.add(cnt_lt(1n+m, a, x), ea)), Nat.add(Nat.add(SR.count(w, 1n+m, k, x), cnt_lt(1n+m, a, x)), Nat.add(h, ea)), Nat.add(cnt_lt(1n+m, b, x), b2n(Nat.is_lt(Nat.mul(x, 1n+m), b))),
        add4(SR.count(w, 1n+m, k, x), h, cnt_lt(1n+m, a, x), ea),
        Equal.trans(Nat, Nat.add(Nat.add(SR.count(w, 1n+m, k, x), cnt_lt(1n+m, a, x)), Nat.add(h, ea)), Nat.add(cnt_lt(1n+m, b, x), Nat.add(h, ea)), Nat.add(cnt_lt(1n+m, b, x), b2n(Nat.is_lt(Nat.mul(x, 1n+m), b))),
          Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(h, ea)), Nat.add(SR.count(w, 1n+m, k, x), cnt_lt(1n+m, a, x)), cnt_lt(1n+m, b, x), sum_lemire(w, m, k, x, hp, ht, hab)),
          Equal.cong(Nat, Nat, z => Nat.add(cnt_lt(1n+m, b, x), z), Nat.add(h, ea), b2n(Nat.is_lt(Nat.mul(x, 1n+m), b)),
            %Equal.sym(Maybe<&2, Nat>, SR.draw(w, x, 1n+m), SR.lemire(w, 1n+m, C.high(w, Nat.mul(x, 1n+m)), C.low(w, Nat.mul(x, 1n+m))), draw_lemire(w, m, x, hp)) : {Nat.add(SR.hit(_, k), ea) == b2n(Nat.is_lt(Nat.mul(x, 1n+m), b)) : Nat}
            term(w, 1n+m, k, Nat.mul(x, 1n+m), ht, hab))))

# ---- counting x n < c: min(N, ceil(c / n)) ----

# a + 1 <= b is a < b
def le_succ_lt(+a: Nat, +b: Nat) -> {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      N.zero_le(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_succ_lt(p, q)

# x n < c is x < ceil(c / n) = (c + n - 1) / n, n = 1 + bp
def lt_ceil(+bp: Nat, +x: Nat, +c: Nat) -> {Nat.is_lt(Nat.mul(x, 1n+bp), c) == Nat.is_lt(x, Nat.div(Nat.add(c, bp), 1n+bp)) : Bool}:
  +X = Nat.mul(x, 1n+bp)
  +D = Nat.div(Nat.add(c, bp), 1n+bp)
  Equal.trans(Bool, Nat.is_lt(X, c), Nat.is_le(1n+X, c), Nat.is_lt(x, D),
    Equal.sym(Bool, Nat.is_le(1n+X, c), Nat.is_lt(X, c), le_succ_lt(X, c)),
    Equal.trans(Bool, Nat.is_le(1n+X, c), Nat.is_le(Nat.add(bp, 1n+X), Nat.add(bp, c)), Nat.is_lt(x, D),
      Equal.sym(Bool, Nat.is_le(Nat.add(bp, 1n+X), Nat.add(bp, c)), Nat.is_le(1n+X, c), AR.le_add_cancel(bp, 1n+X, c)),
      Equal.trans(Bool, Nat.is_le(Nat.add(bp, 1n+X), Nat.add(bp, c)), Nat.is_le(1n+Nat.add(bp, X), Nat.add(c, bp)), Nat.is_lt(x, D),
        %N.add_succ(bp, X) : {Nat.is_le(Nat.add(bp, 1n+X), Nat.add(bp, c)) == Nat.is_le(_, Nat.add(c, bp)) : Bool}
        %N.add_comm(bp, c) : {Nat.is_le(Nat.add(bp, 1n+X), Nat.add(bp, c)) == Nat.is_le(Nat.add(bp, 1n+X), _) : Bool}
        {==},
        Equal.trans(Bool, Nat.is_le(1n+Nat.add(bp, X), Nat.add(c, bp)), Nat.is_le(1n+x, D), Nat.is_lt(x, D),
          Equal.sym(Bool, Nat.is_le(1n+x, D), Nat.is_le(1n+Nat.add(bp, X), Nat.add(c, bp)), AR.le_div(bp, 1n+x, Nat.add(c, bp))),
          le_succ_lt(x, D)))))

def min_zero(+n: Nat) -> {Nat.min(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# min(N + 1, C) = min(N, C) + [N < C]
def min_succ(+n: Nat, +c: Nat) -> {Nat.min(1n+n, c) == Nat.add(Nat.min(n, c), b2n(Nat.is_lt(n, c))) : Nat}:
  match n c:
    case _ 0n:
      %Equal.sym(Nat, Nat.min(n, 0n), 0n, min_zero(n)) : {0n == Nat.add(_, b2n(Nat.is_lt(n, 0n))) : Nat}
      %Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, N.not_lt_zero(n)) : {0n == Nat.add(0n, b2n(_)) : Nat}
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(1n+p, q), Nat.add(Nat.min(p, q), b2n(Nat.is_lt(p, q))), min_succ(p, q))

# THEOREM: #{x < N : x n < c} = min(N, ceil(c / n))
def cnt_min(+bp: Nat, +c: Nat, +N: Nat) -> {cnt_lt(1n+bp, c, N) == Nat.min(N, Nat.div(Nat.add(c, bp), 1n+bp)) : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +x:
      +D = Nat.div(Nat.add(c, bp), 1n+bp)
      Equal.trans(Nat, Nat.add(cnt_lt(1n+bp, c, x), b2n(Nat.is_lt(Nat.mul(x, 1n+bp), c))), Nat.add(Nat.min(x, D), b2n(Nat.is_lt(x, D))), Nat.min(1n+x, D),
        %Equal.sym(Nat, cnt_lt(1n+bp, c, x), Nat.min(x, D), cnt_min(bp, c, x)) : {Nat.add(_, b2n(Nat.is_lt(Nat.mul(x, 1n+bp), c))) == Nat.add(Nat.min(x, D), b2n(Nat.is_lt(x, D))) : Nat}
        %Equal.sym(Bool, Nat.is_lt(Nat.mul(x, 1n+bp), c), Nat.is_lt(x, D), lt_ceil(bp, x, c)) : {Nat.add(Nat.min(x, D), b2n(_)) == Nat.add(Nat.min(x, D), b2n(Nat.is_lt(x, D))) : Nat}
        {==},
        Equal.sym(Nat, Nat.min(1n+x, D), Nat.add(Nat.min(x, D), b2n(Nat.is_lt(x, D))), min_succ(x, D)))

# ---- Lemire's branch: the count ----

def dbl_add(+z: Nat) -> {Nat.double(z) == Nat.add(z, z) : Nat}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), N.add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      Equal.cong(Nat, Nat, x => 2n+x, Nat.double(p), Nat.add(p, p), dbl_add(p))

# Go's -n % n: 2^w mod n
def pm(+w: Nat, +m: Nat) -> {SR.pow2mod(w, 1n+m) == Nat.mod(C.shift(w, 1n), 1n+m) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+k:
      +S = C.shift(k, 1n)
      %Equal.sym(Nat, SR.pow2mod(k, 1n+m), Nat.mod(S, 1n+m), pm(k, m)) : {Nat.mod(Nat.double(_), 1n+m) == Nat.mod(Nat.double(S), 1n+m) : Nat}
      %Equal.sym(Nat, Nat.double(Nat.mod(S, 1n+m)), Nat.add(Nat.mod(S, 1n+m), Nat.mod(S, 1n+m)), dbl_add(Nat.mod(S, 1n+m))) : {Nat.mod(_, 1n+m) == Nat.mod(Nat.double(S), 1n+m) : Nat}
      %Equal.sym(Nat, Nat.double(S), Nat.add(S, S), dbl_add(S)) : {Nat.mod(Nat.add(Nat.mod(S, 1n+m), Nat.mod(S, 1n+m)), 1n+m) == Nat.mod(_, 1n+m) : Nat}
      Equal.trans(Nat, Nat.mod(Nat.add(Nat.mod(S, 1n+m), Nat.mod(S, 1n+m)), 1n+m), Nat.mod(Nat.add(S, Nat.mod(S, 1n+m)), 1n+m), Nat.mod(Nat.add(S, S), 1n+m),
        AR.mod_add_l(m, S, Nat.mod(S, 1n+m)),
        AR.mod_add_r(m, S, S))

# (q n + r) / n = q + r / n
def div_add_mul(+q: Nat, +m: Nat, +r: Nat) -> {Nat.div(Nat.add(Nat.mul(q, 1n+m), r), 1n+m) == Nat.add(q, Nat.div(r, 1n+m)) : Nat}:
  +rq = Nat.div(r, 1n+m)
  +rr = Nat.mod(r, 1n+m)
  %Equal.sym(Nat, r, Nat.add(Nat.mul(rq, 1n+m), rr), AR.dm_eq(m, r)) : {Nat.div(Nat.add(Nat.mul(q, 1n+m), _), 1n+m) == Nat.add(q, rq) : Nat}
  %N.add_assoc(Nat.mul(q, 1n+m), Nat.mul(rq, 1n+m), rr) : {Nat.div(_, 1n+m) == Nat.add(q, rq) : Nat}
  %NA.mul_add_right(q, rq, 1n+m) : {Nat.div(Nat.add(_, rr), 1n+m) == Nat.add(q, rq) : Nat}
  AR.div_of(Nat.add(q, rq), m, rr, AR.dm_lt(m, r))

def min_le(+n: Nat, +c: Nat, +h: {Nat.is_le(c, n) == True{} : Bool}) -> {Nat.min(n, c) == c : Nat}:
  match n c:
    case _ 0n:
      min_zero(n)
    case 0n 1n+q:
      Empty.absurd({Nat.min(0n, 1n+q) == 1n+q : Nat}, L.false_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(p, q), q, min_le(p, q, h))

# a <= b and c < d give a + c < b + d
def lt_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +hcd: {Nat.is_lt(c, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), WI.le_add_r(a, b, c, hab), N.lt_add_left(c, d, b, hcd))

# ceil((k + 1) 2^w / n) <= 2^w for k < n
def cb_le(+w: Nat, +m: Nat, +k: Nat, +hk: {Nat.is_lt(k, 1n+m) == True{} : Bool}) -> {Nat.is_le(Nat.div(Nat.add(C.shift(w, 1n+k), m), 1n+m), C.shift(w, 1n)) == True{} : Bool}:
  +W = C.shift(w, 1n)
  +b = C.shift(w, 1n+k)
  +hb = Equal.trans(Bool, Nat.is_le(b, Nat.mul(W, 1n+m)), Nat.is_le(Nat.mul(1n+k, W), Nat.mul(1n+m, W)), True{},
    %WI.shift_mul(w, 1n+k) : {Nat.is_le(b, Nat.mul(W, 1n+m)) == Nat.is_le(_, Nat.mul(1n+m, W)) : Bool}
    %NA.mul_comm(W, 1n+m) : {Nat.is_le(b, Nat.mul(W, 1n+m)) == Nat.is_le(b, _) : Bool}
    {==},
    LA.mul_le(1n+k, 1n+m, W, N.lt_succ_le_succ(k, 1n+m, hk)))
  +hlt = lt_add2(b, Nat.mul(W, 1n+m), m, 1n+m, hb, N.lt_succ(m))
  +hlt2 = Equal.trans(Bool, Nat.is_lt(Nat.add(b, m), Nat.mul(1n+W, 1n+m)), Nat.is_lt(Nat.add(b, m), Nat.add(Nat.mul(W, 1n+m), 1n+m)), True{},
    %N.add_comm(1n+m, Nat.mul(W, 1n+m)) : {Nat.is_lt(Nat.add(b, m), Nat.mul(1n+W, 1n+m)) == Nat.is_lt(Nat.add(b, m), _) : Bool}
    {==},
    hlt)
  +hnot = Equal.trans(Bool, Nat.is_le(1n+W, Nat.div(Nat.add(b, m), 1n+m)), Nat.is_le(Nat.mul(1n+W, 1n+m), Nat.add(b, m)), False{},
    AR.le_div(m, 1n+W, Nat.add(b, m)),
    N.lt_not_le(Nat.add(b, m), Nat.mul(1n+W, 1n+m), hlt2))
  N.lt_succ_le(Nat.div(Nat.add(b, m), 1n+m), W, N.not_le_lt(1n+W, Nat.div(Nat.add(b, m), 1n+m), hnot))

# t <= 2^w for t < n <= 2^w
def hab_of(+w: Nat, +m: Nat, +k: Nat, +hw: {C.fits(w, 1n+m) == True{} : Bool}) -> {Nat.is_le(Nat.add(SR.pow2mod(w, 1n+m), C.shift(w, k)), C.shift(w, 1n+k)) == True{} : Bool}:
  +W = C.shift(w, 1n)
  +t = SR.pow2mod(w, 1n+m)
  +ht = N.lt_le(t, W, N.lt_trans(t, 1n+m, W,
    %Equal.sym(Nat, SR.pow2mod(w, 1n+m), Nat.mod(W, 1n+m), pm(w, m)) : {Nat.is_lt(_, 1n+m) == True{} : Bool}
    AR.dm_lt(m, W),
    WI.lt_one(w, 1n, {==}, 1n+m, hw)))
  %Equal.sym(Nat, C.shift(w, 1n+k), Nat.add(W, C.shift(w, k)), WI.shift_add(w, 1n, k)) : {Nat.is_le(Nat.add(t, C.shift(w, k)), _) == True{} : Bool}
  WI.le_add_r(t, W, C.shift(w, k), ht)

# (k + 1) 2^w + m = q n + (t + k 2^w + m), q n + t = 2^w
def bm_eq(+w: Nat, +m: Nat, +k: Nat) -> {Nat.add(C.shift(w, 1n+k), m) == Nat.add(Nat.mul(Nat.div(C.shift(w, 1n), 1n+m), 1n+m), Nat.add(Nat.add(SR.pow2mod(w, 1n+m), C.shift(w, k)), m)) : Nat}:
  +W = C.shift(w, 1n)
  +S = C.shift(w, k)
  +qn = Nat.mul(Nat.div(W, 1n+m), 1n+m)
  +t = SR.pow2mod(w, 1n+m)
  %Equal.sym(Nat, C.shift(w, 1n+k), Nat.add(W, S), WI.shift_add(w, 1n, k)) : {Nat.add(_, m) == Nat.add(qn, Nat.add(Nat.add(t, S), m)) : Nat}
  %Equal.sym(Nat, W, Nat.add(qn, Nat.mod(W, 1n+m)), AR.dm_eq(m, W)) : {Nat.add(Nat.add(_, S), m) == Nat.add(qn, Nat.add(Nat.add(t, S), m)) : Nat}
  %pm(w, m) : {Nat.add(Nat.add(Nat.add(qn, _), S), m) == Nat.add(qn, Nat.add(Nat.add(t, S), m)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(qn, t), S), Nat.add(qn, Nat.add(t, S)), N.add_assoc(qn, t, S)) : {Nat.add(_, m) == Nat.add(qn, Nat.add(Nat.add(t, S), m)) : Nat}
  N.add_assoc(qn, Nat.add(t, S), m)

# THEOREM (Lemire's branch): floor(2^w / n) outputs draw k
def lemire_count(+w: Nat, +m: Nat, +k: Nat, +hp: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == False{} : Bool}, +hw: {C.fits(w, 1n+m) == True{} : Bool}, +hk: {Nat.is_lt(k, 1n+m) == True{} : Bool}) -> {SR.count(w, 1n+m, k, C.shift(w, 1n)) == Nat.div(C.shift(w, 1n), 1n+m) : Nat}:
  +W = C.shift(w, 1n)
  +t = SR.pow2mod(w, 1n+m)
  +a = Nat.add(t, C.shift(w, k))
  +b = C.shift(w, 1n+k)
  +q = Nat.div(W, 1n+m)
  +Ca = Nat.div(Nat.add(a, m), 1n+m)
  +Cb = Nat.div(Nat.add(b, m), 1n+m)
  +cnt = SR.count(w, 1n+m, k, W)
  +ht = Equal.trans(Bool, Nat.is_lt(t, 1n+m), Nat.is_lt(Nat.mod(W, 1n+m), 1n+m), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, 1n+m), t, Nat.mod(W, 1n+m), pm(w, m)), AR.dm_lt(m, W))
  +hab = hab_of(w, m, k, hw)
  +hcb = cb_le(w, m, k, hk)
  +bq = Equal.trans(Nat, Cb, Nat.div(Nat.add(Nat.mul(q, 1n+m), Nat.add(a, m)), 1n+m), Nat.add(q, Ca),
    Equal.cong(Nat, Nat, z => Nat.div(z, 1n+m), Nat.add(b, m), Nat.add(Nat.mul(q, 1n+m), Nat.add(a, m)), bm_eq(w, m, k)),
    div_add_mul(q, m, Nat.add(a, m)))
  +hca = Equal.trans(Bool, Nat.is_le(Ca, Cb), Nat.is_le(Ca, Nat.add(q, Ca)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(Ca, z), Cb, Nat.add(q, Ca), bq), le_plus(q, Ca))
  +ma = min_le(W, Ca, N.le_trans(Ca, Cb, W, hca, hcb))
  +mb = min_le(W, Cb, hcb)
  UA.add_cancel_r(cnt, q, Ca,
    Equal.trans(Nat, Nat.add(cnt, Ca), Nat.add(cnt, cnt_lt(1n+m, a, W)), Nat.add(q, Ca),
      Equal.cong(Nat, Nat, z => Nat.add(cnt, z), Ca, cnt_lt(1n+m, a, W),
        Equal.trans(Nat, Ca, Nat.min(W, Ca), cnt_lt(1n+m, a, W), Equal.sym(Nat, Nat.min(W, Ca), Ca, ma), Equal.sym(Nat, cnt_lt(1n+m, a, W), Nat.min(W, Ca), cnt_min(m, a, W)))),
      Equal.trans(Nat, Nat.add(cnt, cnt_lt(1n+m, a, W)), cnt_lt(1n+m, b, W), Nat.add(q, Ca),
        sum_lemire(w, m, k, W, hp, ht, hab),
        Equal.trans(Nat, cnt_lt(1n+m, b, W), Nat.min(W, Cb), Nat.add(q, Ca),
          cnt_min(m, b, W),
          Equal.trans(Nat, Nat.min(W, Cb), Cb, Nat.add(q, Ca), mb, bq)))))
