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

# ---- the mask branch: n = 2^j, x & (n - 1) ----

# #{x < N : and_bits(w, x, m) == k}
def cm(+w: Nat, +m: Nat, +k: Nat, N: Nat) -> Nat:
  match N:
    case 0n:
      0n
    case 1n+ +x:
      Nat.add(cm(w, m, k, x), b2n(Nat.is_eq(SR.and_bits(w, x, m), k)))

# the same count taken over the pairs 2y, 2y + 1 with y < N
def cm2(+w: Nat, +m: Nat, +k: Nat, N: Nat) -> Nat:
  match N:
    case 0n:
      0n
    case 1n+ +y:
      Nat.add(cm2(w, m, k, y), Nat.add(b2n(Nat.is_eq(SR.and_bits(w, Nat.double(y), m), k)), b2n(Nat.is_eq(SR.and_bits(w, 1n+Nat.double(y), m), k))))

def split(+w: Nat, +m: Nat, +k: Nat, +N: Nat) -> {cm(w, m, k, Nat.double(N)) == cm2(w, m, k, N) : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +y:
      +f0 = b2n(Nat.is_eq(SR.and_bits(w, Nat.double(y), m), k))
      +f1 = b2n(Nat.is_eq(SR.and_bits(w, 1n+Nat.double(y), m), k))
      Equal.trans(Nat, Nat.add(Nat.add(cm(w, m, k, Nat.double(y)), f0), f1), Nat.add(cm(w, m, k, Nat.double(y)), Nat.add(f0, f1)), Nat.add(cm2(w, m, k, y), Nat.add(f0, f1)),
        N.add_assoc(cm(w, m, k, Nat.double(y)), f0, f1),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(f0, f1)), cm(w, m, k, Nat.double(y)), cm2(w, m, k, y), split(w, m, k, y)))

# [2a == k] + [2a + 1 == k] == [a == k / 2]
def pair_eq(+a: Nat, +k: Nat) -> {Nat.add(b2n(Nat.is_eq(Nat.double(a), k)), b2n(Nat.is_eq(1n+Nat.double(a), k))) == b2n(Nat.is_eq(a, C.half(k))) : Nat}:
  match a k:
    case 0n 0n:
      {==}
    case 0n 1n:
      {==}
    case 0n 2n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n:
      {==}
    case 1n+p 2n+q:
      pair_eq(p, q)

def bit_dbl0(+y: Nat) -> {C.bit(Nat.double(y)) == 0n : Nat}:
  WI.bit_dbl(0n, y)

def half_dbl0(+y: Nat) -> {C.half(Nat.double(y)) == y : Nat}:
  WI.half_dbl(0n, y)

def bit_dbl1(+y: Nat) -> {C.bit(1n+Nat.double(y)) == 1n : Nat}:
  WI.bit_dbl(1n, y)

def half_dbl1(+y: Nat) -> {C.half(1n+Nat.double(y)) == y : Nat}:
  WI.half_dbl(1n, y)

# with m = 2h + 1: the pair 2y, 2y + 1 draws k once exactly when y draws k / 2
# one width lower with h
def pair_and(+v: Nat, +h: Nat, +k: Nat, +y: Nat) -> {Nat.add(b2n(Nat.is_eq(SR.and_bits(1n+v, Nat.double(y), 1n+Nat.double(h)), k)), b2n(Nat.is_eq(SR.and_bits(1n+v, 1n+Nat.double(y), 1n+Nat.double(h)), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}:
  +M = {1n+Nat.double(h) : Nat}
  %Equal.sym(Nat, C.bit(M), 1n, bit_dbl1(h)) : {Nat.add(b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(Nat.double(y)), _), Nat.double(SR.and_bits(v, C.half(Nat.double(y)), C.half(M)))), k)), b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(1n+Nat.double(y)), _), Nat.double(SR.and_bits(v, C.half(1n+Nat.double(y)), C.half(M)))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  %Equal.sym(Nat, C.half(M), h, half_dbl1(h)) : {Nat.add(b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(Nat.double(y)), 1n), Nat.double(SR.and_bits(v, C.half(Nat.double(y)), _))), k)), b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(1n+Nat.double(y)), 1n), Nat.double(SR.and_bits(v, C.half(1n+Nat.double(y)), _))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  %Equal.sym(Nat, C.bit(Nat.double(y)), 0n, bit_dbl0(y)) : {Nat.add(b2n(Nat.is_eq(Nat.add(Nat.mul(_, 1n), Nat.double(SR.and_bits(v, C.half(Nat.double(y)), h))), k)), b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(1n+Nat.double(y)), 1n), Nat.double(SR.and_bits(v, C.half(1n+Nat.double(y)), h))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  %Equal.sym(Nat, C.half(Nat.double(y)), y, half_dbl0(y)) : {Nat.add(b2n(Nat.is_eq(Nat.add(Nat.mul(0n, 1n), Nat.double(SR.and_bits(v, _, h))), k)), b2n(Nat.is_eq(Nat.add(Nat.mul(C.bit(1n+Nat.double(y)), 1n), Nat.double(SR.and_bits(v, C.half(1n+Nat.double(y)), h))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  %Equal.sym(Nat, C.bit(1n+Nat.double(y)), 1n, bit_dbl1(y)) : {Nat.add(b2n(Nat.is_eq(Nat.double(SR.and_bits(v, y, h)), k)), b2n(Nat.is_eq(Nat.add(Nat.mul(_, 1n), Nat.double(SR.and_bits(v, C.half(1n+Nat.double(y)), h))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  %Equal.sym(Nat, C.half(1n+Nat.double(y)), y, half_dbl1(y)) : {Nat.add(b2n(Nat.is_eq(Nat.double(SR.and_bits(v, y, h)), k)), b2n(Nat.is_eq(Nat.add(1n, Nat.double(SR.and_bits(v, _, h))), k))) == b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))) : Nat}
  pair_eq(SR.and_bits(v, y, h), k)

# the pairs one width up count what the lower width counts
def pairs(+v: Nat, +h: Nat, +k: Nat, +N: Nat) -> {cm2(1n+v, 1n+Nat.double(h), k, N) == cm(v, h, C.half(k), N) : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +y:
      Equal.trans(Nat, Nat.add(cm2(1n+v, 1n+Nat.double(h), k, y), Nat.add(b2n(Nat.is_eq(SR.and_bits(1n+v, Nat.double(y), 1n+Nat.double(h)), k)), b2n(Nat.is_eq(SR.and_bits(1n+v, 1n+Nat.double(y), 1n+Nat.double(h)), k)))), Nat.add(cm(v, h, C.half(k), y), Nat.add(b2n(Nat.is_eq(SR.and_bits(1n+v, Nat.double(y), 1n+Nat.double(h)), k)), b2n(Nat.is_eq(SR.and_bits(1n+v, 1n+Nat.double(y), 1n+Nat.double(h)), k)))), Nat.add(cm(v, h, C.half(k), y), b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k)))),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(b2n(Nat.is_eq(SR.and_bits(1n+v, Nat.double(y), 1n+Nat.double(h)), k)), b2n(Nat.is_eq(SR.and_bits(1n+v, 1n+Nat.double(y), 1n+Nat.double(h)), k)))), cm2(1n+v, 1n+Nat.double(h), k, y), cm(v, h, C.half(k), y), pairs(v, h, k, y)),
        Equal.cong(Nat, Nat, z => Nat.add(cm(v, h, C.half(k), y), z), Nat.add(b2n(Nat.is_eq(SR.and_bits(1n+v, Nat.double(y), 1n+Nat.double(h)), k)), b2n(Nat.is_eq(SR.and_bits(1n+v, 1n+Nat.double(y), 1n+Nat.double(h)), k))), b2n(Nat.is_eq(SR.and_bits(v, y, h), C.half(k))), pair_and(v, h, k, y)))

# x & 0 == 0
def and0(+w: Nat, +x: Nat) -> {SR.and_bits(w, x, 0n) == 0n : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+v:
      %Equal.sym(Nat, Nat.mul(C.bit(x), 0n), 0n, NA.mul_zero(C.bit(x))) : {Nat.add(_, Nat.double(SR.and_bits(v, C.half(x), 0n))) == 0n : Nat}
      %Equal.sym(Nat, SR.and_bits(v, C.half(x), 0n), 0n, and0(v, C.half(x))) : {Nat.add(0n, Nat.double(_)) == 0n : Nat}
      {==}

# n = 1: every output draws 0
def cm0(+w: Nat, +N: Nat) -> {cm(w, 0n, 0n, N) == N : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +x:
      %Equal.sym(Nat, SR.and_bits(w, x, 0n), 0n, and0(w, x)) : {Nat.add(cm(w, 0n, 0n, x), b2n(Nat.is_eq(_, 0n))) == 1n+x : Nat}
      %Equal.sym(Nat, cm(w, 0n, 0n, x), x, cm0(w, x)) : {Nat.add(_, 1n) == 1n+x : Nat}
      Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, N.add_succ(x, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, 0n), x, N.add_zero(x)))

def cm0k(+w: Nat, +k: Nat, +N: Nat, +hk: {Nat.is_lt(k, 1n) == True{} : Bool}) -> {cm(w, 0n, k, N) == N : Nat}:
  match k:
    case 0n:
      cm0(w, N)
    case 1n+q:
      Empty.absurd({cm(w, 0n, 1n+q, N) == N : Nat}, N.lt_zero_absurd(q, hk))

def div_one(+N: Nat) -> {Nat.div(N, 1n) == N : Nat}:
  %Equal.sym(Nat, N, Nat.add(Nat.mul(N, 1n), 0n), Equal.trans(Nat, N, Nat.mul(N, 1n), Nat.add(Nat.mul(N, 1n), 0n), Equal.sym(Nat, Nat.mul(N, 1n), N, NA.mul_one(N)), Equal.sym(Nat, Nat.add(Nat.mul(N, 1n), 0n), Nat.mul(N, 1n), N.add_zero(Nat.mul(N, 1n))))) : {Nat.div(_, 1n) == N : Nat}
  AR.div_of(N, 0n, 0n, {==})

# 2a / 2n = a / n
def div_double(+a: Nat, +h: Nat) -> {Nat.div(Nat.double(a), 2n+Nat.double(h)) == Nat.div(a, 1n+h) : Nat}:
  +q = Nat.div(a, 1n+h)
  +r = Nat.mod(a, 1n+h)
  %Equal.sym(Nat, a, Nat.add(Nat.mul(q, 1n+h), r), AR.dm_eq(h, a)) : {Nat.div(Nat.double(_), 2n+Nat.double(h)) == q : Nat}
  %N.add_double(Nat.mul(q, 1n+h), r) : {Nat.div(_, 2n+Nat.double(h)) == q : Nat}
  %Equal.sym(Nat, Nat.double(Nat.mul(q, 1n+h)), Nat.mul(q, Nat.double(1n+h)), WI.dbl_mul(q, 1n+h)) : {Nat.div(Nat.add(_, Nat.double(r)), 2n+Nat.double(h)) == q : Nat}
  AR.div_of(q, 1n+Nat.double(h), Nat.double(r), N.double_lt(r, 1n+h, AR.dm_lt(h, a)))

# bit * bit == bit
def bitsq_b(+b: Nat, +h: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.mul(b, b) == b : Nat}:
  match b:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+q:
      Empty.absurd({Nat.mul(2n+q, 2n+q) == 2n+q : Nat}, L.false_true(h))

# x & x is the low w bits of x
def and_self(+w: Nat, +x: Nat) -> {SR.and_bits(w, x, x) == C.low(w, x) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+v:
      %Equal.sym(Nat, Nat.mul(C.bit(x), C.bit(x)), C.bit(x), bitsq_b(C.bit(x), WI.bit_le1(x))) : {Nat.add(_, Nat.double(SR.and_bits(v, C.half(x), C.half(x)))) == Nat.add(C.bit(x), Nat.double(C.low(v, C.half(x)))) : Nat}
      Equal.cong(Nat, Nat, z => Nat.add(C.bit(x), Nat.double(z)), SR.and_bits(v, C.half(x), C.half(x)), C.low(v, C.half(x)), and_self(v, C.half(x)))

def dbl0(+z: Nat, +h: {Nat.double(z) == 0n : Nat}) -> {z == 0n : Nat}:
  match z:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.succ_zero(1n+Nat.double(p), h))

# m = bit(m) + 2 half(m)
def decomp(+m: Nat, +b: Nat, +h: Nat, +hb: {C.bit(m) == b : Nat}, +hh: {C.half(m) == h : Nat}) -> {m == Nat.add(b, Nat.double(h)) : Nat}:
  Equal.trans(Nat, m, Nat.add(C.bit(m), Nat.double(C.half(m))), Nat.add(b, Nat.double(h)), WI.hb(m),
    Equal.trans(Nat, Nat.add(C.bit(m), Nat.double(C.half(m))), Nat.add(b, Nat.double(C.half(m))), Nat.add(b, Nat.double(h)),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(C.half(m))), C.bit(m), b, hb),
      Equal.cong(Nat, Nat, z => Nat.add(b, Nat.double(z)), C.half(m), h, hh)))

# n = 2h + 2, m = 2h + 1: n & m is twice (h + 1) & h one width lower
def and_even(+w: Nat, +h: Nat) -> {SR.and_bits(1n+w, 2n+Nat.double(h), 1n+Nat.double(h)) == Nat.double(SR.and_bits(w, 1n+h, h)) : Nat}:
  %Equal.sym(Nat, C.bit(Nat.double(h)), 0n, bit_dbl0(h)) : {Nat.add(Nat.mul(_, C.bit(1n+Nat.double(h))), Nat.double(SR.and_bits(w, 1n+C.half(Nat.double(h)), C.half(1n+Nat.double(h))))) == Nat.double(SR.and_bits(w, 1n+h, h)) : Nat}
  %Equal.sym(Nat, C.half(Nat.double(h)), h, half_dbl0(h)) : {Nat.add(Nat.mul(0n, C.bit(1n+Nat.double(h))), Nat.double(SR.and_bits(w, 1n+_, C.half(1n+Nat.double(h))))) == Nat.double(SR.and_bits(w, 1n+h, h)) : Nat}
  %Equal.sym(Nat, C.half(1n+Nat.double(h)), h, half_dbl1(h)) : {Nat.add(Nat.mul(0n, C.bit(1n+Nat.double(h))), Nat.double(SR.and_bits(w, 1n+h, _))) == Nat.double(SR.and_bits(w, 1n+h, h)) : Nat}
  {==}

# n = 2g + 3, m = 2g + 2: n & m is twice the low bits of g + 1
def and_odd(+w: Nat, +g: Nat) -> {SR.and_bits(1n+w, 3n+Nat.double(g), 2n+Nat.double(g)) == Nat.double(C.low(w, 1n+g)) : Nat}:
  %Equal.sym(Nat, C.bit(Nat.double(g)), 0n, bit_dbl0(g)) : {Nat.add(Nat.mul(C.bit(1n+Nat.double(g)), _), Nat.double(SR.and_bits(w, 1n+C.half(1n+Nat.double(g)), 1n+C.half(Nat.double(g))))) == Nat.double(C.low(w, 1n+g)) : Nat}
  %Equal.sym(Nat, C.half(Nat.double(g)), g, half_dbl0(g)) : {Nat.add(Nat.mul(C.bit(1n+Nat.double(g)), 0n), Nat.double(SR.and_bits(w, 1n+C.half(1n+Nat.double(g)), 1n+_))) == Nat.double(C.low(w, 1n+g)) : Nat}
  %Equal.sym(Nat, C.half(1n+Nat.double(g)), g, half_dbl1(g)) : {Nat.add(Nat.mul(C.bit(1n+Nat.double(g)), 0n), Nat.double(SR.and_bits(w, 1n+_, 1n+g))) == Nat.double(C.low(w, 1n+g)) : Nat}
  %Equal.sym(Nat, C.bit(1n+Nat.double(g)), 1n, bit_dbl1(g)) : {Nat.add(Nat.mul(_, 0n), Nat.double(SR.and_bits(w, 1n+g, 1n+g))) == Nat.double(C.low(w, 1n+g)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.double(z), SR.and_bits(w, 1n+g, 1n+g), C.low(w, 1n+g), and_self(w, 1n+g))

# THEOREM (the mask branch): with n = 1 + m, n & m == 0 and n < 2^v, each
# k < n is the low bits of floor(2^v / n) outputs
def mask(+v: Nat, +m: Nat, +k: Nat, +b: Nat, +h: Nat, +hb: {C.bit(m) == b : Nat}, +hh: {C.half(m) == h : Nat}, +hp: {SR.and_bits(v, 1n+m, m) == 0n : Nat}, +hw: {C.fits(v, 1n+m) == True{} : Bool}, +hk: {Nat.is_lt(k, 1n+m) == True{} : Bool}) -> {cm(v, m, k, C.shift(v, 1n)) == Nat.div(C.shift(v, 1n), 1n+m) : Nat}:
  match v:
    case 0n:
      Empty.absurd({cm(0n, m, k, 1n) == Nat.div(1n, 1n+m) : Nat}, L.false_true(hw))
    case 1n+w:
      match b h:
        case 0n 0n:
          +hm = decomp(m, 0n, 0n, hb, hh)
          %Equal.sym(Nat, m, 0n, hm) : {cm(1n+w, _, k, C.shift(1n+w, 1n)) == Nat.div(C.shift(1n+w, 1n), 1n+_) : Nat}
          Equal.trans(Nat, cm(1n+w, 0n, k, C.shift(1n+w, 1n)), C.shift(1n+w, 1n), Nat.div(C.shift(1n+w, 1n), 1n),
            cm0k(1n+w, k, C.shift(1n+w, 1n), Equal.trans(Bool, Nat.is_lt(k, 1n), Nat.is_lt(k, 1n+m), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(k, 1n+z), 0n, m, Equal.sym(Nat, m, 0n, hm)), hk)),
            Equal.sym(Nat, Nat.div(C.shift(1n+w, 1n), 1n), C.shift(1n+w, 1n), div_one(C.shift(1n+w, 1n))))
        case 0n 1n+g:
          +hm = decomp(m, 0n, 1n+g, hb, hh)
          +hp2 = Equal.trans(Nat, SR.and_bits(1n+w, 3n+Nat.double(g), 2n+Nat.double(g)), SR.and_bits(1n+w, 1n+m, m), 0n, Equal.cong(Nat, Nat, z => SR.and_bits(1n+w, 1n+z, z), 2n+Nat.double(g), m, Equal.sym(Nat, m, 2n+Nat.double(g), hm)), hp)
          +hw2 = Equal.trans(Bool, C.fits(w, 1n+g), C.fits(1n+w, 1n+m), True{},
            Equal.trans(Bool, C.fits(w, 1n+g), C.fits(w, 1n+C.half(1n+Nat.double(g))), C.fits(1n+w, 1n+m),
              Equal.cong(Nat, Bool, z => C.fits(w, 1n+z), g, C.half(1n+Nat.double(g)), Equal.sym(Nat, C.half(1n+Nat.double(g)), g, half_dbl1(g))),
              Equal.cong(Nat, Bool, z => C.fits(1n+w, 1n+z), 2n+Nat.double(g), m, Equal.sym(Nat, m, 2n+Nat.double(g), hm))),
            hw)
          +zero = Equal.trans(Nat, Nat.double(1n+g), Nat.double(C.low(w, 1n+g)), 0n,
            Equal.cong(Nat, Nat, z => Nat.double(z), 1n+g, C.low(w, 1n+g), Equal.sym(Nat, C.low(w, 1n+g), 1n+g, WI.low_fit(w, 1n+g, hw2))),
            Equal.trans(Nat, Nat.double(C.low(w, 1n+g)), SR.and_bits(1n+w, 3n+Nat.double(g), 2n+Nat.double(g)), 0n, Equal.sym(Nat, SR.and_bits(1n+w, 3n+Nat.double(g), 2n+Nat.double(g)), Nat.double(C.low(w, 1n+g)), and_odd(w, g)), hp2))
          Empty.absurd({cm(1n+w, m, k, C.shift(1n+w, 1n)) == Nat.div(C.shift(1n+w, 1n), 1n+m) : Nat}, N.succ_zero(g, dbl0(1n+g, zero)))
        case 1n _:
          +hm = decomp(m, 1n, h, hb, hh)
          +W = C.shift(w, 1n)
          +hp2 = Equal.trans(Nat, SR.and_bits(1n+w, 2n+Nat.double(h), 1n+Nat.double(h)), SR.and_bits(1n+w, 1n+m, m), 0n, Equal.cong(Nat, Nat, z => SR.and_bits(1n+w, 1n+z, z), 1n+Nat.double(h), m, Equal.sym(Nat, m, 1n+Nat.double(h), hm)), hp)
          +hp3 = dbl0(SR.and_bits(w, 1n+h, h), Equal.trans(Nat, Nat.double(SR.and_bits(w, 1n+h, h)), SR.and_bits(1n+w, 2n+Nat.double(h), 1n+Nat.double(h)), 0n, Equal.sym(Nat, SR.and_bits(1n+w, 2n+Nat.double(h), 1n+Nat.double(h)), Nat.double(SR.and_bits(w, 1n+h, h)), and_even(w, h)), hp2))
          +hw3 = Equal.trans(Bool, C.fits(w, 1n+h), C.fits(1n+w, 1n+m), True{},
            Equal.trans(Bool, C.fits(w, 1n+h), C.fits(w, 1n+C.half(Nat.double(h))), C.fits(1n+w, 1n+m),
              Equal.cong(Nat, Bool, z => C.fits(w, 1n+z), h, C.half(Nat.double(h)), Equal.sym(Nat, C.half(Nat.double(h)), h, half_dbl0(h))),
              Equal.cong(Nat, Bool, z => C.fits(1n+w, 1n+z), 1n+Nat.double(h), m, Equal.sym(Nat, m, 1n+Nat.double(h), hm))),
            hw)
          +hk3 = Equal.trans(Bool, Nat.is_lt(C.half(k), 1n+h), Nat.is_lt(k, 1n+m), True{},
            Equal.trans(Bool, Nat.is_lt(C.half(k), 1n+h), Nat.is_lt(k, Nat.double(1n+h)), Nat.is_lt(k, 1n+m), WI.lt_half(k, 1n+h),
              Equal.cong(Nat, Bool, z => Nat.is_lt(k, 1n+z), 1n+Nat.double(h), m, Equal.sym(Nat, m, 1n+Nat.double(h), hm))),
            hk)
          %Equal.sym(Nat, m, 1n+Nat.double(h), hm) : {cm(1n+w, _, k, Nat.double(W)) == Nat.div(Nat.double(W), 1n+_) : Nat}
          Equal.trans(Nat, cm(1n+w, 1n+Nat.double(h), k, Nat.double(W)), cm2(1n+w, 1n+Nat.double(h), k, W), Nat.div(Nat.double(W), 2n+Nat.double(h)),
            split(1n+w, 1n+Nat.double(h), k, W),
            Equal.trans(Nat, cm2(1n+w, 1n+Nat.double(h), k, W), cm(w, h, C.half(k), W), Nat.div(Nat.double(W), 2n+Nat.double(h)),
              pairs(w, h, k, W),
              Equal.trans(Nat, cm(w, h, C.half(k), W), Nat.div(W, 1n+h), Nat.div(Nat.double(W), 2n+Nat.double(h)),
                mask(w, h, C.half(k), C.bit(h), C.half(h), {==}, {==}, hp3, hw3, hk3),
                Equal.sym(Nat, Nat.div(Nat.double(W), 2n+Nat.double(h)), Nat.div(W, 1n+h), div_double(W, h)))))
        case 2n+q _:
          Empty.absurd({cm(1n+w, m, k, C.shift(1n+w, 1n)) == Nat.div(C.shift(1n+w, 1n), 1n+m) : Nat}, L.false_true(Equal.trans(Bool, Nat.is_le(2n+q, 1n), Nat.is_le(C.bit(m), 1n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n), 2n+q, C.bit(m), Equal.sym(Nat, C.bit(m), 2n+q, hb)), WI.bit_le1(m))))

# ---- both branches ----

# the draw is the mask when n is a power of two
def draw_mask(+w: Nat, +m: Nat, +x: Nat, +hp: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == True{} : Bool}) -> {SR.draw(w, x, 1n+m) == Some{SR.and_bits(w, x, m)} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n), True{}, hp) : {SR.draw_pos(w, x, 1n+m, m, _) == Some{SR.and_bits(w, x, m)} : Maybe<&2, Nat>}
  {==}

def count_mask(+w: Nat, +m: Nat, +k: Nat, +N: Nat, +hp: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == True{} : Bool}) -> {SR.count(w, 1n+m, k, N) == cm(w, m, k, N) : Nat}:
  match N:
    case 0n:
      {==}
    case 1n+ +x:
      %Equal.sym(Nat, SR.count(w, 1n+m, k, x), cm(w, m, k, x), count_mask(w, m, k, x, hp)) : {Nat.add(_, SR.hit(SR.draw(w, x, 1n+m), k)) == Nat.add(cm(w, m, k, x), b2n(Nat.is_eq(SR.and_bits(w, x, m), k))) : Nat}
      %Equal.sym(Maybe<&2, Nat>, SR.draw(w, x, 1n+m), Some{SR.and_bits(w, x, m)}, draw_mask(w, m, x, hp)) : {Nat.add(cm(w, m, k, x), SR.hit(_, k)) == Nat.add(cm(w, m, k, x), b2n(Nat.is_eq(SR.and_bits(w, x, m), k))) : Nat}
      {==}

def unbiased_c(+w: Nat, +m: Nat, +k: Nat, +hw: {C.fits(w, 1n+m) == True{} : Bool}, +hk: {Nat.is_lt(k, 1n+m) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n) == c : Bool}) -> {SR.count(w, 1n+m, k, C.shift(w, 1n)) == Nat.div(C.shift(w, 1n), 1n+m) : Nat}:
  match c:
    case False{}:
      lemire_count(w, m, k, hc, hw, hk)
    case True{}:
      Equal.trans(Nat, SR.count(w, 1n+m, k, C.shift(w, 1n)), cm(w, m, k, C.shift(w, 1n)), Nat.div(C.shift(w, 1n), 1n+m),
        count_mask(w, m, k, C.shift(w, 1n), hc),
        mask(w, m, k, C.bit(m), C.half(m), {==}, {==}, N.eq_from_is_eq(SR.and_bits(w, 1n+m, m), 0n, hc), hw, hk))

# THEOREM (Lemire.unbiased): for every width w, bound 0 < n < 2^w and
# k < n, exactly floor(2^w / n) of the 2^w outputs draw k
def unbiased(+w: Nat, +n: Nat, +k: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(w, n) == True{} : Bool}, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> {SR.count(w, n, k, C.shift(w, 1n)) == Nat.div(C.shift(w, 1n), n) : Nat}:
  match n:
    case 0n:
      Empty.absurd({SR.count(w, 0n, k, C.shift(w, 1n)) == Nat.div(C.shift(w, 1n), 0n) : Nat}, L.false_true(hn))
    case 1n+m:
      unbiased_c(w, m, k, hw, hk, Nat.is_eq(SR.and_bits(w, 1n+m, m), 0n), {==})
