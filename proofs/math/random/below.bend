import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/rand.bend as SR
import ../../../spec/math/random/source.bend as SRC
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as LA
import ../typed/width.bend as WI
import ../typed/w64m128.bend as M128
import ../typed/w64add.bend as WA
import ./lemire.bend as LE
import ../../lib/lemmas/proofs/nat_algebra.bend as NA

# Every draw the specification accepts, and its last candidate, is below n:
# so is the bounded draw from any source (and, by Uint64n.value, uint64n).

# x & m <= m
def and_le(+w: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(SR.and_bits(w, a, b), b) == True{} : Bool}:
  match w:
    case 0n:
      N.zero_le(b)
    case 1n+p:
      +hb = WI.hb(b)
      +h1 = WA.mul_le1(C.bit(a), C.bit(b), WI.bit_le1(a))
      +h2 = N.double_le(SR.and_bits(p, C.half(a), C.half(b)), C.half(b), and_le(p, C.half(a), C.half(b)))
      +h3 = N.le_trans(Nat.add(Nat.mul(C.bit(a), C.bit(b)), Nat.double(SR.and_bits(p, C.half(a), C.half(b)))), Nat.add(C.bit(b), Nat.double(SR.and_bits(p, C.half(a), C.half(b)))), Nat.add(C.bit(b), Nat.double(C.half(b))),
        WI.le_add_r(Nat.mul(C.bit(a), C.bit(b)), C.bit(b), Nat.double(SR.and_bits(p, C.half(a), C.half(b))), h1),
        N.le_add_left(Nat.double(SR.and_bits(p, C.half(a), C.half(b))), Nat.double(C.half(b)), C.bit(b), h2))
      %Equal.sym(Nat, b, Nat.add(C.bit(b), Nat.double(C.half(b))), hb) : {Nat.is_le(Nat.add(Nat.mul(C.bit(a), C.bit(b)), Nat.double(SR.and_bits(p, C.half(a), C.half(b)))), _) == True{} : Bool}
      h3

# x < 2^64 and n > 0: floor(x n / 2^64) < n
def high_lt_c(+x: Nat, +n: Nat, +y: Nat, +hy: {Nat.is_lt(y, C.shift(64n, n)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(C.high(64n, y), n) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h = C.high(64n, y)
      +ge = N.le_trans(C.shift(64n, n), C.shift(64n, h), y, WI.shift_mono(64n, n, h, N.not_lt_le(h, n, hc)),
        %Equal.sym(Nat, y, Nat.add(C.low(64n, y), C.shift(64n, h)), WI.low_high(64n, y)) : {Nat.is_le(C.shift(64n, h), _) == True{} : Bool}
        LE.le_plus(C.low(64n, y), C.shift(64n, h)))
      Empty.absurd({False{} == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(y, C.shift(64n, n)), True{}, Equal.sym(Bool, Nat.is_lt(y, C.shift(64n, n)), False{}, N.le_not_lt(y, C.shift(64n, n), ge)), hy)))

# a < n + a for n > 0
def lt_plus(+a: Nat, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(n, a)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(a, Nat.add(n, a)), Nat.is_lt(0n, n), True{}, WI.lt_cancel_r(0n, n, a), hn)

# x < 2^64: x n < 2^64 n
def prod_lt(+x: Nat, +n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +hx: {C.fits(64n, x) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, n), C.shift(64n, n)) == True{} : Bool}:
  +W = C.shift(64n, one)
  +hw = WI.lt_one(64n, one, h1, x, hx)
  +hle = LA.mul_le(1n+x, W, n, N.lt_succ_le_succ(x, W, hw))
  +hlt = N.lt_le_trans(Nat.mul(x, n), Nat.mul(1n+x, n), Nat.mul(W, n), lt_plus(Nat.mul(x, n), n, hn), hle)
  %Equal.sym(Nat, C.shift(64n, n), Nat.mul(n, W), WI.shift_mul_one(64n, one, h1, n)) : {Nat.is_lt(Nat.mul(x, n), _) == True{} : Bool}
  %NA.mul_comm(W, n) : {Nat.is_lt(Nat.mul(x, n), _) == True{} : Bool}
  hlt

# x < 2^64 and n > 0: floor(x n / 2^64) < n
def high_lt(+x: Nat, +n: Nat, +hx: {C.fits(64n, x) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(C.high(64n, Nat.mul(x, n)), n) == True{} : Bool}:
  high_lt_c(x, n, Nat.mul(x, n), prod_lt(x, n, 1n, {==}, hx, hn), Nat.is_lt(C.high(64n, Nat.mul(x, n)), n), {==})

def pfst(-S: Data, p: Nat & S) -> Nat:
  (k, s) = p
  k

def some_or(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def is_some(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def none_some(+y: Nat, e: {None{} == Some{y} : Maybe<&2, Nat>}) -> Empty:
  %Equal.sym(Maybe<&2, Nat>, None{}, Some{y}, e) : L.truth(is_some(_))
  Unit{}

def some_inj(+x: Nat, +y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => some_or(m, x), Some{x}, Some{y}, e)

def acc_lt(+h: Nat, +k: Nat, +n: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +ok: Bool, +e: {SR.accept(h, ok) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_lt(k, n) == True{} : Bool}:
  match ok:
    case True{}:
      %some_inj(h, k, e) : {Nat.is_lt(_, n) == True{} : Bool}
      hh
    case False{}:
      Empty.absurd({Nat.is_lt(k, n) == True{} : Bool}, none_some(k, e))

def draw_pos_lt(+x: Nat, +m: Nat, +k: Nat, +hx: {C.fits(64n, x) == True{} : Bool}, +c: Bool, +e: {SR.draw_pos(64n, x, 1n+m, m, c) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_lt(k, 1n+m) == True{} : Bool}:
  match c:
    case True{}:
      %some_inj(SR.and_bits(64n, x, m), k, e) : {Nat.is_lt(_, 1n+m) == True{} : Bool}
      N.le_lt_succ(SR.and_bits(64n, x, m), m, and_le(64n, x, m))
    case False{}:
      acc_lt(C.high(64n, Nat.mul(x, 1n+m)), k, 1n+m, high_lt(x, 1n+m, hx, {==}), Bool.not(Bool.and(Nat.is_lt(C.low(64n, Nat.mul(x, 1n+m)), 1n+m), Nat.is_lt(C.low(64n, Nat.mul(x, 1n+m)), SR.pow2mod(64n, 1n+m)))), e)

# THEOREM: an accepted draw is below n
def draw_lt(+x: Nat, +n: Nat, +k: Nat, +hx: {C.fits(64n, x) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +e: {SR.draw(64n, x, n) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_lt(k, n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(k, 0n) == True{} : Bool}, L.false_true(hn))
    case 1n+m:
      draw_pos_lt(x, m, k, hx, Nat.is_eq(SR.and_bits(64n, 1n+m, m), 0n), e)

# the bounded draw after a draw of x is below n > 0
def go_lt(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: Nat, m: Maybe<&2, Nat>, +x: Nat, +s1: S, +hx: {C.fits(64n, x) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hm: {SR.draw(64n, x, n) == m : Maybe<&2, Nat>}) -> {Nat.is_lt(pfst(S, SR.below_go(~S, ~next, f, n, m, x, s1)), n) == True{} : Bool}:
  match f m:
    case 0n Some{k}:
      draw_lt(x, n, k, hx, hn, hm)
    case 0n None{}:
      high_lt(x, n, hx, hn)
    case 1n+g Some{k}:
      draw_lt(x, n, k, hx, hn, hm)
    case 1n+g None{}:
      go_lt(~S, ~next, g, n, SR.draw(64n, SW.value(SRC.fst64(S, next(s1))), n), SW.value(SRC.fst64(S, next(s1))), SRC.snd64(S, next(s1)), M128.fit64(SRC.fst64(S, next(s1))), hn, {==})

# THEOREM: the bounded draw from any source is below n > 0
def below_lt(~S: Data, ~next: S -> WU.U64 & S, +f: Nat, +n: Nat, +s: S, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(pfst(S, SR.below(~S, ~next, f, n, s)), n) == True{} : Bool}:
  go_lt(~S, ~next, f, n, SR.draw(64n, SW.value(SRC.fst64(S, next(s))), n), SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s)), M128.fit64(SRC.fst64(S, next(s))), hn, {==})
