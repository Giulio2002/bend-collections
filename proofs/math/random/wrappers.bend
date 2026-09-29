import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/source.bend as SRC
import ../../../spec/math/random.bend as SRM
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../lib/lemmas/spec/numeric.bend as S
import ../typed/width.bend as WW
import ../typed/u32laws.bend as LW
import ../typed/w64add.bend as WA
import ../typed/f64bits.bend as FB
import ../typed/w64clz.bend as WC
import ../typed/w64sh.bend as SH
import ../typed/w64div.bend as W64D
import ../u64/u64div.bend as PD
import ../typed/w64mul.bend as W64M
import ../../lib/word.bend as WD
import ../../lib/arith.bend as LA
import ../natural/arith.bend as AR
import ./bounded.bend as MR
import ./lemire.bend as LE

# The word slices (Go's Uint32, Int64, Int32) and the bounded wrappers
# (Uint32N, IntN, lo + IntN(hi - lo)) of src/math/random/rand.bend, for every
# source: the slices are the stated bits of the output, and the bounded ones
# inherit Uint64n.lt.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def val(+l: U32, +h: U32) -> Nat:
  Nat.add(v(l), C.shift(32n, v(h)))

# ---- Uint32: the top 32 bits ----

def u32_p(-S: Data, p: W.U64 & S) -> {U32.to_nat(R.fst(U32, S, R.top32(S, p))) == C.high(32n, SW.value(SRC.fst64(S, p))) : Nat}:
  match p:
    case Tuple{x, s}:
      match x:
        case W.U64{+l, +h}:
          Equal.sym(Nat, C.high(32n, val(l, h)), v(h), WW.high_u(32n, v(l), v(h), LW.vb(l)))

def uint32_value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Uint32.value(~S, ~next, s):
  u32_p(S, next(s))

# ---- Int64: the low 63 bits ----

def low63_v(+l: U32, +h: U32) -> {SW.value(W.U64{l, U32.and(h, 2147483647)}) == C.low(63n, val(l, h)) : Nat}:
  +n = val(l, h)
  Equal.trans(Nat, Nat.add(v(l), C.shift(32n, v(U32.and(h, 2147483647)))), Nat.add(v(l), C.shift(32n, C.low(31n, v(h)))), C.low(63n, n),
    Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), v(U32.and(h, 2147483647)), C.low(31n, v(h)), FB.andm(h, 31n, 2147483647, {==})),
    Equal.sym(Nat, C.low(63n, n), Nat.add(v(l), C.shift(32n, C.low(31n, v(h)))),
      Equal.trans(Nat, C.low(63n, n), Nat.add(C.low(32n, n), C.shift(32n, C.low(31n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(31n, v(h)))),
        FB.low_split(32n, 31n, n),
        Equal.trans(Nat, Nat.add(C.low(32n, n), C.shift(32n, C.low(31n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(31n, C.high(32n, n)))), Nat.add(v(l), C.shift(32n, C.low(31n, v(h)))),
          Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.low(31n, C.high(32n, n)))), C.low(32n, n), v(l), WW.low_u(32n, v(l), v(h), LW.vb(l))),
          Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, C.low(31n, z))), C.high(32n, n), v(h), WW.high_u(32n, v(l), v(h), LW.vb(l)))))))

def i64_p(-S: Data, p: W.U64 & S) -> {SW.value(R.fst(W.U64, S, R.low63(S, p))) == C.low(63n, SW.value(SRC.fst64(S, p))) : Nat}:
  match p:
    case Tuple{x, s}:
      match x:
        case W.U64{+l, +h}:
          low63_v(l, h)

def int64_value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Int64.value(~S, ~next, s):
  i64_p(S, next(s))

# ---- Int32: the top 31 bits ----

def half_bv(+b: Bool) -> {C.half(S.bit_value(b)) == 0n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# x >> 1 is half of x
def shr_half(+x: U32) -> {v(U32.shr(x)) == C.half(v(x)) : Nat}:
  +b = S.bit_value(U.low_bit(x))
  +y = v(U32.shr(x))
  Equal.sym(Nat, C.half(v(x)), y,
    Equal.trans(Nat, C.half(v(x)), C.half(Nat.add(b, Nat.double(y))), y,
      Equal.cong(Nat, Nat, z => C.half(z), v(x), Nat.add(b, Nat.double(y)), U.shr_split(x)),
      Equal.trans(Nat, C.half(Nat.add(b, Nat.double(y))), Nat.add(C.half(b), y), y, WW.half_dbl(b, y),
        Equal.cong(Nat, Nat, z => Nat.add(z, y), C.half(b), 0n, half_bv(U.low_bit(x))))))

def i32_p(-S: Data, p: W.U64 & S) -> {U32.to_nat(R.fst(U32, S, R.top31(S, p))) == C.high(33n, SW.value(SRC.fst64(S, p))) : Nat}:
  match p:
    case Tuple{x, s}:
      match x:
        case W.U64{+l, +h}:
          Equal.trans(Nat, v(U32.shr(h)), C.half(v(h)), C.high(33n, val(l, h)),
            shr_half(h),
            Equal.sym(Nat, C.high(33n, val(l, h)), C.half(v(h)),
              Equal.trans(Nat, C.high(Nat.add(32n, 1n), val(l, h)), C.high(1n, C.high(32n, val(l, h))), C.half(v(h)),
                WW.high_comp(1n, 32n, val(l, h)),
                Equal.cong(Nat, Nat, z => C.high(1n, z), C.high(32n, val(l, h)), v(h), WW.high_u(32n, v(l), v(h), LW.vb(l))))))

def int32_value(~S: Data, ~next: S -> W.U64 & S, +s: S) -> SRM.Int32.value(~S, ~next, s):
  i32_p(S, next(s))

# ---- Uint32N ----

def lo_le(-S: Data, r: W.U64 & S) -> {Nat.is_le(U32.to_nat(R.fst(U32, S, R.lo32(S, r))), SW.value(R.fst(W.U64, S, r))) == True{} : Bool}:
  match r:
    case Tuple{x, s}:
      match x:
        case W.U64{+l, +h}:
          N.le_add_right(v(l), C.shift(32n, v(h)))

def nz_word(+n: U32, +hn: {U32.is_zero(n) == False{} : Bool}) -> {X.is_zero(W.U64{n, 0}) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_zero(n), False{}, hn) : {Bool.and(_, U32.is_zero(0)) == False{} : Bool}
  {==}

def uint32n_lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: U32, +hn: {U32.is_zero(n) == False{} : Bool}) -> SRM.Uint32n.lt(~S, ~next, s, n, hn):
  h1 = MR.uint64n_lt(~S, ~next, s, W.U64{n, 0}, nz_word(n, hn))
  +h2 = Equal.trans(Bool, Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, W.U64{n, 0}))), v(n)), Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, W.U64{n, 0}))), Nat.add(v(n), C.shift(32n, 0n))), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, W.U64{n, 0}))), z), v(n), Nat.add(v(n), C.shift(32n, 0n)), Equal.sym(Nat, Nat.add(v(n), 0n), v(n), N.add_zero(v(n)))),
    h1)
  N.le_lt_trans(U32.to_nat(R.fst(U32, S, R.lo32(S, R.uint64n(~S, ~next, s, W.U64{n, 0})))), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, W.U64{n, 0}))), v(n), lo_le(S, R.uint64n(~S, ~next, s, W.U64{n, 0})), h2)

# ---- Nat <-> U64 below 2^64: n48 (from proofs/math/typed/u64bgcd.bend)
# and rand.bend's nat64, a byte at a time ----

def vv(+x: W.U64) -> Nat:
  SW.value(x)

def s32(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(Nat.mul(x, 65536n), 65536n) == C.shift(32n, x) : Nat}:
  +k = W64D.k65536(one, h1)
  +e1 = PD.mul_pow(one, h1, 16n, x, 65536n, k)
  +e2 = Equal.trans(Nat, Nat.mul(Nat.mul(x, 65536n), 65536n), Nat.mul(WD.sc(16n, x), 65536n), WD.sc(16n, WD.sc(16n, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, 65536n), Nat.mul(x, 65536n), WD.sc(16n, x), e1), PD.mul_pow(one, h1, 16n, WD.sc(16n, x), 65536n, k))
  Equal.trans(Nat, Nat.mul(Nat.mul(x, 65536n), 65536n), WD.sc(16n, WD.sc(16n, x)), C.shift(32n, x), e2, Equal.trans(Nat, WD.sc(16n, WD.sc(16n, x)), WD.sc(32n, x), C.shift(32n, x), W64M.sc_sc(16n, 16n, x), Equal.sym(Nat, C.shift(32n, x), WD.sc(32n, x), W64M.shift_sc(32n, x))))

def n48v(+one: Nat, +h1: {one == 1n : Nat}, +a: W.U64) -> {X.n48(a) == vv(a) : Nat}:
  match a:
    case W.U64{+l, +h}:
      Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(l), z), Nat.mul(Nat.mul(U32.to_nat(h), 65536n), 65536n), C.shift(32n, U32.to_nat(h)), s32(one, h1, U32.to_nat(h)))


def fits0(+a: Nat) -> {C.fits(a, 0n) == True{} : Bool}:
  %Equal.sym(Nat, C.high(a, 0n), 0n, WC.high0(a)) : {Nat.is_eq(_, 0n) == True{} : Bool}
  {==}

# x < 2^k gives x 2^a < 2^(a + k)
def fits_shift(+a: Nat, +k: Nat, +x: Nat, +h: {C.fits(k, x) == True{} : Bool}) -> {C.fits(Nat.add(a, k), C.shift(a, x)) == True{} : Bool}:
  WW.limbs_fit(a, k, 0n, x, fits0(a), h)

def sh8(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      Nat.add(8n, sh8(j))

def div256(+n: Nat) -> {Nat.div(n, 256n) == C.high(8n, n) : Nat}:
  Equal.sym(Nat, C.high(8n, n), Nat.div(n, 256n), WW.high_div(8n, n, 255n, {==}))

def mod256(+n: Nat) -> {Nat.mod(n, 256n) == C.low(8n, n) : Nat}:
  +q = C.high(8n, n)
  +r = C.low(8n, n)
  +e = Equal.trans(Nat, n, Nat.add(r, C.shift(8n, q)), Nat.add(Nat.mul(q, 256n), r), WW.low_high(8n, n),
    Equal.trans(Nat, Nat.add(r, C.shift(8n, q)), Nat.add(C.shift(8n, q), r), Nat.add(Nat.mul(q, 256n), r), N.add_comm(r, C.shift(8n, q)),
      Equal.cong(Nat, Nat, z => Nat.add(z, r), C.shift(8n, q), Nat.mul(q, 256n), WW.shift_mul(8n, q))))
  Equal.trans(Nat, Nat.mod(n, 256n), Nat.mod(Nat.add(Nat.mul(q, 256n), r), 256n), r,
    Equal.cong(Nat, Nat, z => Nat.mod(z, 256n), n, Nat.add(Nat.mul(q, 256n), r), e),
    AR.mod_of(q, 255n, r, WW.lt_of_fits(8n, r, WW.low_fits(8n, n))))

def byte_v(+n: Nat) -> {v(U32.from_nat(Nat.mod(n, 256n))) == C.low(8n, n) : Nat}:
  %Equal.sym(Nat, Nat.mod(n, 256n), C.low(8n, n), mod256(n)) : {v(U32.from_nat(_)) == C.low(8n, n) : Nat}
  U.to_nat_from_nat(C.low(8n, n), 8n, {==}, WW.lt_of_fits(8n, C.low(8n, n), WW.low_fits(8n, n)))

# the words of w_go are the low 8k bits, for 8k <= 32
def wgo(+k: Nat, +n: Nat, +hk: {Nat.is_le(sh8(k), 32n) == True{} : Bool}) -> {v(R.w_go(k, n)) == C.low(sh8(k), n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +d = C.high(8n, n)
      +hj = N.le_trans(sh8(j), Nat.add(8n, sh8(j)), 32n, LE.le_plus(8n, sh8(j)), hk)
      +hj24 = Equal.trans(Bool, Nat.is_le(sh8(j), 24n), Nat.is_le(Nat.add(8n, sh8(j)), 32n), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(8n, sh8(j)), 32n), Nat.is_le(sh8(j), 24n), AR.le_add_cancel(8n, sh8(j), 24n)), hk)
      +ih = Equal.trans(Nat, v(R.w_go(j, Nat.div(n, 256n))), C.low(sh8(j), Nat.div(n, 256n)), C.low(sh8(j), d), wgo(j, Nat.div(n, 256n), hj), Equal.cong(Nat, Nat, z => C.low(sh8(j), z), Nat.div(n, 256n), d, div256(n)))
      +lw = C.low(sh8(j), d)
      +f24 = SH.fits_mono(sh8(j), 24n, lw, hj24, WW.low_fits(sh8(j), d))
      +f32s = fits_shift(8n, 24n, lw, f24)
      +em = Equal.trans(Nat, v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n))), C.low(32n, C.shift(8n, v(R.w_go(j, Nat.div(n, 256n))))), C.shift(8n, lw),
        SH.mul_p2(R.w_go(j, Nat.div(n, 256n)), 8n, {==}),
        Equal.trans(Nat, C.low(32n, C.shift(8n, v(R.w_go(j, Nat.div(n, 256n))))), C.low(32n, C.shift(8n, lw)), C.shift(8n, lw), Equal.cong(Nat, Nat, z => C.low(32n, C.shift(8n, z)), v(R.w_go(j, Nat.div(n, 256n))), lw, ih), WW.low_fit(32n, C.shift(8n, lw), f32s)))
      +sum = Nat.add(C.low(8n, n), C.shift(8n, lw))
      +es = Equal.sym(Nat, C.low(Nat.add(8n, sh8(j)), n), sum, FB.low_split(8n, sh8(j), n))
      +fsum = SH.fits_mono(Nat.add(8n, sh8(j)), 32n, sum, hk, Equal.trans(Bool, C.fits(Nat.add(8n, sh8(j)), sum), C.fits(Nat.add(8n, sh8(j)), C.low(Nat.add(8n, sh8(j)), n)), True{}, Equal.cong(Nat, Bool, z => C.fits(Nat.add(8n, sh8(j)), z), sum, C.low(Nat.add(8n, sh8(j)), n), es), WW.low_fits(Nat.add(8n, sh8(j)), n)))
      +bv = byte_v(n)
      +vsum = Equal.trans(Nat, Nat.add(v(U32.from_nat(Nat.mod(n, 256n))), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), Nat.add(C.low(8n, n), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), sum,
        Equal.cong(Nat, Nat, z => Nat.add(z, v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), v(U32.from_nat(Nat.mod(n, 256n))), C.low(8n, n), bv),
        Equal.cong(Nat, Nat, z => Nat.add(C.low(8n, n), z), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n))), C.shift(8n, lw), em))
      +hf = Equal.trans(Bool, C.fits(32n, Nat.add(v(U32.from_nat(Nat.mod(n, 256n))), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n))))), C.fits(32n, sum), True{}, Equal.cong(Nat, Bool, z => C.fits(32n, z), Nat.add(v(U32.from_nat(Nat.mod(n, 256n))), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), sum, vsum), fsum)
      Equal.trans(Nat, v(U32.add(U32.from_nat(Nat.mod(n, 256n)), U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), Nat.add(v(U32.from_nat(Nat.mod(n, 256n))), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), C.low(Nat.add(8n, sh8(j)), n),
        WA.add_exact(1n, {==}, U32.from_nat(Nat.mod(n, 256n)), U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)), hf),
        Equal.trans(Nat, Nat.add(v(U32.from_nat(Nat.mod(n, 256n))), v(U32.mul(R.w_go(j, Nat.div(n, 256n)), X.pow2(8n)))), sum, C.low(Nat.add(8n, sh8(j)), n), vsum, es))

# skip(k, n) = n div 2^(8k)
def skip_v(+k: Nat, +n: Nat) -> {R.skip(k, n) == C.high(sh8(k), n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, R.skip(j, Nat.div(n, 256n)), C.high(sh8(j), Nat.div(n, 256n)), C.high(Nat.add(8n, sh8(j)), n),
        skip_v(j, Nat.div(n, 256n)),
        Equal.trans(Nat, C.high(sh8(j), Nat.div(n, 256n)), C.high(sh8(j), C.high(8n, n)), C.high(Nat.add(8n, sh8(j)), n),
          Equal.cong(Nat, Nat, z => C.high(sh8(j), z), Nat.div(n, 256n), C.high(8n, n), div256(n)),
          Equal.sym(Nat, C.high(Nat.add(8n, sh8(j)), n), C.high(sh8(j), C.high(8n, n)), WW.high_comp(sh8(j), 8n, n))))

# THEOREM: nat64(n) denotes n, for n < 2^64
def nat64_v(+n: Nat, +hn: {C.fits(64n, n) == True{} : Bool}) -> {vv(R.nat64(n)) == n : Nat}:
  +l = C.low(32n, n)
  +h = C.low(32n, C.high(32n, n))
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, v(R.w_go(4n, R.skip(4n, n))))), v(R.w_go(4n, n)), l, wgo(4n, n, {==}))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(l, C.shift(32n, z)), v(R.w_go(4n, R.skip(4n, n))), h, Equal.trans(Nat, v(R.w_go(4n, R.skip(4n, n))), C.low(32n, R.skip(4n, n)), h, wgo(4n, R.skip(4n, n), {==}), Equal.cong(Nat, Nat, z => C.low(32n, z), R.skip(4n, n), C.high(32n, n), skip_v(4n, n))))
  +e3 = Equal.sym(Nat, C.low(64n, n), Nat.add(l, C.shift(32n, h)), FB.low_split(32n, 32n, n))
  Equal.trans(Nat, Nat.add(v(R.w_go(4n, n)), C.shift(32n, v(R.w_go(4n, R.skip(4n, n))))), Nat.add(l, C.shift(32n, v(R.w_go(4n, R.skip(4n, n))))), n, e1,
    Equal.trans(Nat, Nat.add(l, C.shift(32n, v(R.w_go(4n, R.skip(4n, n))))), Nat.add(l, C.shift(32n, h)), n, e2,
      Equal.trans(Nat, Nat.add(l, C.shift(32n, h)), C.low(64n, n), n, e3, WW.low_fit(64n, n, hn))))

# ---- IntN ----

def n48_p(-S: Data, r: W.U64 & S) -> {R.fst(Nat, S, R.to_nat(S, r)) == SW.value(R.fst(W.U64, S, r)) : Nat}:
  match r:
    case Tuple{x, s}:
      n48v(1n, {==}, x)

def intn_pos(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(64n, n) == True{} : Bool}) -> {Nat.is_lt(R.fst(Nat, S, R.intn_z(~S, ~next, s, n, False{})), n) == True{} : Bool}:
  +w = {R.nat64(n) : W.U64}
  +ev = nat64_v(n, hw)
  +hz = Equal.trans(Bool, X.is_zero(w), Nat.is_eq(SW.value(w), 0n), False{}, WA.is_zero_value(w),
    Equal.trans(Bool, Nat.is_eq(SW.value(w), 0n), Nat.is_eq(n, 0n), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), SW.value(w), n, ev), N.is_eq_sym_false(0n, n, N.is_eq_lt(0n, n, hn))))
  %Equal.sym(Nat, R.fst(Nat, S, R.to_nat(S, R.uint64n(~S, ~next, s, w))), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, w))), n48_p(S, R.uint64n(~S, ~next, s, w))) : {Nat.is_lt(_, n) == True{} : Bool}
  %ev : {Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, w))), _) == True{} : Bool}
  MR.uint64n_lt(~S, ~next, s, w, hz)

def intn_lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(64n, n) == True{} : Bool}) -> SRM.Intn.lt(~S, ~next, s, n, hn, hw):
  %Equal.sym(Bool, Nat.is_eq(n, 0n), False{}, N.is_eq_sym_false(0n, n, N.is_eq_lt(0n, n, hn))) : {Nat.is_lt(R.fst(Nat, S, R.intn_z(~S, ~next, s, n, _)), n) == True{} : Bool}
  intn_pos(~S, ~next, s, n, hn, hw)

# ---- int_range ----

def plus_fst(-S: Data, +lo: Nat, r: Nat & S) -> {R.fst(Nat, S, R.plus(S, lo, r)) == Nat.add(lo, R.fst(Nat, S, r)) : Nat}:
  match r:
    case Tuple{k, s}:
      {==}

def lt_pos(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(b, a)) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(0n, a)) == True{} : Bool}, N.lt_zero_absurd(a, h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_pos(p, q, h)

def int_range_bounds(~S: Data, ~next: S -> W.U64 & S, +s: S, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool}, +hw: {C.fits(64n, Nat.sub(hi, lo)) == True{} : Bool}) -> SRM.IntRange.bounds(~S, ~next, s, lo, hi, h, hw):
  +d = Nat.sub(hi, lo)
  +k = R.fst(Nat, S, R.intn(~S, ~next, s, d))
  hk = intn_lt(~S, ~next, s, d, lt_pos(lo, hi, h), hw)
  +up = Equal.trans(Bool, Nat.is_lt(Nat.add(lo, k), hi), Nat.is_lt(Nat.add(lo, k), Nat.add(lo, d)), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.add(lo, k), z), hi, Nat.add(lo, d), Equal.sym(Nat, Nat.add(lo, d), hi, N.sub_add(hi, lo, N.lt_le(lo, hi, h)))),
    N.lt_add_left(k, d, lo, hk))
  %Equal.sym(Nat, R.fst(Nat, S, R.plus(S, lo, R.intn(~S, ~next, s, d))), Nat.add(lo, k), plus_fst(S, lo, R.intn(~S, ~next, s, d))) : {Bool.and(Nat.is_le(lo, _), Nat.is_lt(_, hi)) == True{} : Bool}
  L.and_intro(Nat.is_le(lo, Nat.add(lo, k)), Nat.is_lt(Nat.add(lo, k), hi), N.le_add_right(lo, k), up)
