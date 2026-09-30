import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/u32.bend as U
import ../../lib/logic.bend as L
import ../../math/typed/w64mul.bend as W64M
import ./words.bend as LW
import ../../math/typed/width.bend as WW
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/argon2.bend as I
import ../../../spec/crypto/blake/blake2b.bend as B
import ../../../spec/crypto/argon2/blamka.bend as SG
import ../../../spec/crypto/argon2/argon2.bend as SA
import ./gb.bend as GB
import ./blamka.bend as BL

# The reference-index computation of the implementation (U32 products,
# src/math/w64.bend's mul32) equals the specification's (Nat arithmetic,
# RFC 9106 section 3.4.1.2), and so do the address blocks of the
# data-independent segments.

# ---------------------------------------------------------------- lanes of a block

def row_at_eq(+b: A.Block, +i: Nat) -> {I.row_at(b, i) == SG.row(b, i) : T.State}:
  match b i:
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 0n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 1n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 2n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 3n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 4n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 5n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 6n:
      {==}
    case A.B{r0, r1, r2, r3, r4, r5, r6, r7} 7n+z:
      {==}

def at_eq(+v: T.State, +j: Nat) -> {I.at(v, j) == B.at(v, j) : T.Lane}:
  match v j:
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 0n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 1n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 2n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 3n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 4n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 5n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 6n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 7n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 8n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 9n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 10n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 11n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 12n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 13n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 14n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 15n:
      {==}
    case T.V{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} 16n+z:
      {==}

def lane_eq(+b: A.Block, +n: Nat) -> {I.lane(b, n) == SG.lane(b, n) : T.Lane}:
  Equal.trans(T.Lane, I.at(I.row_at(b, Nat.div(n, 16n)), Nat.mod(n, 16n)), I.at(SG.row(b, Nat.div(n, 16n)), Nat.mod(n, 16n)), SG.lane(b, n),
    Equal.cong(T.State, T.Lane, z => I.at(z, Nat.mod(n, 16n)), I.row_at(b, Nat.div(n, 16n)), SG.row(b, Nat.div(n, 16n)), row_at_eq(b, Nat.div(n, 16n))),
    at_eq(SG.row(b, Nat.div(n, 16n)), Nat.mod(n, 16n)))

def pick_eq(+indep: Bool, +addr: A.Block, +idx: Nat, +prev: A.Block) -> {I.pick(indep, addr, idx, prev) == SA.pick(indep, addr, idx, prev) : T.Lane}:
  match indep:
    case True{}:
      lane_eq(addr, Nat.mod(idx, 128n))
    case False{}:
      lane_eq(prev, 0n)

def hi_eq(+x: T.Lane) -> {I.hi(x) == SA.hi(x) : U32}:
  match x:
    case T.W{l, h}:
      {==}

def lo_eq(+x: T.Lane) -> {G.lo(x) == SA.lo(x) : U32}:
  match x:
    case T.W{l, h}:
      {==}

# ---------------------------------------------------------------- the reference area

def ref_lane_eq(+forced: Bool, +l: Nat, +j2: U32, +p: Nat) -> {I.ref_lane(forced, l, j2, p) == SA.ref_lane(forced, l, j2, p) : Nat}:
  match forced:
    case True{}:
      {==}
    case False{}:
      {==}

def area_base_eq(+r0: Bool, +s: Nat, +sl: Nat, +q: Nat) -> {I.area_base(r0, s, sl, q) == SA.area_base(r0, s, sl, q) : Nat}:
  match r0:
    case True{}:
      {==}
    case False{}:
      {==}

def area_other_eq(+base: Nat, +zero: Bool) -> {I.area_other(base, zero) == SA.area_other(base, zero) : Nat}:
  match zero:
    case True{}:
      {==}
    case False{}:
      {==}

def area_eq(+base: Nat, +idx: Nat, +same: Bool) -> {I.area(base, idx, same) == SA.area(base, idx, same) : Nat}:
  match same:
    case True{}:
      {==}
    case False{}:
      area_other_eq(base, Nat.is_eq(idx, 0n))

def start_last_eq(+s: Nat, +sl: Nat, +last: Bool) -> {I.start_last(s, sl, last) == SA.start_last(s, sl, last) : Nat}:
  match last:
    case True{}:
      {==}
    case False{}:
      {==}

def start_eq(+r0: Bool, +s: Nat, +sl: Nat) -> {I.start(r0, s, sl) == SA.start(r0, s, sl) : Nat}:
  match r0:
    case True{}:
      {==}
    case False{}:
      start_last_eq(s, sl, Nat.is_eq(s, 3n))

def prev_index_eq(+l: Nat, +q: Nat, +j: Nat, +first: Bool) -> {I.prev_index(l, q, j, first) == SA.prev_index(l, q, j, first) : Nat}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

def start_index_eq(+first: Bool) -> {I.start_index(first) == SA.start_index(first) : Nat}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

def fits_value(+x: WU.U64) -> {C.fits(64n, SW.value(x)) == True{} : Bool}:
  match x:
    case WU.U64{+l, +h}:
      WW.limbs_fit(32n, 32n, LW.v(l), LW.v(h), LW.vb(l), LW.vb(h))

# ---------------------------------------------------------------- x = J1^2 / 2^32, y = |W| x / 2^32

# The high word of mul32(a, b) is a * b div 2^32.
def hi_mul(+a: U32, +b: U32) -> {U32.to_nat(X.hi(X.mul32(a, b))) == C.high(32n, Nat.mul(U32.to_nat(a), U32.to_nat(b))) : Nat}:
  +n = Nat.mul(U32.to_nat(a), U32.to_nat(b))
  +f64 = L.subst(Nat, z => {C.fits(64n, z) == True{} : Bool}, SW.value(X.mul32(a, b)), n, W64M.mul32_value(a, b), fits_value(X.mul32(a, b)))
  +f32 = LW.fits_high(32n, 32n, n, f64)
  %Equal.sym(WU.U64, X.mul32(a, b), SW.of_nat(n), GB.mul32_of(a, b)) : {U32.to_nat(X.hi(_)) == C.high(32n, n) : Nat}
  LW.vo(C.high(32n, n), f32)

# rel: |W| - 1 - (|W| * (J1^2 / 2^32)) / 2^32, for |W| < 2^k with k <= 32.
def rel_eq(+w: Nat, +j1: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hw: {Nat.is_lt(w, C.pow2(k)) == True{} : Bool}) -> {I.rel(w, j1) == SA.rel(w, j1) : Nat}:
  +xi = X.hi(X.mul32(j1, j1))
  +xs = C.high(32n, Nat.mul(U32.to_nat(j1), U32.to_nat(j1)))
  +ew = U.to_nat_from_nat(w, k, hk, hw)
  +e1 = hi_mul(U32.from_nat(w), xi)
  +e2 = Equal.trans(Nat, C.high(32n, Nat.mul(U32.to_nat(U32.from_nat(w)), U32.to_nat(xi))), C.high(32n, Nat.mul(w, U32.to_nat(xi))), C.high(32n, Nat.mul(w, xs)),
    Equal.cong(Nat, Nat, z => C.high(32n, Nat.mul(z, U32.to_nat(xi))), U32.to_nat(U32.from_nat(w)), w, ew),
    Equal.cong(Nat, Nat, z => C.high(32n, Nat.mul(w, z)), U32.to_nat(xi), xs, hi_mul(j1, j1)))
  Equal.cong(Nat, Nat, z => Nat.sub(Nat.sub(w, 1n), z), U32.to_nat(X.hi(X.mul32(U32.from_nat(w), xi))), C.high(32n, Nat.mul(w, xs)), Equal.trans(Nat, U32.to_nat(X.hi(X.mul32(U32.from_nat(w), xi))), C.high(32n, Nat.mul(U32.to_nat(U32.from_nat(w)), U32.to_nat(xi))), C.high(32n, Nat.mul(w, xs)), e1, e2))

# ---------------------------------------------------------------- address blocks

def input_eq(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> {I.input_block(r, l, s, mm, t, ctr) == SA.input_block(r, l, s, mm, t, ctr) : A.Block}:
  match r:
    case 0n:
      {==}
    case 1n+x:
      {==}

def addresses_eq(+r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +ctr: Nat) -> {I.addresses(r, l, s, mm, t, ctr) == SA.addresses(r, l, s, mm, t, ctr) : A.Block}:
  +z = SA.input_block(r, l, s, mm, t, ctr)
  Equal.trans(A.Block, G.compress(G.zero(), G.compress(G.zero(), I.input_block(r, l, s, mm, t, ctr))), G.compress(G.zero(), G.compress(G.zero(), z)), SG.G(SG.zero(), SG.G(SG.zero(), z)),
    Equal.cong(A.Block, A.Block, x => G.compress(G.zero(), G.compress(G.zero(), x)), I.input_block(r, l, s, mm, t, ctr), z, input_eq(r, l, s, mm, t, ctr)),
    Equal.trans(A.Block, G.compress(G.zero(), G.compress(G.zero(), z)), G.compress(G.zero(), SG.G(SG.zero(), z)), SG.G(SG.zero(), SG.G(SG.zero(), z)),
      Equal.cong(A.Block, A.Block, x => G.compress(G.zero(), x), G.compress(G.zero(), z), SG.G(SG.zero(), z), BL.compress_correct(G.zero(), z)),
      BL.compress_correct(G.zero(), SG.G(SG.zero(), z))))

def regen_eq(+need: Bool, +addr: A.Block, +r: Nat, +l: Nat, +s: Nat, +mm: Nat, +t: Nat, +idx: Nat) -> {I.regen(need, addr, r, l, s, mm, t, idx) == SA.regen(need, addr, r, l, s, mm, t, idx) : A.Block}:
  match need:
    case True{}:
      addresses_eq(r, l, s, mm, t, Nat.add(Nat.div(idx, 128n), 1n))
    case False{}:
      {==}
