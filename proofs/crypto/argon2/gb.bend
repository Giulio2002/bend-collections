import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../math/typed/w64mul.bend as W64M
import ./words.bend as LW
import ../../math/typed/width.bend as WW
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/blake/blake2b/lane.bend as L
import ../../../src/crypto/argon2/blamka.bend as I
import ../../../spec/crypto/blake/blake2b.bend as B
import ../../../spec/crypto/argon2/blamka.bend as S

# GB of the implementation (src/crypto/argon2/blamka.bend) equals GB of the
# specification (spec/crypto/argon2/blamka.bend) for every four lanes.
#
# The only step that is not a computation on the lanes' bits is the product
# of the multiplication-hardened fBlaMka: the implementation's 64-bit product
# of two U32 (src/math/w64.bend's mul32, by 16-bit halves) is the lane of the
# Nat product (mul32's proved value, proofs/math/typed/w64mul.bend, and the
# two-limb round trip). GB is then rewritten one fBlaMka at a time.

# ---------------------------------------------------------------- the product

# Every U64 is the U64 of its value.
def rt(+x: WU.U64) -> {SW.of_nat(SW.value(x)) == x : WU.U64}:
  match x:
    case WU.U64{+l, +h}:
      +el = WW.low_u(32n, LW.v(l), LW.v(h), LW.vb(l))
      +eh = WW.high_u(32n, LW.v(l), LW.v(h), LW.vb(l))
      +e1 = Equal.trans(U32, U32.from_nat(C.low(32n, SW.value(WU.U64{l, h}))), U32.from_nat(LW.v(l)), l, Equal.cong(Nat, U32, z => U32.from_nat(z), C.low(32n, SW.value(WU.U64{l, h})), LW.v(l), el), LW.rt(l))
      +e2 = Equal.trans(U32, U32.from_nat(C.high(32n, SW.value(WU.U64{l, h}))), U32.from_nat(LW.v(h)), h, Equal.cong(Nat, U32, z => U32.from_nat(z), C.high(32n, SW.value(WU.U64{l, h})), LW.v(h), eh), LW.rt(h))
      Equal.trans(WU.U64, WU.U64{U32.from_nat(C.low(32n, SW.value(WU.U64{l, h}))), U32.from_nat(C.high(32n, SW.value(WU.U64{l, h})))}, WU.U64{l, U32.from_nat(C.high(32n, SW.value(WU.U64{l, h})))}, WU.U64{l, h}, Equal.cong(U32, WU.U64, z => WU.U64{z, U32.from_nat(C.high(32n, SW.value(WU.U64{l, h})))}, U32.from_nat(C.low(32n, SW.value(WU.U64{l, h}))), l, e1), Equal.cong(U32, WU.U64, z => WU.U64{l, z}, U32.from_nat(C.high(32n, SW.value(WU.U64{l, h}))), h, e2))

# mul32(a, b) is the U64 of a * b.
def mul32_of(+a: U32, +b: U32) -> {X.mul32(a, b) == SW.of_nat(Nat.mul(U32.to_nat(a), U32.to_nat(b))) : WU.U64}:
  Equal.trans(WU.U64, X.mul32(a, b), SW.of_nat(SW.value(X.mul32(a, b))), SW.of_nat(Nat.mul(U32.to_nat(a), U32.to_nat(b))),
    Equal.sym(WU.U64, SW.of_nat(SW.value(X.mul32(a, b))), X.mul32(a, b), rt(X.mul32(a, b))),
    Equal.cong(Nat, WU.U64, z => SW.of_nat(z), SW.value(X.mul32(a, b)), Nat.mul(U32.to_nat(a), U32.to_nat(b)), W64M.mul32_value(a, b)))

# The implementation's product lane is the specification's.
def prod_correct(+a: U32, +b: U32) -> {I.prod(a, b) == S.lane_of(Nat.mul(U32.to_nat(a), U32.to_nat(b))) : T.Lane}:
  Equal.cong(WU.U64, T.Lane, +z => T.W{X.lo(z), X.hi(z)}, X.mul32(a, b), SW.of_nat(Nat.mul(U32.to_nat(a), U32.to_nat(b))), mul32_of(a, b))

# fBlaMka
def bla_correct(+x: T.Lane, +y: T.Lane) -> {I.bla(x, y) == S.fBlaMka(x, y) : T.Lane}:
  match x y:
    case T.W{+xl, +xh} T.W{+yl, +yh}:
      Equal.cong(T.Lane, T.Lane, +z => L.add(L.add(T.W{xl, xh}, T.W{yl, yh}), L.add(z, z)), I.prod(xl, yl), S.lane_of(Nat.mul(U32.to_nat(xl), U32.to_nat(yl))), prod_correct(xl, yl))

# ---------------------------------------------------------------- GB

# The rotations of XORs, lane by lane.
def rx32(+d: T.Lane, +a: T.Lane) -> {L.rot32(L.xor(d, a)) == B.rotr(B.xor(d, a), 32n) : T.Lane}:
  match d a:
    case T.W{dl, dh} T.W{al, ah}:
      {==}

def rx24(+d: T.Lane, +a: T.Lane) -> {L.rot24(L.xor(d, a)) == B.rotr(B.xor(d, a), 24n) : T.Lane}:
  match d a:
    case T.W{dl, dh} T.W{al, ah}:
      {==}

def rx16(+d: T.Lane, +a: T.Lane) -> {L.rot16(L.xor(d, a)) == B.rotr(B.xor(d, a), 16n) : T.Lane}:
  match d a:
    case T.W{dl, dh} T.W{al, ah}:
      {==}

def rx63(+d: T.Lane, +a: T.Lane) -> {L.rot63(L.xor(d, a)) == B.rotr(B.xor(d, a), 63n) : T.Lane}:
  match d a:
    case T.W{dl, dh} T.W{al, ah}:
      {==}

# The specification's GB after its first k assignment pairs.
def m4(+a2: T.Lane, +b1: T.Lane, +c2: T.Lane, +d2: T.Lane) -> T.Quad:
  T.Q{a2, B.rotr(B.xor(b1, c2), 63n), c2, d2}

def m3(+a2: T.Lane, +b1: T.Lane, +c1: T.Lane, +d1: T.Lane) -> T.Quad:
  +d2 = B.rotr(B.xor(d1, a2), 16n)
  m4(a2, b1, S.fBlaMka(c1, d2), d2)

def m2(+a1: T.Lane, +b: T.Lane, +c1: T.Lane, +d1: T.Lane) -> T.Quad:
  +b1 = B.rotr(B.xor(b, c1), 24n)
  m3(S.fBlaMka(a1, b1), b1, c1, d1)

def m1(+a1: T.Lane, +b: T.Lane, +c: T.Lane, +d: T.Lane) -> T.Quad:
  +d1 = B.rotr(B.xor(d, a1), 32n)
  m2(a1, b, S.fBlaMka(c, d1), d1)

def gb4_correct(+a2: T.Lane, +b1: T.Lane, +c2: T.Lane, +d2: T.Lane) -> {I.gb4(a2, b1, c2, d2) == m4(a2, b1, c2, d2) : T.Quad}:
  Equal.cong(T.Lane, T.Quad, z => T.Q{a2, z, c2, d2}, L.rot63(L.xor(b1, c2)), B.rotr(B.xor(b1, c2), 63n), rx63(b1, c2))

def gb3_correct(+a2: T.Lane, +b1: T.Lane, +c1: T.Lane, +d1: T.Lane) -> {I.gb3(a2, b1, c1, d1) == m3(a2, b1, c1, d1) : T.Quad}:
  +di = L.rot16(L.xor(d1, a2))
  +ds = B.rotr(B.xor(d1, a2), 16n)
  Equal.trans(T.Quad, I.gb4(a2, b1, I.bla(c1, di), di), I.gb4(a2, b1, I.bla(c1, ds), ds), m4(a2, b1, S.fBlaMka(c1, ds), ds),
    Equal.cong(T.Lane, T.Quad, +z => I.gb4(a2, b1, I.bla(c1, z), z), di, ds, rx16(d1, a2)),
    Equal.trans(T.Quad, I.gb4(a2, b1, I.bla(c1, ds), ds), I.gb4(a2, b1, S.fBlaMka(c1, ds), ds), m4(a2, b1, S.fBlaMka(c1, ds), ds),
      Equal.cong(T.Lane, T.Quad, z => I.gb4(a2, b1, z, ds), I.bla(c1, ds), S.fBlaMka(c1, ds), bla_correct(c1, ds)),
      gb4_correct(a2, b1, S.fBlaMka(c1, ds), ds)))

def gb2_correct(+a1: T.Lane, +b: T.Lane, +c1: T.Lane, +d1: T.Lane) -> {I.gb2(a1, b, c1, d1) == m2(a1, b, c1, d1) : T.Quad}:
  +bi = L.rot24(L.xor(b, c1))
  +bs = B.rotr(B.xor(b, c1), 24n)
  Equal.trans(T.Quad, I.gb3(I.bla(a1, bi), bi, c1, d1), I.gb3(I.bla(a1, bs), bs, c1, d1), m3(S.fBlaMka(a1, bs), bs, c1, d1),
    Equal.cong(T.Lane, T.Quad, +z => I.gb3(I.bla(a1, z), z, c1, d1), bi, bs, rx24(b, c1)),
    Equal.trans(T.Quad, I.gb3(I.bla(a1, bs), bs, c1, d1), I.gb3(S.fBlaMka(a1, bs), bs, c1, d1), m3(S.fBlaMka(a1, bs), bs, c1, d1),
      Equal.cong(T.Lane, T.Quad, z => I.gb3(z, bs, c1, d1), I.bla(a1, bs), S.fBlaMka(a1, bs), bla_correct(a1, bs)),
      gb3_correct(S.fBlaMka(a1, bs), bs, c1, d1)))

def gb1_correct(+a1: T.Lane, +b: T.Lane, +c: T.Lane, +d: T.Lane) -> {I.gb1(a1, b, c, d) == m1(a1, b, c, d) : T.Quad}:
  +di = L.rot32(L.xor(d, a1))
  +ds = B.rotr(B.xor(d, a1), 32n)
  Equal.trans(T.Quad, I.gb2(a1, b, I.bla(c, di), di), I.gb2(a1, b, I.bla(c, ds), ds), m2(a1, b, S.fBlaMka(c, ds), ds),
    Equal.cong(T.Lane, T.Quad, +z => I.gb2(a1, b, I.bla(c, z), z), di, ds, rx32(d, a1)),
    Equal.trans(T.Quad, I.gb2(a1, b, I.bla(c, ds), ds), I.gb2(a1, b, S.fBlaMka(c, ds), ds), m2(a1, b, S.fBlaMka(c, ds), ds),
      Equal.cong(T.Lane, T.Quad, z => I.gb2(a1, b, z, ds), I.bla(c, ds), S.fBlaMka(c, ds), bla_correct(c, ds)),
      gb2_correct(a1, b, S.fBlaMka(c, ds), ds)))

# GB: the implementation's equals the specification's.
def gb_correct(+a: T.Lane, +b: T.Lane, +c: T.Lane, +d: T.Lane) -> {I.gb(a, b, c, d) == S.GB(a, b, c, d) : T.Quad}:
  Equal.trans(T.Quad, I.gb1(I.bla(a, b), b, c, d), I.gb1(S.fBlaMka(a, b), b, c, d), m1(S.fBlaMka(a, b), b, c, d),
    Equal.cong(T.Lane, T.Quad, z => I.gb1(z, b, c, d), I.bla(a, b), S.fBlaMka(a, b), bla_correct(a, b)),
    gb1_correct(S.fBlaMka(a, b), b, c, d))
