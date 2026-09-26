import Base
import ../../../spec/math/u64.bend as SU
import ../../../src/math/u64.bend as U
import ../../lib/lemmas/src/wide.bend as W
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U3
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/numeric.bend as NUM
import ../../lib/lemmas/proofs/addition.bend as AD
import ../../lib/lemmas/proofs/modular_addition.bend as MA
import ../../lib/lemmas/proofs/word_addition.bend as WA
import ../../lib/word.bend as WD
import ../../lib/u32div.bend as UD

# src/math/u64.bend against its specification spec/math/u64.bend: a U64
# denotes the 64-bit word bits(a) (low limb first).

def bits(a: U.U64) -> Word(64n):
  SU.bits(a)

# ---- comparison ----

def order_eq(+c: Cmp) -> {U.order(c, EQ{}) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def fin_order(+x: Bool, +y: Bool, +c: Cmp, +d: Cmp) -> {Word.cmp.fin(x, y, U.order(c, d)) == U.order(c, Word.cmp.fin(x, y, d)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Comparing two joined words is comparing the high parts, then the low parts.
def cmp_join(+n: Nat, +m: Nat, +a1: Word(n), +b1: Word(m), +a2: Word(n), +b2: Word(m)) -> {Word.cmp(Nat.add(n, m), W.join(n, m, a1, b1), W.join(n, m, a2, b2)) == U.order(Word.cmp(m, b1, b2), Word.cmp(n, a1, a2)) : Cmp}:
  match n a1 a2:
    case 0n WNil{} WNil{}:
      Equal.sym(Cmp, U.order(Word.cmp(m, b1, b2), EQ{}), Word.cmp(m, b1, b2), order_eq(Word.cmp(m, b1, b2)))
    case 1n+p WCon{x, t1} WCon{y, t2}:
      %Equal.sym(Cmp, Word.cmp(Nat.add(p, m), W.join(p, m, t1, b1), W.join(p, m, t2, b2)), U.order(Word.cmp(m, b1, b2), Word.cmp(p, t1, t2)), cmp_join(p, m, t1, b1, t2, b2)) : {Word.cmp.fin(x, y, _) == U.order(Word.cmp(m, b1, b2), Word.cmp.fin(x, y, Word.cmp(p, t1, t2))) : Cmp}
      fin_order(x, y, Word.cmp(m, b1, b2), Word.cmp(p, t1, t2))

def u32_cmp(+x: Word(32n), +y: Word(32n)) -> {U32.cmp(U32{x}, U32{y}) == Word.cmp(32n, x, y) : Cmp}:
  {==}

def cmp_pack(+alo: U32, +ahi: U32, +blo: U32, +bhi: U32) -> {Word.cmp(64n, W.pack(alo, ahi), W.pack(blo, bhi)) == U.order(U32.cmp(ahi, bhi), U32.cmp(alo, blo)) : Cmp}:
  match alo ahi blo bhi:
    case U32{a} U32{b} U32{c} U32{d}:
      cmp_join(32n, 32n, a, b, c, d)

def ge_fin_zero(+c: Cmp, +x: Bool, +h: {Cmp.is_ge(c) == True{} : Bool}) -> {Cmp.is_ge(Word.cmp.fin(x, False{}, c)) == True{} : Bool}:
  match c x:
    case LT{} _:
      Empty.absurd({Cmp.is_ge(Word.cmp.fin(x, False{}, LT{})) == True{} : Bool}, L.false_true(h))
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case GT{} _:
      {==}

# Nothing compares below zero.
def ge_zero(+n: Nat, +w: Word(n)) -> {Cmp.is_ge(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{x, t}:
      ge_fin_zero(Word.cmp(p, t, Word.zero(p)), x, ge_zero(p, t))

def ge_order(+c: Cmp, +d: Cmp, +h: {Cmp.is_ge(d) == True{} : Bool}) -> {Cmp.is_ge(U.order(c, d)) == Cmp.is_ge(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      h
    case GT{}:
      {==}

def threshold() -> {S.sign_threshold(63n) == W.join(32n, 32n, Word.zero(32n), S.sign_threshold(31n)) : Word(64n)}:
  {==}

def threshold_u32() -> {2147483648 == U32{S.sign_threshold(31n)} : U32}:
  {==}

# The sign of the 64-bit word is the top bit of the high limb.
def negative_pack(+lo: U32, +hi: U32) -> {S.negative(W.pack(lo, hi)) == U32.is_ge(hi, 2147483648) : Bool}:
  match lo hi:
    case U32{a} U32{b}:
      %Equal.sym(Word(64n), W.join(32n, 32n, Word.zero(32n), S.sign_threshold(31n)), S.sign_threshold(63n), threshold()) : {Cmp.is_ge(Word.cmp(64n, W.join(32n, 32n, a, b), _)) == U32.is_ge(U32{b}, 2147483648) : Bool}
      %Equal.sym(Cmp, Word.cmp(64n, W.join(32n, 32n, a, b), W.join(32n, 32n, Word.zero(32n), S.sign_threshold(31n))), U.order(Word.cmp(32n, b, S.sign_threshold(31n)), Word.cmp(32n, a, Word.zero(32n))), cmp_join(32n, 32n, a, b, Word.zero(32n), S.sign_threshold(31n))) : {Cmp.is_ge(_) == U32.is_ge(U32{b}, 2147483648) : Bool}
      %Equal.sym(U32, U32{S.sign_threshold(31n)}, 2147483648, threshold_u32()) : {Cmp.is_ge(U.order(Word.cmp(32n, b, S.sign_threshold(31n)), Word.cmp(32n, a, Word.zero(32n)))) == U32.is_ge(U32{b}, _) : Bool}
      ge_order(Word.cmp(32n, b, S.sign_threshold(31n)), Word.cmp(32n, a, Word.zero(32n)), ge_zero(32n, a))

def le_sign_spec(+alo: U32, +ahi: U32, +blo: U32, +bhi: U32, +na: Bool, +nb: Bool) -> {U.le_sign(alo, ahi, blo, bhi, na, nb) == S.order(W.pack(alo, ahi), W.pack(blo, bhi), na, nb) : Bool}:
  match na nb:
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} True{}:
      %cmp_pack(alo, ahi, blo, bhi) : {Cmp.is_le(_) == Cmp.is_le(Word.cmp(64n, W.pack(alo, ahi), W.pack(blo, bhi))) : Bool}
      {==}
    case False{} False{}:
      %cmp_pack(alo, ahi, blo, bhi) : {Cmp.is_le(_) == Cmp.is_le(Word.cmp(64n, W.pack(alo, ahi), W.pack(blo, bhi))) : Bool}
      {==}

# THEOREM: le_signed is the specification's signed 64-bit order.
def le_signed(+a: U.U64, +b: U.U64) -> {U.le_signed(a, b) == S.order(bits(a), bits(b), S.negative(bits(a)), S.negative(bits(b))) : Bool}:
  match a b:
    case U.U64{alo, ahi} U.U64{blo, bhi}:
      %Equal.sym(Bool, S.negative(W.pack(alo, ahi)), U32.is_ge(ahi, 2147483648), negative_pack(alo, ahi)) : {U.le_signed(U.U64{alo, ahi}, U.U64{blo, bhi}) == S.order(W.pack(alo, ahi), W.pack(blo, bhi), _, S.negative(W.pack(blo, bhi))) : Bool}
      %Equal.sym(Bool, S.negative(W.pack(blo, bhi)), U32.is_ge(bhi, 2147483648), negative_pack(blo, bhi)) : {U.le_signed(U.U64{alo, ahi}, U.U64{blo, bhi}) == S.order(W.pack(alo, ahi), W.pack(blo, bhi), U32.is_ge(ahi, 2147483648), _) : Bool}
      le_sign_spec(alo, ahi, blo, bhi, U32.is_ge(ahi, 2147483648), U32.is_ge(bhi, 2147483648))

# ---- zero test ----

def eq_order(+c: Cmp, +d: Cmp) -> {Cmp.is_eq(U.order(c, d)) == Bool.and(Cmp.is_eq(d), Cmp.is_eq(c)) : Bool}:
  match c d:
    case LT{} LT{}:
      {==}
    case LT{} EQ{}:
      {==}
    case LT{} GT{}:
      {==}
    case EQ{} LT{}:
      {==}
    case EQ{} EQ{}:
      {==}
    case EQ{} GT{}:
      {==}
    case GT{} LT{}:
      {==}
    case GT{} EQ{}:
      {==}
    case GT{} GT{}:
      {==}

def zero_pack() -> {Word.zero(64n) == W.pack(0, 0) : Word(64n)}:
  {==}

# THEOREM: is_zero is the specification's zero test.
def is_zero(+a: U.U64) -> {U.is_zero(a) == S.zero(bits(a)) : Bool}:
  match a:
    case U.U64{lo, hi}:
      %Equal.sym(Word(64n), W.pack(0, 0), Word.zero(64n), zero_pack()) : {U.is_zero(U.U64{lo, hi}) == Cmp.is_eq(Word.cmp(64n, W.pack(lo, hi), _)) : Bool}
      %Equal.sym(Cmp, Word.cmp(64n, W.pack(lo, hi), W.pack(0, 0)), U.order(U32.cmp(hi, 0), U32.cmp(lo, 0)), cmp_pack(lo, hi, 0, 0)) : {U.is_zero(U.U64{lo, hi}) == Cmp.is_eq(_) : Bool}
      Equal.sym(Bool, Cmp.is_eq(U.order(U32.cmp(hi, 0), U32.cmp(lo, 0))), Bool.and(Cmp.is_eq(U32.cmp(lo, 0)), Cmp.is_eq(U32.cmp(hi, 0))), eq_order(U32.cmp(hi, 0), U32.cmp(lo, 0)))

# ---- addition ----

def val(+a: U.U64) -> Nat:
  S.unsigned(64n, bits(a))

def val_pack(+lo: U32, +hi: U32) -> {S.unsigned(64n, W.pack(lo, hi)) == Nat.add(UD.v(lo), WD.sc(32n, UD.v(hi))) : Nat}:
  NUM.pack_interpretation(lo, hi)

def carry32(+x: U32, +y: U32) -> Bool:
  match x y:
    case U32{a} U32{b}:
      AD.carry_out(32n, a, b, False{})

def add_cons(+x: U32, +y: U32) -> {Nat.add(UD.v(U32.add(x, y)), WD.sc(32n, S.bit_value(carry32(x, y)))) == Nat.add(UD.v(x), UD.v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      %Equal.sym(Nat, UD.v(U32{Word.add(32n, a, b)}), WD.uw(32n, Word.add(32n, a, b)), UD.vw(Word.add(32n, a, b))) : {Nat.add(_, WD.sc(32n, S.bit_value(AD.carry_out(32n, a, b, False{})))) == Nat.add(UD.v(U32{a}), UD.v(U32{b})) : Nat}
      %Equal.sym(Nat, UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)) : {Nat.add(WD.uw(32n, Word.add(32n, a, b)), WD.sc(32n, S.bit_value(AD.carry_out(32n, a, b, False{})))) == Nat.add(_, UD.v(U32{b})) : Nat}
      %Equal.sym(Nat, UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)) : {Nat.add(WD.uw(32n, Word.add(32n, a, b)), WD.sc(32n, S.bit_value(AD.carry_out(32n, a, b, False{})))) == Nat.add(WD.uw(32n, a), _) : Nat}
      A.cons(32n, a, b)

def add_lt1(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32) -> {U32.is_lt(U32.add(x, y), x) == carry32(x, y) : Bool}:
  %Equal.sym(Bool, U32.is_lt(U32.add(x, y), x), Nat.is_lt(UD.v(U32.add(x, y)), UD.v(x)), U3.is_lt_nat(U32.add(x, y), x)) : {_ == carry32(x, y) : Bool}
  WD.carry_lt(32n, one, h1, UD.v(U32.add(x, y)), UD.v(x), UD.v(y), carry32(x, y), add_cons(x, y), UD.vb(one, h1, y))

# the low-limb wrap test is the low-limb carry
def add_lt(+x: U32, +y: U32) -> {U32.is_lt(U32.add(x, y), x) == carry32(x, y) : Bool}:
  add_lt1(1n, {==}, x, y)

def carry_v(+c: Bool) -> {UD.v(U.carry(c)) == S.bit_value(c) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def add_hi(ahi: U32, bhi: U32, c: Bool) -> U32:
  U32.add(U32.add(ahi, bhi), U.carry(c))

def add_over(a: U.U64, b: U.U64) -> Nat:
  match a b:
    case U.U64{+alo, +ahi} U.U64{+blo, +bhi}:
      Nat.add(S.bit_value(carry32(ahi, bhi)), S.bit_value(carry32(U32.add(ahi, bhi), U.carry(U32.is_lt(U32.add(alo, blo), alo)))))

# the sum loses exactly 2^64 times the high carries
def add_value(+a: U.U64, +b: U.U64) -> {Nat.add(val(U.add(a, b)), WD.sc(64n, add_over(a, b))) == Nat.add(val(a), val(b)) : Nat}:
  match a b:
    case U.U64{+alo, +ahi} U.U64{+blo, +bhi}:
      +lo = U32.add(alo, blo)
      +cb = U32.is_lt(lo, alo)
      +t = U32.add(ahi, bhi)
      +h = U32.add(t, U.carry(cb))
      +c0 = S.bit_value(carry32(alo, blo))
      +c1 = S.bit_value(carry32(ahi, bhi))
      +c2 = S.bit_value(carry32(t, U.carry(cb)))
      +f1 = add_cons(alo, blo)
      +f2 = add_cons(ahi, bhi)
      +f3 = Equal.trans(Nat, Nat.add(UD.v(h), WD.sc(32n, c2)), Nat.add(UD.v(t), UD.v(U.carry(cb))), Nat.add(UD.v(t), c0), add_cons(t, U.carry(cb)),
        Equal.cong(Nat, Nat, z => Nat.add(UD.v(t), z), UD.v(U.carry(cb)), c0, Equal.trans(Nat, UD.v(U.carry(cb)), S.bit_value(cb), c0, carry_v(cb), Equal.cong(Bool, Nat, S.bit_value, cb, carry32(alo, blo), add_lt(alo, blo)))))
      %Equal.sym(Nat, S.unsigned(64n, W.pack(lo, h)), Nat.add(UD.v(lo), WD.sc(32n, UD.v(h))), val_pack(lo, h)) : {Nat.add(_, WD.sc(64n, Nat.add(c1, c2))) == Nat.add(S.unsigned(64n, W.pack(alo, ahi)), S.unsigned(64n, W.pack(blo, bhi))) : Nat}
      %Equal.sym(Nat, S.unsigned(64n, W.pack(alo, ahi)), Nat.add(UD.v(alo), WD.sc(32n, UD.v(ahi))), val_pack(alo, ahi)) : {Nat.add(Nat.add(UD.v(lo), WD.sc(32n, UD.v(h))), WD.sc(64n, Nat.add(c1, c2))) == Nat.add(_, S.unsigned(64n, W.pack(blo, bhi))) : Nat}
      %Equal.sym(Nat, S.unsigned(64n, W.pack(blo, bhi)), Nat.add(UD.v(blo), WD.sc(32n, UD.v(bhi))), val_pack(blo, bhi)) : {Nat.add(Nat.add(UD.v(lo), WD.sc(32n, UD.v(h))), WD.sc(64n, Nat.add(c1, c2))) == Nat.add(Nat.add(UD.v(alo), WD.sc(32n, UD.v(ahi))), _) : Nat}
      WD.add_alg(32n, UD.v(lo), UD.v(h), UD.v(t), c0, c1, c2, UD.v(alo), UD.v(ahi), UD.v(blo), UD.v(bhi), f1, f2, f3)

# THEOREM: add is 64-bit wrapping addition.
def add(+a: U.U64, +b: U.U64) -> {bits(U.add(a, b)) == Word.add(64n, bits(a), bits(b)) : Word(64n)}:
  Equal.trans(Word(64n), bits(U.add(a, b)), S.from_nat(64n, Nat.add(val(a), val(b))), Word.add(64n, bits(a), bits(b)),
    Equal.trans(Word(64n), bits(U.add(a, b)), S.from_nat(64n, Nat.add(val(U.add(a, b)), WD.sc(64n, add_over(a, b)))), S.from_nat(64n, Nat.add(val(a), val(b))),
      Equal.sym(Word(64n), S.from_nat(64n, Nat.add(val(U.add(a, b)), WD.sc(64n, add_over(a, b)))), bits(U.add(a, b)), MA.reconstruct(64n, bits(U.add(a, b)), add_over(a, b))),
      Equal.cong(Nat, Word(64n), z => S.from_nat(64n, z), Nat.add(val(U.add(a, b)), WD.sc(64n, add_over(a, b))), Nat.add(val(a), val(b)), add_value(a, b))),
    Equal.sym(Word(64n), Word.add(64n, bits(a), bits(b)), S.from_nat(64n, Nat.add(val(a), val(b))), WA.refines(64n, bits(a), bits(b))))

# ---- negation ----

def inc_zero32(+x: Word(32n)) -> {U32.is_zero(U32{Word.inc(32n, x)}) == WD.ones(32n, x) : Bool}:
  WD.inc_zero(32n, x)

def add_carry(+xw: Word(32n), +c: Bool) -> {U32.add(U32{xw}, U.carry(c)) == U32{WD.incif(32n, c, xw)} : U32}:
  match c:
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, xw, WD.one_word(31n)), Word.inc(32n, xw), WD.add_one(31n, xw))
    case False{}:
      A.add_zero(U32{xw})

# THEOREM: neg is two's-complement negation.
def neg(+a: U.U64) -> {bits(U.neg(a)) == Word.inc(64n, Word.not(64n, bits(a))) : Word(64n)}:
  match a:
    case U.U64{+lo, +hi}:
      match lo hi:
        case U32{+x} U32{+y}:
          +nx = Word.not(32n, x)
          +ny = Word.not(32n, y)
          +j = W.join(32n, 32n, Word.inc(32n, nx), WD.incif(32n, WD.ones(32n, nx), ny))
          +p1 = Equal.cong(U32, Word(64n), z => W.pack(U32{Word.inc(32n, nx)}, z), U32.add(U32{ny}, U.carry(U32.is_zero(U32{Word.inc(32n, nx)}))), U32{WD.incif(32n, WD.ones(32n, nx), ny)},
            Equal.trans(U32, U32.add(U32{ny}, U.carry(U32.is_zero(U32{Word.inc(32n, nx)}))), U32.add(U32{ny}, U.carry(WD.ones(32n, nx))), U32{WD.incif(32n, WD.ones(32n, nx), ny)},
              Equal.cong(Bool, U32, c => U32.add(U32{ny}, U.carry(c)), U32.is_zero(U32{Word.inc(32n, nx)}), WD.ones(32n, nx), inc_zero32(nx)),
              add_carry(ny, WD.ones(32n, nx))))
          +p2 = Equal.trans(Word(64n), Word.inc(64n, Word.not(64n, W.join(32n, 32n, x, y))), Word.inc(64n, W.join(32n, 32n, nx, ny)), j,
            Equal.cong(Word(64n), Word(64n), w => Word.inc(64n, w), Word.not(64n, W.join(32n, 32n, x, y)), W.join(32n, 32n, nx, ny), WD.not_join(32n, 32n, x, y)),
            WD.inc_join(32n, 32n, nx, ny))
          Equal.trans(Word(64n), bits(U.neg(U.U64{U32{x}, U32{y}})), j, Word.inc(64n, Word.not(64n, W.join(32n, 32n, x, y))), p1, Equal.sym(Word(64n), Word.inc(64n, Word.not(64n, W.join(32n, 32n, x, y))), j, p2))
