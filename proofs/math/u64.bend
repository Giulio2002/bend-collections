import Base
import ../../src/math/u64.bend as U
import ../lemmas/src/wide.bend as W
import ../lemmas/spec/numeric.bend as S
import ../lib/logic.bend as L

# src/math/u64.bend against the 64-bit specification of proofs/lemmas/spec:
# a U64 denotes the 64-bit word whose low 32 bits are lo and high 32 bits hi.

def bits(a: U.U64) -> Word(64n):
  match a:
    case U.U64{lo, hi}:
      W.pack(lo, hi)

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
