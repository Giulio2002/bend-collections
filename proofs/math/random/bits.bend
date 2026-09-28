import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random/rand.bend as SR
import ../../../src/math/u64.bend as WU
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../typed/width.bend as WI
import ../typed/w64add.bend as WA

# Bitwise and on words against SR.and_bits on their values: bit by bit on
# U32 words, then a 64-bit word as two 32-bit limbs.

def bv(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# one bit and the rest: (b + 2a) & (c + 2d) = b c + 2 (a & d)
def and_step(+p: Nat, +b: Nat, +a: Nat, +c: Nat, +d: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +hc: {Nat.is_le(c, 1n) == True{} : Bool}) -> {SR.and_bits(1n+p, Nat.add(b, Nat.double(a)), Nat.add(c, Nat.double(d))) == Nat.add(Nat.mul(b, c), Nat.double(SR.and_bits(p, a, d))) : Nat}:
  match b c:
    case 0n 0n:
      %Equal.sym(Nat, C.bit(Nat.double(a)), 0n, WI.bit_dbl(0n, a)) : {Nat.add(Nat.mul(_, C.bit(Nat.double(d))), Nat.double(SR.and_bits(p, C.half(Nat.double(a)), C.half(Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(Nat.double(a)), a, WI.half_dbl(0n, a)) : {Nat.add(Nat.mul(0n, C.bit(Nat.double(d))), Nat.double(SR.and_bits(p, _, C.half(Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(Nat.double(d)), d, WI.half_dbl(0n, d)) : {Nat.add(Nat.mul(0n, C.bit(Nat.double(d))), Nat.double(SR.and_bits(p, a, _))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      {==}
    case 0n 1n:
      %Equal.sym(Nat, C.bit(Nat.double(a)), 0n, WI.bit_dbl(0n, a)) : {Nat.add(Nat.mul(_, C.bit(1n+Nat.double(d))), Nat.double(SR.and_bits(p, C.half(Nat.double(a)), C.half(1n+Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(Nat.double(a)), a, WI.half_dbl(0n, a)) : {Nat.add(Nat.mul(0n, C.bit(1n+Nat.double(d))), Nat.double(SR.and_bits(p, _, C.half(1n+Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(1n+Nat.double(d)), d, WI.half_dbl(1n, d)) : {Nat.add(Nat.mul(0n, C.bit(1n+Nat.double(d))), Nat.double(SR.and_bits(p, a, _))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      {==}
    case 1n 0n:
      %Equal.sym(Nat, C.bit(1n+Nat.double(a)), 1n, WI.bit_dbl(1n, a)) : {Nat.add(Nat.mul(_, C.bit(Nat.double(d))), Nat.double(SR.and_bits(p, C.half(1n+Nat.double(a)), C.half(Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.bit(Nat.double(d)), 0n, WI.bit_dbl(0n, d)) : {Nat.add(Nat.mul(1n, _), Nat.double(SR.and_bits(p, C.half(1n+Nat.double(a)), C.half(Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(1n+Nat.double(a)), a, WI.half_dbl(1n, a)) : {Nat.add(Nat.mul(1n, 0n), Nat.double(SR.and_bits(p, _, C.half(Nat.double(d))))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(Nat.double(d)), d, WI.half_dbl(0n, d)) : {Nat.add(Nat.mul(1n, 0n), Nat.double(SR.and_bits(p, a, _))) == Nat.add(0n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      {==}
    case 1n 1n:
      %Equal.sym(Nat, C.bit(1n+Nat.double(a)), 1n, WI.bit_dbl(1n, a)) : {Nat.add(Nat.mul(_, C.bit(1n+Nat.double(d))), Nat.double(SR.and_bits(p, C.half(1n+Nat.double(a)), C.half(1n+Nat.double(d))))) == Nat.add(1n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.bit(1n+Nat.double(d)), 1n, WI.bit_dbl(1n, d)) : {Nat.add(Nat.mul(1n, _), Nat.double(SR.and_bits(p, C.half(1n+Nat.double(a)), C.half(1n+Nat.double(d))))) == Nat.add(1n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(1n+Nat.double(a)), a, WI.half_dbl(1n, a)) : {Nat.add(Nat.mul(1n, 1n), Nat.double(SR.and_bits(p, _, C.half(1n+Nat.double(d))))) == Nat.add(1n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      %Equal.sym(Nat, C.half(1n+Nat.double(d)), d, WI.half_dbl(1n, d)) : {Nat.add(Nat.mul(1n, 1n), Nat.double(SR.and_bits(p, a, _))) == Nat.add(1n, Nat.double(SR.and_bits(p, a, d))) : Nat}
      {==}
    case 2n+q _:
      Empty.absurd({SR.and_bits(1n+p, Nat.add(2n+q, Nat.double(a)), Nat.add(c, Nat.double(d))) == Nat.add(Nat.mul(2n+q, c), Nat.double(SR.and_bits(p, a, d))) : Nat}, L.false_true(hb))
    case _ 2n+q:
      Empty.absurd({SR.and_bits(1n+p, Nat.add(b, Nat.double(a)), Nat.add(2n+q, Nat.double(d))) == Nat.add(Nat.mul(b, 2n+q), Nat.double(SR.and_bits(p, a, d))) : Nat}, L.false_true(hc))

def bv_le(+b: Bool) -> {Nat.is_le(bv(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bv_and(+x: Bool, +y: Bool) -> {bv(Bool.and(x, y)) == Nat.mul(bv(x), bv(y)) : Nat}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

# a word's value, its low bit first
def to_nat_con(+p: Nat, +x: Bool, +t: Word(p)) -> {Word.to_nat(1n+p, WCon{x, t}) == Nat.add(bv(x), Nat.double(Word.to_nat(p, t))) : Nat}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# THEOREM: Word.and is and_bits on the values
def wand(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.to_nat(n, Word.and(n, a, b)) == SR.and_bits(n, Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{+x, +t} WCon{+y, +u}:
      +e1 = to_nat_con(p, Bool.and(x, y), Word.and(p, t, u))
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(bv(Bool.and(x, y)), Nat.double(z)), Word.to_nat(p, Word.and(p, t, u)), SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)), wand(p, t, u))
      +e3 = Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)))), bv(Bool.and(x, y)), Nat.mul(bv(x), bv(y)), bv_and(x, y))
      +e4 = Equal.sym(Nat, SR.and_bits(1n+p, Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), Nat.add(bv(y), Nat.double(Word.to_nat(p, u)))), Nat.add(Nat.mul(bv(x), bv(y)), Nat.double(SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)))), and_step(p, bv(x), Word.to_nat(p, t), bv(y), Word.to_nat(p, u), bv_le(x), bv_le(y)))
      %Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, t}), Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), to_nat_con(p, x, t)) : {Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, t, u)}) == SR.and_bits(1n+p, _, Word.to_nat(1n+p, WCon{y, u})) : Nat}
      %Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, u}), Nat.add(bv(y), Nat.double(Word.to_nat(p, u))), to_nat_con(p, y, u)) : {Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, t, u)}) == SR.and_bits(1n+p, Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), _) : Nat}
      Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, t, u)}), Nat.add(bv(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, t, u)))), SR.and_bits(1n+p, Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), Nat.add(bv(y), Nat.double(Word.to_nat(p, u)))), e1,
        Equal.trans(Nat, Nat.add(bv(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, t, u)))), Nat.add(bv(Bool.and(x, y)), Nat.double(SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)))), SR.and_bits(1n+p, Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), Nat.add(bv(y), Nat.double(Word.to_nat(p, u)))), e2,
          Equal.trans(Nat, Nat.add(bv(Bool.and(x, y)), Nat.double(SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)))), Nat.add(Nat.mul(bv(x), bv(y)), Nat.double(SR.and_bits(p, Word.to_nat(p, t), Word.to_nat(p, u)))), SR.and_bits(1n+p, Nat.add(bv(x), Nat.double(Word.to_nat(p, t))), Nat.add(bv(y), Nat.double(Word.to_nat(p, u)))), e3, e4)))

def uand(+x: U32, +y: U32) -> {U32.to_nat(U32.and(x, y)) == SR.and_bits(32n, U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      wand(32n, a, b)

# THEOREM: and on two limbs, (a1 + 2^k b1) & (a2 + 2^k b2) = a1 & a2 + 2^k (b1 & b2)
def and_join(+k: Nat, +j: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +h1: {C.fits(k, a1) == True{} : Bool}, +h2: {C.fits(k, a2) == True{} : Bool}) -> {SR.and_bits(Nat.add(k, j), Nat.add(a1, C.shift(k, b1)), Nat.add(a2, C.shift(k, b2))) == Nat.add(SR.and_bits(k, a1, a2), C.shift(k, SR.and_bits(j, b1, b2))) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, a1, 0n, N.eq_from_is_eq(a1, 0n, h1)) : {SR.and_bits(j, Nat.add(_, b1), Nat.add(a2, b2)) == Nat.add(SR.and_bits(0n, _, a2), SR.and_bits(j, b1, b2)) : Nat}
      %Equal.sym(Nat, a2, 0n, N.eq_from_is_eq(a2, 0n, h2)) : {SR.and_bits(j, b1, Nat.add(_, b2)) == Nat.add(SR.and_bits(0n, 0n, _), SR.and_bits(j, b1, b2)) : Nat}
      {==}
    case 1n+p:
      +S1 = C.shift(p, b1)
      +S2 = C.shift(p, b2)
      +X = SR.and_bits(j, b1, b2)
      +B = Nat.mul(C.bit(a1), C.bit(a2))
      +Ih = and_join(p, j, C.half(a1), b1, C.half(a2), b2, h1, h2)
      %Equal.sym(Nat, C.bit(Nat.add(a1, Nat.double(S1))), C.bit(a1), WI.bit_dbl(a1, S1)) : {Nat.add(Nat.mul(_, C.bit(Nat.add(a2, Nat.double(S2)))), Nat.double(SR.and_bits(Nat.add(p, j), C.half(Nat.add(a1, Nat.double(S1))), C.half(Nat.add(a2, Nat.double(S2)))))) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.bit(Nat.add(a2, Nat.double(S2))), C.bit(a2), WI.bit_dbl(a2, S2)) : {Nat.add(Nat.mul(C.bit(a1), _), Nat.double(SR.and_bits(Nat.add(p, j), C.half(Nat.add(a1, Nat.double(S1))), C.half(Nat.add(a2, Nat.double(S2)))))) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.half(Nat.add(a1, Nat.double(S1))), Nat.add(C.half(a1), S1), WI.half_dbl(a1, S1)) : {Nat.add(B, Nat.double(SR.and_bits(Nat.add(p, j), _, C.half(Nat.add(a2, Nat.double(S2)))))) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.half(Nat.add(a2, Nat.double(S2))), Nat.add(C.half(a2), S2), WI.half_dbl(a2, S2)) : {Nat.add(B, Nat.double(SR.and_bits(Nat.add(p, j), Nat.add(C.half(a1), S1), _))) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, SR.and_bits(Nat.add(p, j), Nat.add(C.half(a1), S1), Nat.add(C.half(a2), S2)), Nat.add(SR.and_bits(p, C.half(a1), C.half(a2)), C.shift(p, X)), Ih) : {Nat.add(B, Nat.double(_)) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      %N.add_double(SR.and_bits(p, C.half(a1), C.half(a2)), C.shift(p, X)) : {Nat.add(B, _) == Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2)))), Nat.double(C.shift(p, X))), Nat.add(B, Nat.add(Nat.double(SR.and_bits(p, C.half(a1), C.half(a2))), Nat.double(C.shift(p, X)))), N.add_assoc(B, Nat.double(SR.and_bits(p, C.half(a1), C.half(a2))), Nat.double(C.shift(p, X))))

# THEOREM: the 64-bit and of rand.bend is and_bits on the values
def and64_value(+a: WU.U64, +b: WU.U64) -> {SW.value(R.and64(a, b)) == SR.and_bits(64n, SW.value(a), SW.value(b)) : Nat}:
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      %Equal.sym(Nat, U32.to_nat(U32.and(al, bl)), SR.and_bits(32n, U32.to_nat(al), U32.to_nat(bl)), uand(al, bl)) : {Nat.add(_, C.shift(32n, U32.to_nat(U32.and(ah, bh)))) == SR.and_bits(64n, SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.and(ah, bh)), SR.and_bits(32n, U32.to_nat(ah), U32.to_nat(bh)), uand(ah, bh)) : {Nat.add(SR.and_bits(32n, U32.to_nat(al), U32.to_nat(bl)), C.shift(32n, _)) == SR.and_bits(64n, SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})) : Nat}
      Equal.sym(Nat, SR.and_bits(64n, SW.value(WU.U64{al, ah}), SW.value(WU.U64{bl, bh})), Nat.add(SR.and_bits(32n, U32.to_nat(al), U32.to_nat(bl)), C.shift(32n, SR.and_bits(32n, U32.to_nat(ah), U32.to_nat(bh)))), and_join(32n, 32n, U32.to_nat(al), U32.to_nat(ah), U32.to_nat(bl), U32.to_nat(bh), WA.vb(al), WA.vb(bl)))
