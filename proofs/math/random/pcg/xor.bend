import Base
import ../../../../spec/lib/common.bend as C
import ../../../../spec/math/w64.bend as SW
import ../../../../spec/math/random/pcg.bend as SP
import ../../../../src/math/u64.bend as WU
import ../../../../src/math/random/pcg.bend as P
import ../../../lib/lemmas/spec/numeric.bend as S
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../lib/word.bend as WD
import ../../../lib/u32div.bend as UD
import ../../../lib/logic.bend as L
import ../../typed/width.bend as WW
import ../../typed/w64sh.bend as SH

# Exclusive or on words against SP.xor_bits on their values: bit by bit on
# a Word(n), then split at a limb boundary, then the two-limb U64 of
# src/math/random/pcg.bend's xor64.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the low bit and the rest of bv(b) + 2 u
def bit_bvd(+b: Bool, +u: Nat) -> {C.bit(Nat.add(S.bit_value(b), Nat.double(u))) == S.bit_value(b) : Nat}:
  match b:
    case True{}:
      WW.bit_dbl(1n, u)
    case False{}:
      WW.bit_dbl(0n, u)

def xbit(+a: Bool, +b: Bool) -> {S.bit_value(Bool.xor(a, b)) == SP.b2n(Bool.not(Nat.is_eq(S.bit_value(a), S.bit_value(b)))) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# one step of xor_bits on two values written bit + 2 rest
def step_eq(+p: Nat, +ba: Bool, +ua: Nat, +bb: Bool, +ub: Nat) -> {SP.xor_bits(1n+p, Nat.add(S.bit_value(ba), Nat.double(ua)), Nat.add(S.bit_value(bb), Nat.double(ub))) == Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, ub))) : Nat}:
  +A = Nat.add(S.bit_value(ba), Nat.double(ua))
  +B = Nat.add(S.bit_value(bb), Nat.double(ub))
  %Equal.sym(Nat, C.bit(A), S.bit_value(ba), bit_bvd(ba, ua)) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(_, C.bit(B)))), Nat.double(SP.xor_bits(p, C.half(A), C.half(B)))) == Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, ub))) : Nat}
  %Equal.sym(Nat, C.bit(B), S.bit_value(bb), bit_bvd(bb, ub)) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), _))), Nat.double(SP.xor_bits(p, C.half(A), C.half(B)))) == Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, ub))) : Nat}
  %Equal.sym(Nat, C.half(A), ua, SH.half_bv(ba, ua)) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, _, C.half(B)))) == Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, ub))) : Nat}
  %Equal.sym(Nat, C.half(B), ub, SH.half_bv(bb, ub)) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, _))) == Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(ba), S.bit_value(bb)))), Nat.double(SP.xor_bits(p, ua, ub))) : Nat}
  {==}

# the value of a word xor is xor_bits of the values
def xor_word(+n: Nat, +x: Word(n), +y: Word(n)) -> {WD.uw(n, Word.xor(n, x, y)) == SP.xor_bits(n, WD.uw(n, x), WD.uw(n, y)) : Nat}:
  match n x y:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{+a, +xt} WCon{+b, +yt}:
      +M = Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(a), S.bit_value(b)))), Nat.double(SP.xor_bits(p, WD.uw(p, xt), WD.uw(p, yt))))
      +e1 = Equal.trans(Nat, Nat.add(S.bit_value(Bool.xor(a, b)), Nat.double(WD.uw(p, Word.xor(p, xt, yt)))), Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(a), S.bit_value(b)))), Nat.double(WD.uw(p, Word.xor(p, xt, yt)))), M,
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(WD.uw(p, Word.xor(p, xt, yt)))), S.bit_value(Bool.xor(a, b)), SP.b2n(Bool.not(Nat.is_eq(S.bit_value(a), S.bit_value(b)))), xbit(a, b)),
        Equal.cong(Nat, Nat, z => Nat.add(SP.b2n(Bool.not(Nat.is_eq(S.bit_value(a), S.bit_value(b)))), Nat.double(z)), WD.uw(p, Word.xor(p, xt, yt)), SP.xor_bits(p, WD.uw(p, xt), WD.uw(p, yt)), xor_word(p, xt, yt)))
      Equal.trans(Nat, Nat.add(S.bit_value(Bool.xor(a, b)), Nat.double(WD.uw(p, Word.xor(p, xt, yt)))), M, SP.xor_bits(1n+p, Nat.add(S.bit_value(a), Nat.double(WD.uw(p, xt))), Nat.add(S.bit_value(b), Nat.double(WD.uw(p, yt)))),
        e1, Equal.sym(Nat, SP.xor_bits(1n+p, Nat.add(S.bit_value(a), Nat.double(WD.uw(p, xt))), Nat.add(S.bit_value(b), Nat.double(WD.uw(p, yt)))), M, step_eq(p, a, WD.uw(p, xt), b, WD.uw(p, yt))))

def xor32(+x: U32, +y: U32) -> {v(U32.xor(x, y)) == SP.xor_bits(32n, v(x), v(y)) : Nat}:
  match x y:
    case U32{+wx} U32{+wy}:
      %Equal.sym(Nat, v(U32{wx}), WD.uw(32n, wx), UD.vw(wx)) : {v(U32{Word.xor(32n, wx, wy)}) == SP.xor_bits(32n, _, v(U32{wy})) : Nat}
      %Equal.sym(Nat, v(U32{wy}), WD.uw(32n, wy), UD.vw(wy)) : {v(U32{Word.xor(32n, wx, wy)}) == SP.xor_bits(32n, WD.uw(32n, wx), _) : Nat}
      Equal.trans(Nat, v(U32{Word.xor(32n, wx, wy)}), WD.uw(32n, Word.xor(32n, wx, wy)), SP.xor_bits(32n, WD.uw(32n, wx), WD.uw(32n, wy)), UD.vw(Word.xor(32n, wx, wy)), xor_word(32n, wx, wy))

def fits0(+a: Nat, +h: {C.fits(0n, a) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      Empty.absurd({1n+q == 0n : Nat}, L.false_true(h))

# xor_bits splits at bit k when the low parts fit k bits
def xsplit(+k: Nat, +j: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +ha: {C.fits(k, al) == True{} : Bool}, +hb: {C.fits(k, bl) == True{} : Bool}) -> {SP.xor_bits(Nat.add(k, j), Nat.add(al, C.shift(k, ah)), Nat.add(bl, C.shift(k, bh))) == Nat.add(SP.xor_bits(k, al, bl), C.shift(k, SP.xor_bits(j, ah, bh))) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, al, 0n, fits0(al, ha)) : {SP.xor_bits(j, Nat.add(_, ah), Nat.add(bl, bh)) == SP.xor_bits(j, ah, bh) : Nat}
      %Equal.sym(Nat, bl, 0n, fits0(bl, hb)) : {SP.xor_bits(j, Nat.add(0n, ah), Nat.add(_, bh)) == SP.xor_bits(j, ah, bh) : Nat}
      {==}
    case 1n+p:
      +A = Nat.add(al, Nat.double(C.shift(p, ah)))
      +B = Nat.add(bl, Nat.double(C.shift(p, bh)))
      +X = SP.xor_bits(j, ah, bh)
      +Y = SP.xor_bits(p, C.half(al), C.half(bl))
      +bx = SP.b2n(Bool.not(Nat.is_eq(C.bit(al), C.bit(bl))))
      %Equal.sym(Nat, C.bit(A), C.bit(al), WW.bit_dbl(al, C.shift(p, ah))) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(_, C.bit(B)))), Nat.double(SP.xor_bits(Nat.add(p, j), C.half(A), C.half(B)))) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.bit(B), C.bit(bl), WW.bit_dbl(bl, C.shift(p, bh))) : {Nat.add(SP.b2n(Bool.not(Nat.is_eq(C.bit(al), _))), Nat.double(SP.xor_bits(Nat.add(p, j), C.half(A), C.half(B)))) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.half(A), Nat.add(C.half(al), C.shift(p, ah)), WW.half_dbl(al, C.shift(p, ah))) : {Nat.add(bx, Nat.double(SP.xor_bits(Nat.add(p, j), _, C.half(B)))) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, C.half(B), Nat.add(C.half(bl), C.shift(p, bh)), WW.half_dbl(bl, C.shift(p, bh))) : {Nat.add(bx, Nat.double(SP.xor_bits(Nat.add(p, j), Nat.add(C.half(al), C.shift(p, ah)), _))) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, SP.xor_bits(Nat.add(p, j), Nat.add(C.half(al), C.shift(p, ah)), Nat.add(C.half(bl), C.shift(p, bh))), Nat.add(Y, C.shift(p, X)), xsplit(p, j, C.half(al), ah, C.half(bl), bh, ha, hb)) : {Nat.add(bx, Nat.double(_)) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      %Equal.sym(Nat, Nat.double(Nat.add(Y, C.shift(p, X))), Nat.add(Nat.double(Y), Nat.double(C.shift(p, X))), NA.double_add(Y, C.shift(p, X))) : {Nat.add(bx, _) == Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(bx, Nat.double(Y)), Nat.double(C.shift(p, X))), Nat.add(bx, Nat.add(Nat.double(Y), Nat.double(C.shift(p, X)))), NA.add_assoc(bx, Nat.double(Y), Nat.double(C.shift(p, X))))

# THEOREM: the value of xor64 is xor_bits(64) of the values
def xor64_value(+a: WU.U64, +b: WU.U64) -> {SW.value(P.xor64(a, b)) == SP.xor_bits(64n, SW.value(a), SW.value(b)) : Nat}:
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      %Equal.sym(Nat, v(U32.xor(al, bl)), SP.xor_bits(32n, v(al), v(bl)), xor32(al, bl)) : {Nat.add(_, C.shift(32n, v(U32.xor(ah, bh)))) == SP.xor_bits(64n, Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))) : Nat}
      %Equal.sym(Nat, v(U32.xor(ah, bh)), SP.xor_bits(32n, v(ah), v(bh)), xor32(ah, bh)) : {Nat.add(SP.xor_bits(32n, v(al), v(bl)), C.shift(32n, _)) == SP.xor_bits(64n, Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))) : Nat}
      Equal.sym(Nat, SP.xor_bits(Nat.add(32n, 32n), Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(SP.xor_bits(32n, v(al), v(bl)), C.shift(32n, SP.xor_bits(32n, v(ah), v(bh)))), xsplit(32n, 32n, v(al), v(ah), v(bl), v(bh), SH.vb(al), SH.vb(bl)))
