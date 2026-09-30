import Base
import ../../../spec/lib/common.bend as SC
import ../../../spec/lib/numeric.bend as SNUM
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/lemmas/proofs/numeric.bend as RN
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L

# The few word and arithmetic lemmas the Poly1305 proofs need, restated here
# from proofs/lib/{arith,u32,u32alg,word}.bend and proofs/math/typed/w64mul.bend
# so that the Poly1305 and AEAD proof roots do not load those libraries (and
# everything they import): same statements, same proofs.

def mul_le(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  +e = Nat.sub(b, a)
  +hb = N.sub_add(b, a, h)
  +m = Equal.trans(Nat, Nat.add(Nat.mul(a, c), Nat.mul(e, c)), Nat.mul(Nat.add(a, e), c), Nat.mul(b, c), Equal.sym(Nat, Nat.mul(Nat.add(a, e), c), Nat.add(Nat.mul(a, c), Nat.mul(e, c)), NA.mul_add_right(a, e, c)), Equal.cong(Nat, Nat, z => Nat.mul(z, c), Nat.add(a, e), b, hb))
  L.subst(Nat, z => {Nat.is_le(Nat.mul(a, c), z) == True{} : Bool}, Nat.add(Nat.mul(a, c), Nat.mul(e, c)), Nat.mul(b, c), m, N.le_add_right(Nat.mul(a, c), Nat.mul(e, c)))

def one_mul(+d: Nat) -> {Nat.mul(1n, d) == d : Nat}:
  N.add_zero(d)

def cong_l(+x: Nat, +y: Nat, +z: Nat, +e: {x == y : Nat}) -> {Nat.add(x, z) == Nat.add(y, z) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(t, z), x, y, e)

def cong_r(+z: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.add(z, x) == Nat.add(z, y) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.add(z, t), x, y, e)

def le_mul_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, b), Nat.mul(a, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(a, b), Nat.mul(b, a), NA.mul_comm(a, b)) : {Nat.is_le(_, Nat.mul(a, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(a, c), Nat.mul(c, a), NA.mul_comm(a, c)) : {Nat.is_le(Nat.mul(b, a), _) == True{} : Bool}
  mul_le(b, c, a, h)

def add_cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      Equal.trans(Nat, a, Nat.add(a, 0n), b, Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)), Equal.trans(Nat, Nat.add(a, 0n), Nat.add(b, 0n), b, e, N.add_zero(b)))
    case 1n+k:
      add_cancel_r(a, b, k, N.succ_inj(Nat.add(a, k), Nat.add(b, k), Equal.trans(Nat, 1n+Nat.add(a, k), Nat.add(a, 1n+k), 1n+Nat.add(b, k), Equal.sym(Nat, Nat.add(a, 1n+k), 1n+Nat.add(a, k), N.add_succ(a, k)), Equal.trans(Nat, Nat.add(a, 1n+k), Nat.add(b, 1n+k), 1n+Nat.add(b, k), e, N.add_succ(b, k)))))

def sc_zero(+n: Nat) -> {S.scale_binary(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, S.scale_binary(p, 0n), 0n, sc_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pow2_scale(+k: Nat) -> {SC.pow2(k) == S.scale_binary(k, 1n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, SC.pow2(p), S.scale_binary(p, 1n), pow2_scale(p))

def to_nat_word(+w: Word(32n)) -> {U32.to_nat(U32{w}) == S.unsigned(32n, w) : Nat}:
  RN.primitive_word_interpretation(32n, w)

def uw(+n: Nat, +w: Word(n)) -> Nat:
  S.unsigned(n, w)

def sc(+n: Nat, +k: Nat) -> Nat:
  S.scale_binary(n, k)

def mask(+n: Nat, +k: Nat) -> Word(n):
  SNUM.mask(n, k)

def hi_part(+n: Nat, +k: Nat, +x: Word(n)) -> Nat:
  match n k x:
    case 0n _ WNil{}:
      0n
    case 1n+p 0n WCon{b, t}:
      uw(1n+p, WCon{b, t})
    case 1n+p 1n+j WCon{b, t}:
      hi_part(p, j, t)

def and_false_bv(+b: Bool) -> {S.bit_value(Bool.and(b, False{})) == 0n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_zero(+p: Nat, +t: Word(p)) -> {uw(p, Word.and(p, t, mask(p, 0n))) == 0n : Nat}:
  match p t:
    case 0n WNil{}:
      {==}
    case 1n+q WCon{b, s}:
      %Equal.sym(Nat, S.bit_value(Bool.and(b, False{})), 0n, and_false_bv(b)) : {Nat.add(_, Nat.double(uw(q, Word.and(q, s, mask(q, 0n))))) == 0n : Nat}
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(q, Word.and(q, s, mask(q, 0n))), 0n, and_zero(q, s))

def low0(+p: Nat, +b: Bool, +t: Word(p)) -> {uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n))) == 0n : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(p, Word.and(p, t, mask(p, 0n))), 0n, and_zero(p, t))
    case False{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(p, Word.and(p, t, mask(p, 0n))), 0n, and_zero(p, t))

def lt1r(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, sc(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(x, sc(n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(x, S.scale_binary(n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), h)

def sc_pos(+k: Nat) -> {Nat.is_lt(0n, sc(k, 1n)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      N.double_lt(0n, sc(j, 1n), sc_pos(j))

def mask_lt(+n: Nat, +k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Word(n)) -> {Nat.is_lt(uw(n, Word.and(n, x, mask(n, k))), sc(k, one)) == True{} : Bool}:
  match n k x:
    case 0n _ WNil{}:
      lt1r(k, one, h1, 0n, sc_pos(k))
    case 1n+p 0n WCon{b, t}:
      +z = uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n)))
      L.subst(Nat, o => {Nat.is_lt(z, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, w => {Nat.is_lt(w, 1n) == True{} : Bool}, 0n, z, Equal.sym(Nat, z, 0n, low0(p, b, t)), {==}))
    case 1n+p 1n+j WCon{b, t}:
      N.double_lt_bit(Bool.and(b, True{}), uw(p, Word.and(p, t, mask(p, j))), sc(j, one), mask_lt(p, j, one, h1, t))

def mask_split(+n: Nat, +k: Nat, +x: Word(n)) -> {uw(n, x) == Nat.add(uw(n, Word.and(n, x, mask(n, k))), sc(k, hi_part(n, k, x))) : Nat}:
  match n k x:
    case 0n _ WNil{}:
      Equal.sym(Nat, sc(k, 0n), 0n, sc_zero(k))
    case 1n+p 0n WCon{b, t}:
      %Equal.sym(Nat, uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n))), 0n, low0(p, b, t)) : {uw(1n+p, WCon{b, t}) == Nat.add(_, uw(1n+p, WCon{b, t})) : Nat}
      {==}
    case 1n+p 1n+j WCon{b, t}:
      +at = uw(p, Word.and(p, t, mask(p, j)))
      +hs = sc(j, hi_part(p, j, t))
      %Equal.sym(Bool, Bool.and(b, True{}), b, and_true(b)) : {Nat.add(S.bit_value(b), Nat.double(uw(p, t))) == Nat.add(Nat.add(S.bit_value(_), Nat.double(at)), Nat.double(hs)) : Nat}
      %Equal.sym(Nat, uw(p, t), Nat.add(at, hs), mask_split(p, j, t)) : {Nat.add(S.bit_value(b), Nat.double(_)) == Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)) : Nat}
      Equal.trans(Nat, Nat.add(S.bit_value(b), Nat.double(Nat.add(at, hs))), Nat.add(S.bit_value(b), Nat.add(Nat.double(at), Nat.double(hs))), Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)),
        Equal.cong(Nat, Nat, z => Nat.add(S.bit_value(b), z), Nat.double(Nat.add(at, hs)), Nat.add(Nat.double(at), Nat.double(hs)), Equal.sym(Nat, Nat.add(Nat.double(at), Nat.double(hs)), Nat.double(Nat.add(at, hs)), N.add_double(at, hs))),
        Equal.sym(Nat, Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)), Nat.add(S.bit_value(b), Nat.add(Nat.double(at), Nat.double(hs))), N.add_assoc(S.bit_value(b), Nat.double(at), Nat.double(hs))))
