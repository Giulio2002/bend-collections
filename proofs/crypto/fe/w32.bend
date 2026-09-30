import Base
import ../../../spec/lib/common.bend as C
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32div.bend as UD
import ../../lib/u32half.bend as UH
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M

# 32-bit word facts the curve proofs use (masks, the low bit, shifts,
# exact sums and products), gathered here from proofs/math/u64/u64div.bend,
# proofs/math/typed/shrn.bend, proofs/math/hash/hash.bend and the byte
# field's canon.bend so that the curve proofs do not load those libraries.

def hp32(+k: Nat, x: U32) -> Nat:
  match x:
    case U32{w}:
      WD.hi_part(32n, k, w)

def and32w(+k: Nat, +x: U32) -> {UD.v(x) == Nat.add(UD.v(U32.and(x, U32{WD.mask(32n, k)})), WD.sc(k, hp32(k, x))) : Nat}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, UD.v(U32{w}), WD.uw(32n, w), UD.vw(w)) : {_ == Nat.add(UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.sc(k, WD.hi_part(32n, k, w))) : Nat}
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.uw(32n, Word.and(32n, w, WD.mask(32n, k))), UD.vw(Word.and(32n, w, WD.mask(32n, k)))) : {WD.uw(32n, w) == Nat.add(_, WD.sc(k, WD.hi_part(32n, k, w))) : Nat}
      WD.mask_split(32n, k, w)

def and32(+k: Nat, +x: U32, +m: U32, +hm: {m == U32{WD.mask(32n, k)} : U32}) -> {UD.v(x) == Nat.add(UD.v(U32.and(x, m)), WD.sc(k, hp32(k, x))) : Nat}:
  L.subst(U32, z => {UD.v(x) == Nat.add(UD.v(U32.and(x, z)), WD.sc(k, hp32(k, x))) : Nat}, U32{WD.mask(32n, k)}, m, Equal.sym(U32, m, U32{WD.mask(32n, k)}, hm), and32w(k, x))

def and32_ltw(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32) -> {Nat.is_lt(UD.v(U32.and(x, U32{WD.mask(32n, k)})), WD.sc(k, one)) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, w, WD.mask(32n, k))}), WD.uw(32n, Word.and(32n, w, WD.mask(32n, k))), UD.vw(Word.and(32n, w, WD.mask(32n, k)))) : {Nat.is_lt(_, WD.sc(k, one)) == True{} : Bool}
      WD.mask_lt(32n, k, one, h1, w)

def and32_lt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32, +m: U32, +hm: {m == U32{WD.mask(32n, k)} : U32}) -> {Nat.is_lt(UD.v(U32.and(x, m)), WD.sc(k, one)) == True{} : Bool}:
  L.subst(U32, z => {Nat.is_lt(UD.v(U32.and(x, z)), WD.sc(k, one)) == True{} : Bool}, U32{WD.mask(32n, k)}, m, Equal.sym(U32, m, U32{WD.mask(32n, k)}, hm), and32_ltw(k, one, h1, x))

def add32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.add(UD.v(x), UD.v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.add(x, y)) == Nat.add(UD.v(x), UD.v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      +cv = Equal.trans(Nat, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), Equal.cong(Nat, Nat, z => Nat.add(z, UD.v(U32{b})), UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)), Equal.cong(Nat, Nat, z => Nat.add(WD.uw(32n, a), z), UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)))
      +hw = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), cv, h)
      Equal.trans(Nat, UD.v(U32{Word.add(32n, a, b)}), WD.uw(32n, Word.add(32n, a, b)), Nat.add(UD.v(U32{a}), UD.v(U32{b})), UD.vw(Word.add(32n, a, b)), Equal.trans(Nat, WD.uw(32n, Word.add(32n, a, b)), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), Nat.add(UD.v(U32{a}), UD.v(U32{b})), WD.add_exact(32n, one, h1, a, b, hw), Equal.sym(Nat, Nat.add(UD.v(U32{a}), UD.v(U32{b})), Nat.add(WD.uw(32n, a), WD.uw(32n, b)), cv)))

def mul32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.mul(UD.v(x), UD.v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.mul(x, y)) == Nat.mul(UD.v(x), UD.v(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      +cv = Equal.trans(Nat, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), Equal.cong(Nat, Nat, z => Nat.mul(z, UD.v(U32{b})), UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)), Equal.cong(Nat, Nat, z => Nat.mul(WD.uw(32n, a), z), UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)))
      +hw = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), cv, h)
      Equal.trans(Nat, UD.v(U32{Word.mul(32n, a, b)}), WD.uw(32n, Word.mul(32n, a, b)), Nat.mul(UD.v(U32{a}), UD.v(U32{b})), UD.vw(Word.mul(32n, a, b)), Equal.trans(Nat, WD.uw(32n, Word.mul(32n, a, b)), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), Nat.mul(UD.v(U32{a}), UD.v(U32{b})), WD.mul_exact(32n, one, h1, a, b, hw), Equal.sym(Nat, Nat.mul(UD.v(U32{a}), UD.v(U32{b})), Nat.mul(WD.uw(32n, a), WD.uw(32n, b)), cv)))

def mul_pow(+one: Nat, +h1: {one == 1n : Nat}, +j: Nat, +c: Nat, +kv: Nat, +hk: {kv == WD.sc(j, one) : Nat}) -> {Nat.mul(c, kv) == WD.sc(j, c) : Nat}:
  Equal.trans(Nat, Nat.mul(c, kv), Nat.mul(c, WD.sc(j, one)), WD.sc(j, c), Equal.cong(Nat, Nat, z => Nat.mul(c, z), kv, WD.sc(j, one), hk), AR.mul_sc1(j, one, h1, c))

# v(x * k) == 2^j v(x) when v(k) == 2^j and 2^j v(x) < 2^32

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- one csub ----

def and1(+one: Nat, +h1: {one == 1n : Nat}, +l: U32) -> {v(U32.and(l, 1)) == Nat.mod(v(l), 2n) : Nat}:
  +a = and32(1n, l, 1, {==})
  +b = and32_lt(1n, one, h1, l, 1, {==})
  +hp = hp32(1n, l)
  +b2 = L.subst(Nat, o => {Nat.is_lt(v(U32.and(l, 1)), WD.sc(1n, o)) == True{} : Bool}, one, 1n, h1, b)
  +e1 = Equal.trans(Nat, v(l), Nat.add(v(U32.and(l, 1)), WD.sc(1n, hp)), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), a, Equal.trans(Nat, Nat.add(v(U32.and(l, 1)), WD.sc(1n, hp)), Nat.add(WD.sc(1n, hp), v(U32.and(l, 1))), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), NA.add_comm(v(U32.and(l, 1)), WD.sc(1n, hp)), M.cong_l(WD.sc(1n, hp), Nat.mul(hp, 2n), v(U32.and(l, 1)), Equal.trans(Nat, Nat.double(hp), Nat.mul(2n, hp), Nat.mul(hp, 2n), NA.double_mul(hp), NA.mul_comm(2n, hp)))))
  Equal.sym(Nat, Nat.mod(v(l), 2n), v(U32.and(l, 1)), Equal.trans(Nat, Nat.mod(v(l), 2n), Nat.mod(Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), 2n), v(U32.and(l, 1)), M.cong_mod(2n, v(l), Nat.add(Nat.mul(hp, 2n), v(U32.and(l, 1))), e1), NR.mod_of(hp, 1n, v(U32.and(l, 1)), b2)))

# the value mod 2 is the low limb mod 2

def hlf_half(+n: Nat) -> {UH.hlf(n) == C.half(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+q:
      Equal.cong(Nat, Nat, z => 1n+z, UH.hlf(q), C.half(q), hlf_half(q))

# high(p, half(n)) == half(high(p, n)): both halve p + 1 times

def high_half(+p: Nat, +n: Nat) -> {C.high(p, C.half(n)) == C.half(C.high(p, n)) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      high_half(q, C.half(n))

# the value of a shift right: high(k, x), for every k

def shrn_high(+x: U32, +k: Nat) -> {v(U32.shrn(x, k)) == C.high(k, v(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +e1 = Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), UH.hlf(v(U32.shrn(x, p))), C.half(v(U32.shrn(x, p))), UH.shr_value(U32.shrn(x, p)), hlf_half(v(U32.shrn(x, p))))
      +e2 = Equal.cong(Nat, Nat, z => C.half(z), v(U32.shrn(x, p)), C.high(p, v(x)), shrn_high(x, p))
      Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), C.half(C.high(p, v(x))), C.high(1n+p, v(x)), Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), C.half(v(U32.shrn(x, p))), C.half(C.high(p, v(x))), e1, e2), Equal.sym(Nat, C.high(1n+p, v(x)), C.half(C.high(p, v(x))), high_half(p, v(x))))

# the 2^k table is the word with bit k set

def add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  +l1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(c, b)) == True{} : Bool}, Nat.add(c, a), Nat.add(a, c), N.add_comm(c, a), N.le_add_left(a, b, c, h1))
  +l2 = L.subst(Nat, z => {Nat.is_le(Nat.add(a, c), z) == True{} : Bool}, Nat.add(c, b), Nat.add(b, c), N.add_comm(c, b), l1)
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), l2, N.le_add_left(c, d, b, h2))

# masking never exceeds the mask

def bit_and_le(+a: Bool, +b: Bool) -> {Nat.is_le(S.bit_value(Bool.and(a, b)), S.bit_value(b)) == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def and_le(+n: Nat, +x: Word(n), +m: Word(n)) -> {Nat.is_le(WD.uw(n, Word.and(n, x, m)), WD.uw(n, m)) == True{} : Bool}:
  match n x m:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{a, t1} WCon{b, t2}:
      add_le(S.bit_value(Bool.and(a, b)), S.bit_value(b), Nat.double(WD.uw(p, Word.and(p, t1, t2))), Nat.double(WD.uw(p, t2)), bit_and_le(a, b), N.double_le(WD.uw(p, Word.and(p, t1, t2)), WD.uw(p, t2), and_le(p, t1, t2)))

def and_le32(+x: U32, +m: U32) -> {Nat.is_le(UD.v(U32.and(x, m)), UD.v(m)) == True{} : Bool}:
  match x m:
    case U32{+a} U32{+b}:
      %Equal.sym(Nat, UD.v(U32{Word.and(32n, a, b)}), WD.uw(32n, Word.and(32n, a, b)), UD.vw(Word.and(32n, a, b))) : {Nat.is_le(_, UD.v(U32{b})) == True{} : Bool}
      %Equal.sym(Nat, UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)) : {Nat.is_le(WD.uw(32n, Word.and(32n, a, b)), _) == True{} : Bool}
      and_le(32n, a, b)

# THEOREM: a bucket never exceeds the mask.
