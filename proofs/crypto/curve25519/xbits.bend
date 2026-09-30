import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as S
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/lemmas/spec/numeric.bend as SN
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/typed/width.bend as WI
import ../../math/typed/shrn.bend as SR
import ../../math/hash/hash.bend as HH
import ./num.bend as M
import ./limbs.bend as LM
import ./canon.bend as CN

# The byte-level pieces of X25519 (src/crypto/curve25519/x25519.bend against
# spec/crypto/curve25519/x25519.bend): scalar bits, clamping, the bit
# count, the swap bit, and the 32-byte encoding.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- bits of the scalar ----

def high_zero(+t: Nat) -> {C.high(t, 0n) == 0n : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+ +q:
      high_zero(q)

# bit t (t < 8) of b + 2^8 V is bit t of b
def low_bit(+t: Nat, +b: U32, +w: Nat) -> {v(U32.and(U32.shrn(b, t), 1)) == C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))) : Nat}:
  +e1 = CN.and1(1n, {==}, U32.shrn(b, t))
  +e2 = Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), v(U32.shrn(b, t)), C.high(t, v(b)), SR.shrn_high(b, t))
  +e3 = Equal.sym(Nat, C.bit(C.high(t, v(b))), Nat.mod(C.high(t, v(b)), 2n), WI.bit_mod(C.high(t, v(b))))
  +e4 = Equal.cong(Nat, Nat, z => C.bit(z), C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w)))), Nat.add(C.high(t, v(b)), Nat.double(w)), WI.high_add_shift(t, v(b), Nat.double(w)))
  +e5 = WI.bit_dbl(C.high(t, v(b)), w)
  Equal.trans(Nat, v(U32.and(U32.shrn(b, t), 1)), Nat.mod(v(U32.shrn(b, t)), 2n), C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))), e1, Equal.trans(Nat, Nat.mod(v(U32.shrn(b, t)), 2n), Nat.mod(C.high(t, v(b)), 2n), C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))), e2, Equal.trans(Nat, Nat.mod(C.high(t, v(b)), 2n), C.bit(C.high(t, v(b))), C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))), e3, Equal.sym(Nat, C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))), C.bit(C.high(t, v(b))), Equal.trans(Nat, C.bit(C.high(t, Nat.add(v(b), C.shift(t, Nat.double(w))))), C.bit(Nat.add(C.high(t, v(b)), Nat.double(w))), C.bit(C.high(t, v(b))), e4, e5)))))

# X.kbit(bs, t) is bit t of the value of the bytes
def kbit_val(+bs: List<&2, U32>, +t: Nat, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {v(X.kbit(bs, t)) == S.kbit(FS.value(bs), t) : Nat}:
  match bs t:
    case Nil{} _:
      Equal.cong(Nat, Nat, z => C.bit(z), 0n, C.high(t, 0n), Equal.sym(Nat, C.high(t, 0n), 0n, high_zero(t)))
    case Con{+b, +bt} 0n:
      low_bit(0n, b, C.shift(7n, FS.value(bt)))
    case Con{+b, +bt} 1n:
      low_bit(1n, b, C.shift(6n, FS.value(bt)))
    case Con{+b, +bt} 2n:
      low_bit(2n, b, C.shift(5n, FS.value(bt)))
    case Con{+b, +bt} 3n:
      low_bit(3n, b, C.shift(4n, FS.value(bt)))
    case Con{+b, +bt} 4n:
      low_bit(4n, b, C.shift(3n, FS.value(bt)))
    case Con{+b, +bt} 5n:
      low_bit(5n, b, C.shift(2n, FS.value(bt)))
    case Con{+b, +bt} 6n:
      low_bit(6n, b, C.shift(1n, FS.value(bt)))
    case Con{+b, +bt} 7n:
      low_bit(7n, b, FS.value(bt))
    case Con{+b, +bt} 8n+ +q:
      +V = FS.value(bt)
      +hbl = N.le_lt_succ(v(b), 255n, LM.lea_head(b, bt, 255n, hb))
      +e1 = WI.high_comp(q, 8n, Nat.add(v(b), C.shift(8n, V)))
      +e2 = Equal.cong(Nat, Nat, z => C.high(q, z), C.high(8n, Nat.add(v(b), C.shift(8n, V))), V, WI.high_uniq(8n, v(b), V, hbl))
      +e3 = Equal.cong(Nat, Nat, z => C.bit(z), C.high(Nat.add(8n, q), Nat.add(v(b), C.shift(8n, V))), C.high(q, V), Equal.trans(Nat, C.high(Nat.add(8n, q), Nat.add(v(b), C.shift(8n, V))), C.high(q, C.high(8n, Nat.add(v(b), C.shift(8n, V)))), C.high(q, V), e1, e2))
      Equal.trans(Nat, v(X.kbit(bt, q)), C.bit(C.high(q, V)), C.bit(C.high(Nat.add(8n, q), Nat.add(v(b), C.shift(8n, V)))), kbit_val(bt, q, LM.lea_tail(b, bt, 255n, hb)), Equal.sym(Nat, C.bit(C.high(Nat.add(8n, q), Nat.add(v(b), C.shift(8n, V)))), C.bit(C.high(q, V)), e3))

def kbit_le(+bs: List<&2, U32>, +t: Nat, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {Nat.is_le(S.kbit(FS.value(bs), t), 1n) == True{} : Bool}:
  WI.bit_le1(C.high(t, FS.value(bs)))

# ---- clamping, the bit count ----

def clamp_top_eq(+xs: List<&2, U32>) -> {X.clamp_top(xs) == S.clamp_last(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, X.clamp_top(Con{y, yt}), S.clamp_last(Con{y, yt}), clamp_top_eq(Con{y, yt}))

def clamp_eq(+bs: List<&2, U32>) -> {X.clamp(bs) == S.clamp(bs) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      clamp_top_eq(Con{U32.and(b, 248), bt})

def len_eq(+bs: List<&2, U32>) -> {X.len(bs) == C.length(U32, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      Equal.cong(Nat, Nat, z => 1n+z, X.len(bt), C.length(U32, bt), len_eq(bt))

def nbits_eq(+k: List<&2, U32>) -> {X.nbits(k) == S.bits(k) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.sub(Nat.mul(8n, z), 1n), X.len(k), C.length(U32, k), len_eq(k))

# or never exceeds the sum
def bit_or_le(+a: Bool, +b: Bool) -> {Nat.is_le(SN.bit_value(Bool.or(a, b)), Nat.add(SN.bit_value(a), SN.bit_value(b))) == True{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or_le(+n: Nat, +x: Word(n), +m: Word(n)) -> {Nat.is_le(WD.uw(n, Word.or(n, x, m)), Nat.add(WD.uw(n, x), WD.uw(n, m))) == True{} : Bool}:
  match n x m:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+ +p WCon{+a, +t1} WCon{+b, +t2}:
      +u1 = WD.uw(p, t1)
      +u2 = WD.uw(p, t2)
      +d1 = N.double_le(WD.uw(p, Word.or(p, t1, t2)), Nat.add(u1, u2), or_le(p, t1, t2))
      +d2 = L.subst(Nat, z => {Nat.is_le(Nat.double(WD.uw(p, Word.or(p, t1, t2))), z) == True{} : Bool}, Nat.double(Nat.add(u1, u2)), Nat.add(Nat.double(u1), Nat.double(u2)), NA.double_add(u1, u2), d1)
      +s = M.le_add2(SN.bit_value(Bool.or(a, b)), Nat.double(WD.uw(p, Word.or(p, t1, t2))), Nat.add(SN.bit_value(a), SN.bit_value(b)), Nat.add(Nat.double(u1), Nat.double(u2)), bit_or_le(a, b), d2)
      L.subst(Nat, z => {Nat.is_le(Nat.add(SN.bit_value(Bool.or(a, b)), Nat.double(WD.uw(p, Word.or(p, t1, t2)))), z) == True{} : Bool}, Nat.add(Nat.add(SN.bit_value(a), SN.bit_value(b)), Nat.add(Nat.double(u1), Nat.double(u2))), Nat.add(Nat.add(SN.bit_value(a), Nat.double(u1)), Nat.add(SN.bit_value(b), Nat.double(u2))), M.add4(SN.bit_value(a), SN.bit_value(b), Nat.double(u1), Nat.double(u2)), s)

def or_le32(+x: U32, +m: U32) -> {Nat.is_le(v(U32.or(x, m)), Nat.add(v(x), v(m))) == True{} : Bool}:
  match x m:
    case U32{+a} U32{+b}:
      %Equal.sym(Nat, UD.v(U32{Word.or(32n, a, b)}), WD.uw(32n, Word.or(32n, a, b)), UD.vw(Word.or(32n, a, b))) : {Nat.is_le(_, Nat.add(v(U32{a}), v(U32{b}))) == True{} : Bool}
      %Equal.sym(Nat, UD.v(U32{a}), WD.uw(32n, a), UD.vw(a)) : {Nat.is_le(WD.uw(32n, Word.or(32n, a, b)), Nat.add(_, v(U32{b}))) == True{} : Bool}
      %Equal.sym(Nat, UD.v(U32{b}), WD.uw(32n, b), UD.vw(b)) : {Nat.is_le(WD.uw(32n, Word.or(32n, a, b)), Nat.add(WD.uw(32n, a), _)) == True{} : Bool}
      or_le(32n, a, b)

def clamp_top_okb(+n: Nat, +xs: List<&2, U32>, +e: {LM.okb(1n+n, xs, 255n) == True{} : Bool}) -> {LM.okb(1n+n, X.clamp_top(xs), 255n) == True{} : Bool}:
  match n xs:
    case _ Nil{}:
      Empty.absurd({LM.okb(1n+n, Nil{}, 255n) == True{} : Bool}, L.false_true(e))
    case 0n Con{+x, Nil{}}:
      +a = HH.and_le32(x, 127)
      +o = or_le32(U32.and(x, 127), 64)
      +b = N.le_trans(v(U32.or(U32.and(x, 127), 64)), Nat.add(v(U32.and(x, 127)), 64n), 255n, o, N.le_trans(Nat.add(v(U32.and(x, 127)), 64n), Nat.add(127n, 64n), 255n, M.le_add_r(v(U32.and(x, 127)), 127n, 64n, a), {==}))
      L.and_intro(Nat.is_le(v(U32.or(U32.and(x, 127), 64)), 255n), True{}, b, {==})
    case 0n Con{x, Con{y, yt}}:
      Empty.absurd({LM.okb(1n, X.clamp_top(Con{x, Con{y, yt}}), 255n) == True{} : Bool}, L.false_true(LM.okb_tail(0n, x, Con{y, yt}, 255n, e)))
    case 1n+m Con{x, Nil{}}:
      Empty.absurd({LM.okb(2n+m, X.clamp_top(Con{x, Nil{}}), 255n) == True{} : Bool}, L.false_true(LM.okb_tail(1n+m, x, Nil{}, 255n, e)))
    case 1n+ +m Con{+x, Con{+y, +yt}}:
      L.and_intro(Nat.is_le(v(x), 255n), LM.okb(1n+m, X.clamp_top(Con{y, yt}), 255n), LM.okb_head(1n+m, x, Con{y, yt}, 255n, e), clamp_top_okb(m, Con{y, yt}, LM.okb_tail(1n+m, x, Con{y, yt}, 255n, e)))

def clamp_okb(+k: List<&2, U32>, +e: {LM.okb(32n, k, 255n) == True{} : Bool}) -> {LM.okb(32n, X.clamp(k), 255n) == True{} : Bool}:
  match k:
    case Nil{}:
      Empty.absurd({LM.okb(32n, Nil{}, 255n) == True{} : Bool}, L.false_true(e))
    case Con{+b, +bt}:
      +ha = N.le_trans(v(U32.and(b, 248)), 248n, 255n, HH.and_le32(b, 248), {==})
      clamp_top_okb(31n, Con{U32.and(b, 248), bt}, L.and_intro(Nat.is_le(v(U32.and(b, 248)), 255n), LM.okb(31n, bt, 255n), ha, LM.okb_tail(31n, b, bt, 255n, e)))

# ---- the swap bit ----

def u0(+a: U32, +e: {v(a) == 0n : Nat}) -> {a == 0 : U32}:
  U.injective(a, 0, e)

def u1(+a: U32, +e: {v(a) == 1n : Nat}) -> {a == 1 : U32}:
  U.injective(a, 1, e)

# swap ^= k_t on bits
def xor_bits(+a: U32, +b: U32, +na: Nat, +nb: Nat, +ea: {v(a) == na : Nat}, +eb: {v(b) == nb : Nat}, +ha: {Nat.is_le(na, 1n) == True{} : Bool}, +hb: {Nat.is_le(nb, 1n) == True{} : Bool}) -> {v(U32.xor(a, b)) == S.bxor(na, nb) : Nat}:
  match na nb:
    case 0n 0n:
      %Equal.sym(U32, a, 0, u0(a, ea)) : {v(U32.xor(_, b)) == 0n : Nat}
      %Equal.sym(U32, b, 0, u0(b, eb)) : {v(U32.xor(0, _)) == 0n : Nat}
      {==}
    case 0n 1n:
      %Equal.sym(U32, a, 0, u0(a, ea)) : {v(U32.xor(_, b)) == 1n : Nat}
      %Equal.sym(U32, b, 1, u1(b, eb)) : {v(U32.xor(0, _)) == 1n : Nat}
      {==}
    case 1n 0n:
      %Equal.sym(U32, a, 1, u1(a, ea)) : {v(U32.xor(_, b)) == 1n : Nat}
      %Equal.sym(U32, b, 0, u0(b, eb)) : {v(U32.xor(1, _)) == 1n : Nat}
      {==}
    case 1n 1n:
      %Equal.sym(U32, a, 1, u1(a, ea)) : {v(U32.xor(_, b)) == 0n : Nat}
      %Equal.sym(U32, b, 1, u1(b, eb)) : {v(U32.xor(1, _)) == 0n : Nat}
      {==}
    case 2n+q _:
      Empty.absurd({v(U32.xor(a, b)) == S.bxor(2n+q, nb) : Nat}, L.false_true(ha))
    case _ 2n+q:
      Empty.absurd({v(U32.xor(a, b)) == S.bxor(na, 2n+q) : Nat}, L.false_true(hb))

def bxor_le(+a: Nat, +b: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.is_le(S.bxor(a, b), 1n) == True{} : Bool}:
  match a:
    case 0n:
      hb
    case 1n+q:
      AR.sub_le2(1n, b)

# ---- the encoding ----

def byte_rt(+y: U32, +hy: {Nat.is_le(v(y), 255n) == True{} : Bool}) -> {U32.from_nat(v(y)) == y : U32}:
  U.injective(U32.from_nat(v(y)), y, U.to_nat_from_nat(v(y), 8n, {==}, N.le_lt_succ(v(y), 255n, hy)))

# n tight bytes are the little-endian encoding of their value
def bytes_le(+n: Nat, +ys: List<&2, U32>, +e: {LM.okb(n, ys, 255n) == True{} : Bool}) -> {S.le_bytes(n, FS.value(ys)) == ys : List<&2, U32>}:
  match n ys:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({Nil{} == Con{y, yt} : List<&2, U32>}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({S.le_bytes(1n+m, 0n) == Nil{} : List<&2, U32>}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      +V = FS.value(yt)
      +hy = LM.okb_head(m, y, yt, 255n, e)
      +hl = N.le_lt_succ(v(y), 255n, hy)
      +x = Nat.add(v(y), C.shift(8n, V))
      +ex = Equal.trans(Nat, x, Nat.add(C.shift(8n, V), v(y)), Nat.add(Nat.mul(V, 256n), v(y)), NA.add_comm(v(y), C.shift(8n, V)), M.cong_l(C.shift(8n, V), Nat.mul(V, 256n), v(y), Equal.sym(Nat, Nat.mul(V, 256n), C.shift(8n, V), LM.m256(V))))
      +em = Equal.trans(Nat, Nat.mod(x, 256n), Nat.mod(Nat.add(Nat.mul(V, 256n), v(y)), 256n), v(y), M.cong_mod(256n, x, Nat.add(Nat.mul(V, 256n), v(y)), ex), NR.mod_of(V, 255n, v(y), hl))
      +ed = Equal.trans(Nat, Nat.div(x, 256n), Nat.div(Nat.add(Nat.mul(V, 256n), v(y)), 256n), V, Equal.cong(Nat, Nat, z => Nat.div(z, 256n), x, Nat.add(Nat.mul(V, 256n), v(y)), ex), NR.div_of(V, 255n, v(y), hl))
      +e1 = Equal.trans(U32, U32.from_nat(Nat.mod(x, 256n)), U32.from_nat(v(y)), y, Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.mod(x, 256n), v(y), em), byte_rt(y, hy))
      +e2 = Equal.trans(List<&2, U32>, S.le_bytes(m, Nat.div(x, 256n)), S.le_bytes(m, V), yt, Equal.cong(Nat, List<&2, U32>, z => S.le_bytes(m, z), Nat.div(x, 256n), V, ed), bytes_le(m, yt, LM.okb_tail(m, y, yt, 255n, e)))
      Equal.trans(List<&2, U32>, Con{U32.from_nat(Nat.mod(x, 256n)), S.le_bytes(m, Nat.div(x, 256n))}, Con{y, S.le_bytes(m, Nat.div(x, 256n))}, Con{y, yt}, Equal.cong(U32, List<&2, U32>, z => Con{z, S.le_bytes(m, Nat.div(x, 256n))}, U32.from_nat(Nat.mod(x, 256n)), y, e1), Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{y, z}, S.le_bytes(m, Nat.div(x, 256n)), yt, e2))

# ---- decodeUCoordinate ----

def mask_eq(+xs: List<&2, U32>) -> {F.mask_top(xs) == S.mask_last(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match xt:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, F.mask_top(Con{y, yt}), S.mask_last(Con{y, yt}), mask_eq(Con{y, yt}))

def mask_okb(+n: Nat, +xs: List<&2, U32>, +e: {LM.okb(1n+n, xs, 255n) == True{} : Bool}) -> {LM.okb(1n+n, F.mask_top(xs), 255n) == True{} : Bool}:
  match n xs:
    case _ Nil{}:
      Empty.absurd({LM.okb(1n+n, Nil{}, 255n) == True{} : Bool}, L.false_true(e))
    case 0n Con{+x, Nil{}}:
      L.and_intro(Nat.is_le(v(U32.and(x, 127)), 255n), True{}, N.le_trans(v(U32.and(x, 127)), 127n, 255n, HH.and_le32(x, 127), {==}), {==})
    case 0n Con{x, Con{y, yt}}:
      Empty.absurd({LM.okb(1n, F.mask_top(Con{x, Con{y, yt}}), 255n) == True{} : Bool}, L.false_true(LM.okb_tail(0n, x, Con{y, yt}, 255n, e)))
    case 1n+m Con{x, Nil{}}:
      Empty.absurd({LM.okb(2n+m, F.mask_top(Con{x, Nil{}}), 255n) == True{} : Bool}, L.false_true(LM.okb_tail(1n+m, x, Nil{}, 255n, e)))
    case 1n+ +m Con{+x, Con{+y, +yt}}:
      L.and_intro(Nat.is_le(v(x), 255n), LM.okb(1n+m, F.mask_top(Con{y, yt}), 255n), LM.okb_head(1n+m, x, Con{y, yt}, 255n, e), mask_okb(m, Con{y, yt}, LM.okb_tail(1n+m, x, Con{y, yt}, 255n, e)))
