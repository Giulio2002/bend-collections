import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ./nl.bend as NL
import ./pw.bend as PW
import ./pass.bend as PS

# The radix conversions of src/crypto/curve25519/limbs.bend through bit
# lists (least significant first): bits(w, x) is x for x < 2^w, a list of
# w-bit limbs flattens to its value, and grouping bits w at a time gives
# limbs of that value. Hence to_bytes_l (17-bit limbs to bytes) and
# of_bytes_l (bytes to 17-bit limbs, bit 255 dropped) keep the value.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# the value of a bit list
def bv(bs: List<&2, Nat>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, bt}:
      Nat.add(b, Nat.double(bv(bt)))

# the value of w-bit limbs
def lvw(+w: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      Nat.add(x, WD.sc(w, lvw(w, xt)))

def lvw17(+xs: List<&2, Nat>) -> {lvw(17n, xs) == FV.lv(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(x, WD.sc(17n, lvw(17n, xt)), C.shift(17n, FV.lv(xt)), M.cong_sc(17n, lvw(17n, xt), FV.lv(xt), lvw17(xt)))

def lvw8(+bs: List<&2, U32>) -> {lvw(8n, LS.nat_of(bs)) == FS.value(bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(U32.to_nat(x), WD.sc(8n, lvw(8n, LS.nat_of(xt))), C.shift(8n, FS.value(xt)), M.cong_sc(8n, lvw(8n, LS.nat_of(xt)), FS.value(xt), lvw8(xt)))

def sc_zero(+k: Nat) -> {WD.sc(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => Nat.double(t), WD.sc(m, 0n), 0n, sc_zero(m))

def dbl_sc(+x: Nat) -> {Nat.double(x) == WD.sc(1n, x) : Nat}:
  {==}

# ---- bits of a number ----

# x < 2 (2^m one) -> x div 2 < 2^m one
def half_lt(+x: Nat, +S: Nat, +h: {Nat.is_lt(x, Nat.double(S)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(x, 2n), S) == True{} : Bool}:
  +e0 = NR.le_div(1n, S, x)
  +h2 = L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, Nat.double(S), Nat.mul(S, 2n), tr(Nat.double(S), Nat.add(S, S), Nat.mul(S, 2n), NA.double_self(S), tr(Nat.add(S, S), Nat.add(S, Nat.mul(S, 1n)), Nat.mul(S, 2n), M.cong_r(S, S, Nat.mul(S, 1n), sy(Nat.mul(S, 1n), S, NA.mul_one(S))), sy(Nat.mul(S, 2n), Nat.add(S, Nat.mul(S, 1n)), NA.mul_succ(S, 1n)))), h)
  N.not_le_lt(S, Nat.div(x, 2n), Equal.trans(Bool, Nat.is_le(S, Nat.div(x, 2n)), Nat.is_le(Nat.mul(S, 2n), x), False{}, e0, N.lt_not_le(x, Nat.mul(S, 2n), h2)))

# x mod 2 + double(x div 2) == x
def dm2(+x: Nat) -> {Nat.add(Nat.mod(x, 2n), Nat.double(Nat.div(x, 2n))) == x : Nat}:
  +q = Nat.div(x, 2n)
  +r = Nat.mod(x, 2n)
  +e0 = NR.dm_eq(1n, x)
  +e1 = tr(Nat.double(q), Nat.add(q, q), Nat.mul(q, 2n), NA.double_self(q), tr(Nat.add(q, q), Nat.add(q, Nat.mul(q, 1n)), Nat.mul(q, 2n), M.cong_r(q, q, Nat.mul(q, 1n), sy(Nat.mul(q, 1n), q, NA.mul_one(q))), sy(Nat.mul(q, 2n), Nat.add(q, Nat.mul(q, 1n)), NA.mul_succ(q, 1n))))
  tr(Nat.add(r, Nat.double(q)), Nat.add(Nat.mul(q, 2n), r), x, tr(Nat.add(r, Nat.double(q)), Nat.add(r, Nat.mul(q, 2n)), Nat.add(Nat.mul(q, 2n), r), M.cong_r(r, Nat.double(q), Nat.mul(q, 2n), e1), NA.add_comm(r, Nat.mul(q, 2n))), sy(x, Nat.add(Nat.mul(q, 2n), r), e0))

def lt_one_zero(+x: Nat, +h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      Empty.absurd({1n+y == 0n : Nat}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(y, 0n), True{}, Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, N.not_lt_zero(y)), h)))

# bits(w, x) is x for x < 2^w
def bits_val(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +x: Nat, +h: {Nat.is_lt(x, WD.sc(w, one)) == True{} : Bool}) -> {bv(LS.bits(w, x)) == x : Nat}:
  match w:
    case 0n:
      sy(x, 0n, lt_one_zero(x, L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, one, 1n, h1, h)))
    case 1n+ +m:
      +q = Nat.div(x, 2n)
      +ih = bits_val(one, h1, m, q, half_lt(x, WD.sc(m, one), h))
      tr(Nat.add(Nat.mod(x, 2n), Nat.double(bv(LS.bits(m, q)))), Nat.add(Nat.mod(x, 2n), Nat.double(q)), x, M.cong_r(Nat.mod(x, 2n), Nat.double(bv(LS.bits(m, q))), Nat.double(q), Equal.cong(Nat, Nat, t => Nat.double(t), bv(LS.bits(m, q)), q, ih)), dm2(x))

def bits_len(+w: Nat, +x: Nat) -> {PS.ln(LS.bits(w, x)) == w : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.bits(m, Nat.div(x, 2n))), m, bits_len(m, Nat.div(x, 2n)))

def app_val(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {bv(LS.app(a, b)) == Nat.add(bv(a), WD.sc(PS.ln(a), bv(b))) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +B = WD.sc(PS.ln(xt), bv(b))
      +e1 = M.cong_r(x, Nat.double(bv(LS.app(xt, b))), Nat.double(Nat.add(bv(xt), B)), Equal.cong(Nat, Nat, t => Nat.double(t), bv(LS.app(xt, b)), Nat.add(bv(xt), B), app_val(xt, b)))
      +e2 = M.cong_r(x, Nat.double(Nat.add(bv(xt), B)), Nat.add(Nat.double(bv(xt)), Nat.double(B)), NA.double_add(bv(xt), B))
      tr(Nat.add(x, Nat.double(bv(LS.app(xt, b)))), Nat.add(x, Nat.double(Nat.add(bv(xt), B))), Nat.add(Nat.add(x, Nat.double(bv(xt))), Nat.double(B)), e1, tr(Nat.add(x, Nat.double(Nat.add(bv(xt), B))), Nat.add(x, Nat.add(Nat.double(bv(xt)), Nat.double(B))), Nat.add(Nat.add(x, Nat.double(bv(xt))), Nat.double(B)), e2, sy(Nat.add(Nat.add(x, Nat.double(bv(xt))), Nat.double(B)), Nat.add(x, Nat.add(Nat.double(bv(xt)), Nat.double(B))), NA.add_assoc(x, Nat.double(bv(xt)), Nat.double(B)))))

# w-bit limbs flatten to their value
def bits_all_val(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +xs: List<&2, Nat>, +h: {FV.below(xs, WD.sc(w, one)) == True{} : Bool}) -> {bv(LS.bits_all(w, xs)) == lvw(w, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +e1 = app_val(LS.bits(w, x), LS.bits_all(w, xt))
      +e2 = M.cong_add(bv(LS.bits(w, x)), x, WD.sc(PS.ln(LS.bits(w, x)), bv(LS.bits_all(w, xt))), WD.sc(w, lvw(w, xt)), bits_val(one, h1, w, x, NL.below_head(x, xt, WD.sc(w, one), h)), tr(WD.sc(PS.ln(LS.bits(w, x)), bv(LS.bits_all(w, xt))), WD.sc(w, bv(LS.bits_all(w, xt))), WD.sc(w, lvw(w, xt)), Equal.cong(Nat, Nat, t => WD.sc(t, bv(LS.bits_all(w, xt))), PS.ln(LS.bits(w, x)), w, bits_len(w, x)), M.cong_sc(w, bv(LS.bits_all(w, xt)), lvw(w, xt), bits_all_val(one, h1, w, xt, NL.below_tail(x, xt, WD.sc(w, one), h)))))
      tr(bv(LS.app(LS.bits(w, x), LS.bits_all(w, xt))), Nat.add(bv(LS.bits(w, x)), WD.sc(PS.ln(LS.bits(w, x)), bv(LS.bits_all(w, xt)))), Nat.add(x, WD.sc(w, lvw(w, xt))), e1, e2)

# ---- grouping ----

# bs == unbits(w, bs) + 2^w bits(drop(w, bs))
def split_val(+w: Nat, +bs: List<&2, Nat>) -> {bv(bs) == Nat.add(LS.unbits(w, bs), WD.sc(w, bv(LS.drop(w, bs)))) : Nat}:
  match w bs:
    case 0n _:
      {==}
    case 1n+ +m Nil{}:
      sy(WD.sc(1n+m, 0n), 0n, sc_zero(1n+m))
    case 1n+ +m Con{+b, +bt}:
      +U = LS.unbits(m, bt)
      +D = WD.sc(m, bv(LS.drop(m, bt)))
      +e1 = M.cong_r(b, Nat.double(bv(bt)), Nat.double(Nat.add(U, D)), Equal.cong(Nat, Nat, t => Nat.double(t), bv(bt), Nat.add(U, D), split_val(m, bt)))
      +e2 = M.cong_r(b, Nat.double(Nat.add(U, D)), Nat.add(Nat.double(U), Nat.double(D)), NA.double_add(U, D))
      tr(Nat.add(b, Nat.double(bv(bt))), Nat.add(b, Nat.double(Nat.add(U, D))), Nat.add(Nat.add(b, Nat.double(U)), Nat.double(D)), e1, tr(Nat.add(b, Nat.double(Nat.add(U, D))), Nat.add(b, Nat.add(Nat.double(U), Nat.double(D))), Nat.add(Nat.add(b, Nat.double(U)), Nat.double(D)), e2, sy(Nat.add(Nat.add(b, Nat.double(U)), Nat.double(D)), Nat.add(b, Nat.add(Nat.double(U), Nat.double(D))), NA.add_assoc(b, Nat.double(U), Nat.double(D)))))

# the bits fit n groups of w
def fits(+w: Nat, n: Nat, bs: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      match bs:
        case Nil{}:
          True{}
        case Con{b, bt}:
          False{}
    case 1n+m:
      fits(w, m, LS.drop(w, bs))

def group_val(+w: Nat, +n: Nat, +bs: List<&2, Nat>, +h: {fits(w, n, bs) == True{} : Bool}) -> {lvw(w, LS.group(w, n, bs)) == bv(bs) : Nat}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{b, bt}:
      Empty.absurd({0n == bv(Con{b, bt}) : Nat}, L.false_true(h))
    case 1n+ +m _:
      +ih = group_val(w, m, LS.drop(w, bs), h)
      tr(Nat.add(LS.unbits(w, bs), WD.sc(w, lvw(w, LS.group(w, m, LS.drop(w, bs))))), Nat.add(LS.unbits(w, bs), WD.sc(w, bv(LS.drop(w, bs)))), bv(bs), M.cong_r(LS.unbits(w, bs), WD.sc(w, lvw(w, LS.group(w, m, LS.drop(w, bs)))), WD.sc(w, bv(LS.drop(w, bs))), M.cong_sc(w, lvw(w, LS.group(w, m, LS.drop(w, bs))), bv(LS.drop(w, bs)), ih)), sy(bv(bs), Nat.add(LS.unbits(w, bs), WD.sc(w, bv(LS.drop(w, bs)))), split_val(w, bs)))

# ---- bit bounds ----

# every entry below 2 (a bit list)
def bits_lt(+w: Nat, +x: Nat) -> {FV.below(LS.bits(w, x), 2n) == True{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+ +m:
      NL.below_con(Nat.mod(x, 2n), LS.bits(m, Nat.div(x, 2n)), 2n, NR.dm_lt(1n, x), bits_lt(m, Nat.div(x, 2n)))

def app_below(+a: List<&2, Nat>, +b: List<&2, Nat>, +k: Nat, +ha: {FV.below(a, k) == True{} : Bool}, +hb: {FV.below(b, k) == True{} : Bool}) -> {FV.below(LS.app(a, b), k) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +xt}:
      NL.below_con(x, LS.app(xt, b), k, NL.below_head(x, xt, k, ha), app_below(xt, b, k, NL.below_tail(x, xt, k, ha), hb))

def bits_all_lt(+w: Nat, +xs: List<&2, Nat>) -> {FV.below(LS.bits_all(w, xs), 2n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      app_below(LS.bits(w, x), LS.bits_all(w, xt), 2n, bits_lt(w, x), bits_all_lt(w, xt))

def drop_lt2(+n: Nat, +bs: List<&2, Nat>, +h: {FV.below(bs, 2n) == True{} : Bool}) -> {FV.below(LS.drop(n, bs), 2n) == True{} : Bool}:
  NL.drop_below(n, bs, 2n, h)

# unbits(w, bs) < 2^w for a bit list
def unbits_lt(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +bs: List<&2, Nat>, +h: {FV.below(bs, 2n) == True{} : Bool}) -> {Nat.is_lt(LS.unbits(w, bs), WD.sc(w, one)) == True{} : Bool}:
  match w bs:
    case 0n _:
      L.subst(Nat, o => {Nat.is_lt(0n, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
    case 1n+ +m Nil{}:
      PW.sc_pos(1n+m, one, h1)
    case 1n+ +m Con{+b, +bt}:
      +u = LS.unbits(m, bt)
      +S = WD.sc(m, one)
      +ih = unbits_lt(one, h1, m, bt, NL.below_tail(b, bt, 2n, h))
      +hb = N.lt_succ_le(b, 1n, NL.below_head(b, bt, 2n, h))
      +a1 = M.le_add_r(b, 1n, Nat.double(u), hb)
      +a2 = N.le_lt_trans(Nat.add(b, Nat.double(u)), Nat.add(1n, Nat.double(u)), Nat.double(1n+u), a1, N.lt_succ(1n+Nat.double(u)))
      N.lt_le_trans(Nat.add(b, Nat.double(u)), Nat.double(1n+u), Nat.double(S), a2, N.double_le(1n+u, S, N.lt_succ_le_succ(u, S, ih)))

# ---- lengths ----

def app_len(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {PS.ln(LS.app(a, b)) == Nat.add(PS.ln(a), PS.ln(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.app(xt, b)), Nat.add(PS.ln(xt), PS.ln(b)), app_len(xt, b))

def take_len(+n: Nat, +bs: List<&2, Nat>) -> {Nat.is_le(PS.ln(LS.take(n, bs)), n) == True{} : Bool}:
  match n bs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+b, +bt}:
      take_len(m, bt)

# len(drop(w, bs)) <= k when len(bs) <= w + k
def drop_len_le(+w: Nat, +k: Nat, +bs: List<&2, Nat>, +h: {Nat.is_le(PS.ln(bs), Nat.add(w, k)) == True{} : Bool}) -> {Nat.is_le(PS.ln(LS.drop(w, bs)), k) == True{} : Bool}:
  match w bs:
    case 0n _:
      h
    case 1n+m Nil{}:
      N.zero_le(k)
    case 1n+ +m Con{+b, +bt}:
      drop_len_le(m, k, bt, h)

# at most w n bits fit n groups of w
def fits_len(+w: Nat, +n: Nat, +bs: List<&2, Nat>, +h: {Nat.is_le(PS.ln(bs), Nat.mul(n, w)) == True{} : Bool}) -> {fits(w, n, bs) == True{} : Bool}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{b, bt}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case 1n+ +m _:
      fits_len(w, m, LS.drop(w, bs), drop_len_le(w, Nat.mul(m, w), bs, h))

