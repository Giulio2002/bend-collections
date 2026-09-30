import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../spec/crypto/curve25519/x25519.bend as S
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../fe/w32.bend as PD
import ./num.bend as M
import ../fe/pw.bend as PW
import ../fe/rel.bend as RE
import ../fe/conv.bend as CV

# Small lemmas of the X25519 proof that the Ed25519 proofs share: the
# constants (a24 and digits under the symbolic one), decodeUCoordinate's
# mask as the value mod 2^255, selection by a bit, small constants as
# elements of the fast field.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- constants ----

def digits_eq(+one: Nat, +ds: List<&2, Nat>) -> {X.digits(one, ds) == FS.digits(one, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +dt}:
      M.cong_r(Nat.mul(one, d), FE.pow2(8n, X.digits(one, dt)), C.shift(8n, FS.digits(one, dt)), Equal.cong(Nat, Nat, t => FE.pow2(8n, t), X.digits(one, dt), FS.digits(one, dt), digits_eq(one, dt)))

def a24_eq(+one: Nat) -> {X.a24(one) == S.a24(one) : Nat}:
  digits_eq(one, [65n, 219n, 1n])

# (a + b) + c == (a + c) + b
def CA_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  tr(Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b), NA.add_assoc(a, b, c), tr(Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), M.cong_r(a, Nat.add(b, c), Nat.add(c, b), NA.add_comm(b, c)), sy(Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), NA.add_assoc(a, c, b))))

# x < S -> x + one <= S
def succ_le(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +S: Nat, +h: {Nat.is_lt(x, S) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, one), S) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_le(Nat.add(x, o), S) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, t => {Nat.is_le(t, S) == True{} : Bool}, 1n+x, Nat.add(x, 1n), tr(1n+x, 1n+Nat.add(x, 0n), Nat.add(x, 1n), Equal.cong(Nat, Nat, t => 1n+t, x, Nat.add(x, 0n), sy(Nat.add(x, 0n), x, N.add_zero(x))), sy(Nat.add(x, 1n), 1n+Nat.add(x, 0n), N.add_succ(x, 0n))), N.lt_succ_le_succ(x, S, h)))

# one d < 2^8 for a digit d < 256
def dig_lt(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(one, d), WD.sc(8n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(Nat.mul(o, d), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, t => {Nat.is_lt(t, WD.sc(8n, 1n)) == True{} : Bool}, d, Nat.mul(1n, d), sy(Nat.mul(1n, d), d, AR.one_mul(d)), hd))

# a24 = 65 + 2^8 (219 + 2^8 1) < 2^17
def a24_lt(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(X.a24(one), WD.sc(17n, one)) == True{} : Bool}:
  +m0 = Nat.mul(one, 65n)
  +m1 = Nat.mul(one, 219n)
  +m2 = Nat.mul(one, 1n)
  +s8 = WD.sc(8n, one)
  +z = FE.pow2(8n, 0n)
  +e2 = tr(Nat.add(m2, z), m2, one, tr(Nat.add(m2, z), Nat.add(m2, 0n), m2, M.cong_r(m2, z, 0n, {==}), N.add_zero(m2)), NA.mul_one(one))
  +inner = Nat.add(m1, WD.sc(8n, Nat.add(m2, z)))
  +ei = M.cong_r(m1, WD.sc(8n, Nat.add(m2, z)), s8, M.cong_sc(8n, Nat.add(m2, z), one, e2))
  +l1 = L.subst(Nat, t => {Nat.is_le(Nat.add(t, one), WD.sc(9n, one)) == True{} : Bool}, Nat.add(m1, s8), inner, sy(inner, Nat.add(m1, s8), ei), L.subst(Nat, t => {Nat.is_le(t, WD.sc(9n, one)) == True{} : Bool}, Nat.add(Nat.add(m1, one), s8), Nat.add(Nat.add(m1, s8), one), CA_swap(m1, one, s8), PW.add_le_dbl(Nat.add(m1, one), s8, 8n, one, succ_le(one, h1, m1, s8, dig_lt(one, h1, 219n, {==})), N.le_refl(s8))))
  +l2 = L.subst(Nat, t => {Nat.is_le(t, WD.sc(17n, one)) == True{} : Bool}, WD.sc(8n, Nat.add(inner, one)), Nat.add(WD.sc(8n, inner), s8), sy(Nat.add(WD.sc(8n, inner), s8), WD.sc(8n, Nat.add(inner, one)), M.sc_add(8n, inner, one)), L.subst(Nat, t => {Nat.is_le(WD.sc(8n, Nat.add(inner, one)), t) == True{} : Bool}, WD.sc(8n, WD.sc(9n, one)), WD.sc(17n, one), M.sc_sc(8n, 9n, one), M.le_sc(8n, Nat.add(inner, one), WD.sc(9n, one), l1)))
  +l3 = N.lt_le_trans(Nat.add(m0, WD.sc(8n, inner)), Nat.add(s8, WD.sc(8n, inner)), WD.sc(17n, one), N.lt_add_r2(m0, s8, WD.sc(8n, inner), dig_lt(one, h1, 65n, {==})), L.subst(Nat, t => {Nat.is_le(t, WD.sc(17n, one)) == True{} : Bool}, Nat.add(WD.sc(8n, inner), s8), Nat.add(s8, WD.sc(8n, inner)), NA.add_comm(WD.sc(8n, inner), s8), l2))
  l3


# ---- decodeUCoordinate: masking bit 255 is the value mod 2^255 ----

def m7(n: Nat) -> Nat:
  match n:
    case 0n:
      7n
    case 1n+m:
      Nat.add(8n, m7(m))

# M = 1 + (M - 1) for a power of two
def pos_succ(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {1n+Nat.sub(WD.sc(k, one), 1n) == WD.sc(k, one) : Nat}:
  N.sub_add(WD.sc(k, one), 1n, N.lt_succ_le_succ(0n, WD.sc(k, one), PW.sc_pos(k, one, h1)))

# (q M + r) mod M == r for r < M = 2^k
def mod_pow(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +q: Nat, +r: Nat, +h: {Nat.is_lt(r, WD.sc(k, one)) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, WD.sc(k, one)), r), WD.sc(k, one)) == r : Nat}:
  +b = Nat.sub(WD.sc(k, one), 1n)
  +hb = pos_succ(one, h1, k)
  +h2 = L.subst(Nat, t => {Nat.is_lt(r, t) == True{} : Bool}, WD.sc(k, one), 1n+b, sy(1n+b, WD.sc(k, one), hb), h)
  L.subst(Nat, t => {Nat.mod(Nat.add(Nat.mul(q, t), r), t) == r : Nat}, 1n+b, WD.sc(k, one), hb, NR.mod_of(q, b, r, h2))

# x + 2^8 V == (x + 2^8 (V mod M)) + q 2^8 M, and the mod
def mod_shift(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +x: Nat, +V: Nat, +hx: {Nat.is_lt(x, WD.sc(8n, one)) == True{} : Bool}) -> {Nat.mod(Nat.add(x, WD.sc(8n, V)), WD.sc(8n, WD.sc(k, one))) == Nat.add(x, WD.sc(8n, Nat.mod(V, WD.sc(k, one)))) : Nat}:
  +Mo = WD.sc(k, one)
  +b = Nat.sub(Mo, 1n)
  +hb = pos_succ(one, h1, k)
  +q = Nat.div(V, Mo)
  +r = Nat.mod(V, Mo)
  +eV = L.subst(Nat, t => {V == Nat.add(Nat.mul(Nat.div(V, t), t), Nat.mod(V, t)) : Nat}, 1n+b, Mo, hb, NR.dm_eq(b, V))
  +hr = L.subst(Nat, t => {Nat.is_lt(Nat.mod(V, t), t) == True{} : Bool}, 1n+b, Mo, hb, NR.dm_lt(b, V))
  +S8M = WD.sc(8n, Mo)
  +e1 = tr(WD.sc(8n, V), WD.sc(8n, Nat.add(Nat.mul(q, Mo), r)), Nat.add(Nat.mul(q, S8M), WD.sc(8n, r)), M.cong_sc(8n, V, Nat.add(Nat.mul(q, Mo), r), eV), tr(WD.sc(8n, Nat.add(Nat.mul(q, Mo), r)), Nat.add(WD.sc(8n, Nat.mul(q, Mo)), WD.sc(8n, r)), Nat.add(Nat.mul(q, S8M), WD.sc(8n, r)), sy(Nat.add(WD.sc(8n, Nat.mul(q, Mo)), WD.sc(8n, r)), WD.sc(8n, Nat.add(Nat.mul(q, Mo), r)), M.sc_add(8n, Nat.mul(q, Mo), r)), M.cong_l(WD.sc(8n, Nat.mul(q, Mo)), Nat.mul(q, S8M), WD.sc(8n, r), tr(WD.sc(8n, Nat.mul(q, Mo)), Nat.mul(WD.sc(8n, Mo), q), Nat.mul(q, S8M), tr(WD.sc(8n, Nat.mul(q, Mo)), WD.sc(8n, Nat.mul(Mo, q)), Nat.mul(WD.sc(8n, Mo), q), M.cong_sc(8n, Nat.mul(q, Mo), Nat.mul(Mo, q), NA.mul_comm(q, Mo)), AR.sc_mul(8n, Mo, q)), NA.mul_comm(WD.sc(8n, Mo), q)))))
  +y = Nat.add(x, WD.sc(8n, r))
  +e2 = tr(Nat.add(x, WD.sc(8n, V)), Nat.add(x, Nat.add(Nat.mul(q, S8M), WD.sc(8n, r))), Nat.add(Nat.mul(q, S8M), y), M.cong_r(x, WD.sc(8n, V), Nat.add(Nat.mul(q, S8M), WD.sc(8n, r)), e1), NA.add_swap(x, Nat.mul(q, S8M), WD.sc(8n, r)))
  +ro = Nat.add(r, one)
  +hro = succ_le(one, h1, r, Mo, hr)
  +l1 = N.lt_le_trans(y, Nat.add(WD.sc(8n, one), WD.sc(8n, r)), WD.sc(8n, Mo), N.lt_add_r2(x, WD.sc(8n, one), WD.sc(8n, r), hx), L.subst(Nat, t => {Nat.is_le(t, WD.sc(8n, Mo)) == True{} : Bool}, WD.sc(8n, Nat.add(one, r)), Nat.add(WD.sc(8n, one), WD.sc(8n, r)), sy(Nat.add(WD.sc(8n, one), WD.sc(8n, r)), WD.sc(8n, Nat.add(one, r)), M.sc_add(8n, one, r)), M.le_sc(8n, Nat.add(one, r), Mo, L.subst(Nat, t => {Nat.is_le(t, Mo) == True{} : Bool}, ro, Nat.add(one, r), NA.add_comm(r, one), hro))))
  +S8M2 = WD.sc(Nat.add(8n, k), one)
  +eS = M.sc_sc(8n, k, one)
  +l2 = L.subst(Nat, t => {Nat.is_lt(y, t) == True{} : Bool}, S8M, S8M2, eS, l1)
  +e3 = L.subst(Nat, t => {Nat.mod(Nat.add(Nat.mul(q, t), y), t) == y : Nat}, S8M2, S8M, sy(S8M, S8M2, eS), mod_pow(one, h1, Nat.add(8n, k), q, y, l2))
  tr(Nat.mod(Nat.add(x, WD.sc(8n, V)), S8M), Nat.mod(Nat.add(Nat.mul(q, S8M), y), S8M), y, Equal.cong(Nat, Nat, t => Nat.mod(t, S8M), Nat.add(x, WD.sc(8n, V)), Nat.add(Nat.mul(q, S8M), y), e2), e3)

def mask_mod(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +hb: {FS.bytes_ok(1n+n, xs) == True{} : Bool}) -> {FS.value(S.mask_last(xs)) == Nat.mod(FS.value(xs), WD.sc(m7(n), one)) : Nat}:
  match n xs:
    case _ Nil{}:
      Empty.absurd({0n == Nat.mod(0n, WD.sc(m7(n), one)) : Nat}, L.false_true(hb))
    case 0n Con{+x, Nil{}}:
      +a = U32.and(x, 127)
      +M7 = WD.sc(7n, one)
      +hp = PD.hp32(7n, x)
      +e0 = PD.and32(7n, x, 127, {==})
      +hl = PD.and32_lt(7n, one, h1, x, 127, {==})
      +e1 = tr(v(x), Nat.add(v(a), WD.sc(7n, hp)), Nat.add(Nat.mul(hp, M7), v(a)), e0, tr(Nat.add(v(a), WD.sc(7n, hp)), Nat.add(WD.sc(7n, hp), v(a)), Nat.add(Nat.mul(hp, M7), v(a)), NA.add_comm(v(a), WD.sc(7n, hp)), M.cong_l(WD.sc(7n, hp), Nat.mul(hp, M7), v(a), sy(Nat.mul(hp, M7), WD.sc(7n, hp), AR.mul_sc1(7n, one, h1, hp)))))
      +e2 = tr(Nat.mod(v(x), M7), Nat.mod(Nat.add(Nat.mul(hp, M7), v(a)), M7), v(a), Equal.cong(Nat, Nat, t => Nat.mod(t, M7), v(x), Nat.add(Nat.mul(hp, M7), v(a)), e1), mod_pow(one, h1, 7n, hp, v(a), hl))
      tr(Nat.add(v(a), 0n), v(a), Nat.mod(Nat.add(v(x), 0n), M7), N.add_zero(v(a)), tr(v(a), Nat.mod(v(x), M7), Nat.mod(Nat.add(v(x), 0n), M7), sy(Nat.mod(v(x), M7), v(a), e2), Equal.cong(Nat, Nat, t => Nat.mod(t, M7), v(x), Nat.add(v(x), 0n), sy(Nat.add(v(x), 0n), v(x), N.add_zero(v(x))))))
    case 0n Con{x, Con{y, yt}}:
      Empty.absurd({FS.value(S.mask_last(Con{x, Con{y, yt}})) == Nat.mod(FS.value(Con{x, Con{y, yt}}), WD.sc(7n, one)) : Nat}, L.false_true(L.and_right(Nat.is_lt(v(x), 256n), FS.bytes_ok(0n, Con{y, yt}), hb)))
    case 1n+m Con{x, Nil{}}:
      Empty.absurd({FS.value(S.mask_last(Con{x, Nil{}})) == Nat.mod(FS.value(Con{x, Nil{}}), WD.sc(m7(1n+m), one)) : Nat}, L.false_true(L.and_right(Nat.is_lt(v(x), 256n), FS.bytes_ok(1n+m, Nil{}), hb)))
    case 1n+ +m Con{+x, Con{+y, +yt}}:
      +rest = {Con{y, yt} : List<&2, U32>}
      +hx = L.and_left(Nat.is_lt(v(x), 256n), FS.bytes_ok(1n+m, rest), hb)
      +hr = L.and_right(Nat.is_lt(v(x), 256n), FS.bytes_ok(1n+m, rest), hb)
      +hx8 = L.subst(Nat, o => {Nat.is_lt(v(x), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), hx)
      +ih = mask_mod(one, h1, m, rest, hr)
      +Mo = WD.sc(m7(m), one)
      +V = FS.value(rest)
      +e1 = M.cong_r(v(x), C.shift(8n, FS.value(S.mask_last(rest))), WD.sc(8n, Nat.mod(V, Mo)), M.cong_sc(8n, FS.value(S.mask_last(rest)), Nat.mod(V, Mo), ih))
      +e2 = sy(Nat.mod(Nat.add(v(x), WD.sc(8n, V)), WD.sc(8n, Mo)), Nat.add(v(x), WD.sc(8n, Nat.mod(V, Mo))), mod_shift(one, h1, m7(m), v(x), V, hx8))
      +e3 = Equal.cong(Nat, Nat, t => Nat.mod(Nat.add(v(x), WD.sc(8n, V)), t), WD.sc(8n, Mo), WD.sc(Nat.add(8n, m7(m)), one), M.sc_sc(8n, m7(m), one))
      tr(Nat.add(v(x), C.shift(8n, FS.value(S.mask_last(rest)))), Nat.add(v(x), WD.sc(8n, Nat.mod(V, Mo))), Nat.mod(Nat.add(v(x), C.shift(8n, V)), WD.sc(Nat.add(8n, m7(m)), one)), e1, tr(Nat.add(v(x), WD.sc(8n, Nat.mod(V, Mo))), Nat.mod(Nat.add(v(x), WD.sc(8n, V)), WD.sc(8n, Mo)), Nat.mod(Nat.add(v(x), C.shift(8n, V)), WD.sc(Nat.add(8n, m7(m)), one)), e2, e3))

def decode_u_fe(+one: Nat, +h1: {one == 1n : Nat}, +u: List<&2, U32>, +hu: {FS.tight(u) == True{} : Bool}) -> {FV.value(FE.of_bytes(u)) == S.decode_u(u) : Nat}:
  tr(FV.value(FE.of_bytes(u)), Nat.mod(FS.value(u), WD.sc(255n, one)), S.decode_u(u), CV.of_bytes_value(one, h1, u, hu), sy(FS.value(S.mask_last(u)), Nat.mod(FS.value(u), WD.sc(255n, one)), mask_mod(one, h1, 31n, u, hu)))

# ---- conditional swaps ----

def sel_fst(+one: Nat, +pp: Nat, +w: U32, +W: Nat, +hw: {v(w) == W : Nat}, +hwb: {Nat.is_le(W, 1n) == True{} : Bool}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b)) -> RE.Rel(one, pp, FE.select(w, x, y), S.cs_fst(W, a, b)):
  match W:
    case 0n:
      RE.r_eq(one, pp, FE.select(w, x, y), x, a, RE.sel_z(w, hw, x, y), rx)
    case 1n:
      RE.r_eq(one, pp, FE.select(w, x, y), y, b, RE.sel_o(w, hw, x, y), ry)
    case 2n+q:
      Empty.absurd(RE.Rel(one, pp, FE.select(w, x, y), b), L.false_true(hwb))

def sel_snd(+one: Nat, +pp: Nat, +w: U32, +W: Nat, +hw: {v(w) == W : Nat}, +hwb: {Nat.is_le(W, 1n) == True{} : Bool}, +x: FE.Fe, +y: FE.Fe, +a: Nat, +b: Nat, +rx: RE.Rel(one, pp, x, a), +ry: RE.Rel(one, pp, y, b)) -> RE.Rel(one, pp, FE.select(w, y, x), S.cs_snd(W, a, b)):
  match W:
    case 0n:
      RE.r_eq(one, pp, FE.select(w, y, x), y, b, RE.sel_z(w, hw, y, x), ry)
    case 1n:
      RE.r_eq(one, pp, FE.select(w, y, x), x, a, RE.sel_o(w, hw, y, x), rx)
    case 2n+q:
      Empty.absurd(RE.Rel(one, pp, FE.select(w, y, x), a), L.false_true(hwb))

def LSrep(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{0n, LSrep(m)}

def zeros_below(+n: Nat, +b: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool}) -> {FV.below(LSrep(n), b) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(Nat.is_lt(0n, b), FV.below(LSrep(m), b), hb, zeros_below(m, b, hb))

def small_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {Nat.is_lt(k, WD.sc(19n, one)) == True{} : Bool}) -> {FV.ok(one, FE.small(k)) == True{} : Bool}:
  L.and_intro(Nat.is_lt(k, WD.sc(19n, one)), FV.below(LSrep(14n), WD.sc(19n, one)), hk, zeros_below(14n, WD.sc(19n, one), PW.sc_pos(19n, one, h1)))

def one_lt19(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(1n, WD.sc(19n, one)) == True{} : Bool}:
  L.subst(Nat, t => {Nat.is_lt(t, WD.sc(19n, one)) == True{} : Bool}, WD.sc(0n, one), 1n, h1, PW.lt_sc(18n, 0n, one, h1))

