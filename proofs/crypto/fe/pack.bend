import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ./nl.bend as NL
import ./pw.bend as PW
import ./pass.bend as PS

# The radix conversions of src/crypto/curve25519/limbs.bend (written by
# tools/gen_pack.py with them): pk (bytes to 17-bit limbs) and up (17-bit
# limbs to bytes) move the digits through a bit buffer acc of nb bits.
# With acc < 2^nb,
#
#   lv(pk(bs, acc, nb))      == acc + 2^nb value(bs)     (bytes below 256)
#   value(up(xs, acc, nb))   == acc + 2^nb lv(xs)        (limbs below 2^17)
#
# every limb of pk is below 2^17 and every byte of up below 256, and the
# lengths depend only on the input's length (pkn, upn).

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- shifts and digits ----

def sc_zero(+k: Nat) -> {WD.sc(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      Equal.cong(Nat, Nat, t => Nat.double(t), WD.sc(j, 0n), 0n, sc_zero(j))

# 2^a x <= 2^b x for a <= b
def sc_up(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(WD.sc(a, x), WD.sc(b, x)) == True{} : Bool}:
  +d = Nat.sub(b, a)
  +e = tr(Nat.add(d, a), Nat.add(a, d), b, NA.add_comm(d, a), N.sub_add(b, a, h))
  L.subst(Nat, z => {Nat.is_le(WD.sc(a, x), WD.sc(z, x)) == True{} : Bool}, Nat.add(d, a), b, e, M.sc_mono(d, a, x))

# a digit x < 2^w entering above i buffered bits: acc + 2^i x < 2^i 2^w
def lt_in(+one: Nat, +h1: {one == 1n : Nat}, +i: Nat, +w: Nat, +acc: Nat, +x: Nat, +ha: {Nat.is_lt(acc, WD.sc(i, one)) == True{} : Bool}, +hx: {Nat.is_lt(x, WD.sc(w, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(acc, WD.sc(i, x)), WD.sc(i, WD.sc(w, one))) == True{} : Bool}:
  +t1 = N.lt_add_r2(acc, WD.sc(i, one), WD.sc(i, x), ha)
  +e2 = tr(Nat.add(WD.sc(i, one), WD.sc(i, x)), WD.sc(i, Nat.add(one, x)), WD.sc(i, Nat.add(x, one)), M.sc_add(i, one, x), M.cong_sc(i, Nat.add(one, x), Nat.add(x, one), NA.add_comm(one, x)))
  +t3 = M.le_sc(i, Nat.add(x, one), WD.sc(w, one), PW.succ_le(one, h1, x, WD.sc(w, one), hx))
  N.lt_le_trans(Nat.add(acc, WD.sc(i, x)), WD.sc(i, Nat.add(x, one)), WD.sc(i, WD.sc(w, one)), L.subst(Nat, z => {Nat.is_lt(Nat.add(acc, WD.sc(i, x)), z) == True{} : Bool}, Nat.add(WD.sc(i, one), WD.sc(i, x)), WD.sc(i, Nat.add(x, one)), e2, t1), t3)

# (acc + 2^i x) + 2^(i + w) v == acc + 2^i (x + 2^w v)
def lo(+w: Nat, +i: Nat, +acc: Nat, +x: Nat, +v: Nat, +lv: Nat, +ih: {lv == Nat.add(Nat.add(acc, WD.sc(i, x)), WD.sc(Nat.add(i, w), v)) : Nat}) -> {lv == Nat.add(acc, WD.sc(i, Nat.add(x, WD.sc(w, v)))) : Nat}:
  +A = WD.sc(i, x)
  +e1 = M.cong_r(A, WD.sc(Nat.add(i, w), v), WD.sc(i, WD.sc(w, v)), sy(WD.sc(i, WD.sc(w, v)), WD.sc(Nat.add(i, w), v), M.sc_sc(i, w, v)))
  +e2 = tr(Nat.add(A, WD.sc(Nat.add(i, w), v)), Nat.add(A, WD.sc(i, WD.sc(w, v))), WD.sc(i, Nat.add(x, WD.sc(w, v))), e1, M.sc_add(i, x, WD.sc(w, v)))
  tr(lv, Nat.add(Nat.add(acc, A), WD.sc(Nat.add(i, w), v)), Nat.add(acc, WD.sc(i, Nat.add(x, WD.sc(w, v)))), ih, tr(Nat.add(Nat.add(acc, A), WD.sc(Nat.add(i, w), v)), Nat.add(acc, Nat.add(A, WD.sc(Nat.add(i, w), v))), Nat.add(acc, WD.sc(i, Nat.add(x, WD.sc(w, v)))), N.add_assoc(acc, A, WD.sc(Nat.add(i, w), v)), M.cong_r(acc, Nat.add(A, WD.sc(Nat.add(i, w), v)), WD.sc(i, Nat.add(x, WD.sc(w, v))), e2)))

# 2^k == 1 + (2^k - 1)
def ksucc(+k: Nat) -> {1n+Nat.sub(WD.sc(k, 1n), 1n) == WD.sc(k, 1n) : Nat}:
  PW.pos_succ(1n, {==}, k)

# x mod 2^k + 2^k (x div 2^k) == x
def dmk(+k: Nat, +x: Nat) -> {Nat.add(Nat.mod(x, WD.sc(k, 1n)), WD.sc(k, Nat.div(x, WD.sc(k, 1n)))) == x : Nat}:
  +K = WD.sc(k, 1n)
  +q = Nat.div(x, K)
  +r = Nat.mod(x, K)
  +e0 = L.subst(Nat, z => {x == Nat.add(Nat.mul(Nat.div(x, z), z), Nat.mod(x, z)) : Nat}, 1n+Nat.sub(K, 1n), K, ksucc(k), NR.dm_eq(Nat.sub(K, 1n), x))
  tr(Nat.add(r, WD.sc(k, q)), Nat.add(r, Nat.mul(q, K)), x, M.cong_r(r, WD.sc(k, q), Nat.mul(q, K), sy(Nat.mul(q, K), WD.sc(k, q), AR.mul_sc(k, q))), tr(Nat.add(r, Nat.mul(q, K)), Nat.add(Nat.mul(q, K), r), x, NA.add_comm(r, Nat.mul(q, K)), sy(x, Nat.add(Nat.mul(q, K), r), e0)))

# x mod 2^k < 2^k (in the symbolic one)
def modk_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +x: Nat) -> {Nat.is_lt(Nat.mod(x, WD.sc(k, 1n)), WD.sc(k, one)) == True{} : Bool}:
  +K = WD.sc(k, 1n)
  L.subst(Nat, o => {Nat.is_lt(Nat.mod(x, K), WD.sc(k, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, z => {Nat.is_lt(Nat.mod(x, z), z) == True{} : Bool}, 1n+Nat.sub(K, 1n), K, ksucc(k), NR.dm_lt(Nat.sub(K, 1n), x)))

# s < 2^k E -> s div 2^k < E
def div_ltk(+k: Nat, +s: Nat, +E: Nat, +h: {Nat.is_lt(s, WD.sc(k, E)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(s, WD.sc(k, 1n)), E) == True{} : Bool}:
  +K = WD.sc(k, 1n)
  +h2 = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, WD.sc(k, E), Nat.mul(E, K), sy(Nat.mul(E, K), WD.sc(k, E), AR.mul_sc(k, E)), h)
  +e0 = L.subst(Nat, z => {Nat.is_le(E, Nat.div(s, z)) == Nat.is_le(Nat.mul(E, z), s) : Bool}, 1n+Nat.sub(K, 1n), K, ksucc(k), NR.le_div(Nat.sub(K, 1n), E, s))
  N.not_le_lt(E, Nat.div(s, K), Equal.trans(Bool, Nat.is_le(E, Nat.div(s, K)), Nat.is_le(Nat.mul(E, K), s), False{}, e0, N.lt_not_le(s, Nat.mul(E, K), h2)))

# x mod 256 == x for x < 256
def mod256(+x: Nat, +h: {Nat.is_lt(x, 256n) == True{} : Bool}) -> {Nat.mod(x, 256n) == x : Nat}:
  NR.mod_of(0n, 255n, x, h)

# the digit's low part r completes a limb (or byte) above the buffer, and
# its high part u stays: with r + u == x,
# (acc + 2^j r) + (2^j u + 2^j t) == acc + 2^j (x + t)
def emitv(+j: Nat, +acc: Nat, +r: Nat, +u: Nat, +x: Nat, +t: Nat, +ex: {Nat.add(r, u) == x : Nat}) -> {Nat.add(Nat.add(acc, WD.sc(j, r)), Nat.add(WD.sc(j, u), WD.sc(j, t))) == Nat.add(acc, WD.sc(j, Nat.add(x, t))) : Nat}:
  +R = WD.sc(j, r)
  +U = WD.sc(j, u)
  +T = WD.sc(j, t)
  +G = Nat.add(acc, WD.sc(j, Nat.add(x, t)))
  +e1 = tr(Nat.add(R, Nat.add(U, T)), Nat.add(Nat.add(R, U), T), WD.sc(j, Nat.add(x, t)), sy(Nat.add(Nat.add(R, U), T), Nat.add(R, Nat.add(U, T)), N.add_assoc(R, U, T)), tr(Nat.add(Nat.add(R, U), T), Nat.add(WD.sc(j, x), T), WD.sc(j, Nat.add(x, t)), M.cong_l(Nat.add(R, U), WD.sc(j, x), T, tr(Nat.add(R, U), WD.sc(j, Nat.add(r, u)), WD.sc(j, x), M.sc_add(j, r, u), M.cong_sc(j, Nat.add(r, u), x, ex))), M.sc_add(j, x, t)))
  tr(Nat.add(Nat.add(acc, R), Nat.add(U, T)), Nat.add(acc, Nat.add(R, Nat.add(U, T))), G, N.add_assoc(acc, R, Nat.add(U, T)), M.cong_r(acc, Nat.add(R, Nat.add(U, T)), WD.sc(j, Nat.add(x, t)), e1))

# a + 2^w p with p == q + s: a + (2^w q + 2^w s)
def emitw(+w: Nat, +a: Nat, +p: Nat, +q: Nat, +s: Nat, +ih: {p == Nat.add(q, s) : Nat}) -> {Nat.add(a, WD.sc(w, p)) == Nat.add(a, Nat.add(WD.sc(w, q), WD.sc(w, s))) : Nat}:
  M.cong_r(a, WD.sc(w, p), Nat.add(WD.sc(w, q), WD.sc(w, s)), tr(WD.sc(w, p), WD.sc(w, Nat.add(q, s)), Nat.add(WD.sc(w, q), WD.sc(w, s)), M.cong_sc(w, p, Nat.add(q, s), ih), sy(Nat.add(WD.sc(w, q), WD.sc(w, s)), WD.sc(w, Nat.add(q, s)), M.sc_add(w, q, s))))

# ---- bytes to 17-bit limbs ----

def b8_lt(+b: U32) -> {Nat.is_lt(LS.b8(b), 256n) == True{} : Bool}:
  NR.dm_lt(255n, U32.to_nat(b))

def b8_lt1(+one: Nat, +h1: {one == 1n : Nat}, +b: U32) -> {Nat.is_lt(LS.b8(b), WD.sc(8n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(LS.b8(b), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), b8_lt(b))

def b8_id(+b: U32, +h: {Nat.is_lt(U32.to_nat(b), 256n) == True{} : Bool}) -> {LS.b8(b) == U32.to_nat(b) : Nat}:
  mod256(U32.to_nat(b), h)


# the value, for bytes below 256
def pk_val(+bs: List<&2, U32>, +acc: Nat, +nb: Nat, +hb: {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}, +hn: {Nat.is_le(nb, 16n) == True{} : Bool}) -> {FV.lv(LS.pk(bs, acc, nb)) == Nat.add(acc, WD.sc(nb, FS.value(bs))) : Nat}:
  match bs:
    case Nil{}:
      M.cong_r(acc, 0n, WD.sc(nb, 0n), sy(WD.sc(nb, 0n), 0n, sc_zero(nb)))
    case Con{+b, +bt}:
      match nb:
        case 0n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(0n, B)), 8n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(0n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 0n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(0n, B)), 8n, ht, {==})))
        case 1n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(1n, B)), 9n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(1n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 1n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(1n, B)), 9n, ht, {==})))
        case 2n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(2n, B)), 10n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(2n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 2n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(2n, B)), 10n, ht, {==})))
        case 3n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(3n, B)), 11n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(3n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 3n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(3n, B)), 11n, ht, {==})))
        case 4n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(4n, B)), 12n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(4n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 4n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(4n, B)), 12n, ht, {==})))
        case 5n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(5n, B)), 13n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(5n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 5n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(5n, B)), 13n, ht, {==})))
        case 6n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(6n, B)), 14n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(6n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 6n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(6n, B)), 14n, ht, {==})))
        case 7n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(7n, B)), 15n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(7n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 7n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(7n, B)), 15n, ht, {==})))
        case 8n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(8n, B)), 16n))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(8n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, 8n, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(8n, B)), 16n, ht, {==})))
        case 9n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 256n)
          +q = Nat.div(B, 256n)
          +a = Nat.add(acc, LS.shl(9n, r))
          +P = FV.lv(LS.pk(bt, q, 0n))
          +x1 = emitw(17n, a, P, q, WD.sc(0n, V), pk_val(bt, q, 0n, ht, {==}))
          +x2 = emitv(9n, acc, r, WD.sc(8n, q), B, WD.sc(8n, V), dmk(8n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(9n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(0n, V)))), Nat.add(acc, WD.sc(9n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 10n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 128n)
          +q = Nat.div(B, 128n)
          +a = Nat.add(acc, LS.shl(10n, r))
          +P = FV.lv(LS.pk(bt, q, 1n))
          +x1 = emitw(17n, a, P, q, WD.sc(1n, V), pk_val(bt, q, 1n, ht, {==}))
          +x2 = emitv(10n, acc, r, WD.sc(7n, q), B, WD.sc(8n, V), dmk(7n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(10n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(1n, V)))), Nat.add(acc, WD.sc(10n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 11n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 64n)
          +q = Nat.div(B, 64n)
          +a = Nat.add(acc, LS.shl(11n, r))
          +P = FV.lv(LS.pk(bt, q, 2n))
          +x1 = emitw(17n, a, P, q, WD.sc(2n, V), pk_val(bt, q, 2n, ht, {==}))
          +x2 = emitv(11n, acc, r, WD.sc(6n, q), B, WD.sc(8n, V), dmk(6n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(11n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(2n, V)))), Nat.add(acc, WD.sc(11n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 12n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 32n)
          +q = Nat.div(B, 32n)
          +a = Nat.add(acc, LS.shl(12n, r))
          +P = FV.lv(LS.pk(bt, q, 3n))
          +x1 = emitw(17n, a, P, q, WD.sc(3n, V), pk_val(bt, q, 3n, ht, {==}))
          +x2 = emitv(12n, acc, r, WD.sc(5n, q), B, WD.sc(8n, V), dmk(5n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(12n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(3n, V)))), Nat.add(acc, WD.sc(12n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 13n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 16n)
          +q = Nat.div(B, 16n)
          +a = Nat.add(acc, LS.shl(13n, r))
          +P = FV.lv(LS.pk(bt, q, 4n))
          +x1 = emitw(17n, a, P, q, WD.sc(4n, V), pk_val(bt, q, 4n, ht, {==}))
          +x2 = emitv(13n, acc, r, WD.sc(4n, q), B, WD.sc(8n, V), dmk(4n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(13n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(4n, V)))), Nat.add(acc, WD.sc(13n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 14n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 8n)
          +q = Nat.div(B, 8n)
          +a = Nat.add(acc, LS.shl(14n, r))
          +P = FV.lv(LS.pk(bt, q, 5n))
          +x1 = emitw(17n, a, P, q, WD.sc(5n, V), pk_val(bt, q, 5n, ht, {==}))
          +x2 = emitv(14n, acc, r, WD.sc(3n, q), B, WD.sc(8n, V), dmk(3n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(14n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(5n, V)))), Nat.add(acc, WD.sc(14n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 15n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 4n)
          +q = Nat.div(B, 4n)
          +a = Nat.add(acc, LS.shl(15n, r))
          +P = FV.lv(LS.pk(bt, q, 6n))
          +x1 = emitw(17n, a, P, q, WD.sc(6n, V), pk_val(bt, q, 6n, ht, {==}))
          +x2 = emitv(15n, acc, r, WD.sc(2n, q), B, WD.sc(8n, V), dmk(2n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(15n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(6n, V)))), Nat.add(acc, WD.sc(15n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 16n:
          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
          +r = Nat.mod(B, 2n)
          +q = Nat.div(B, 2n)
          +a = Nat.add(acc, LS.shl(16n, r))
          +P = FV.lv(LS.pk(bt, q, 7n))
          +x1 = emitw(17n, a, P, q, WD.sc(7n, V), pk_val(bt, q, 7n, ht, {==}))
          +x2 = emitv(16n, acc, r, WD.sc(1n, q), B, WD.sc(8n, V), dmk(1n, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(16n, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(7n, V)))), Nat.add(acc, WD.sc(16n, Nat.add(B, WD.sc(8n, V)))), x1, x2))
        case 17n+m:
          Empty.absurd({FV.lv(LS.pk(Con{b, bt}, acc, 17n+m)) == Nat.add(acc, WD.sc(17n+m, FS.value(Con{b, bt}))) : Nat}, L.false_true(hn))

# every limb is below 2^17, for a buffer acc < 2^nb
def pk_below(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +acc: Nat, +nb: Nat, +ha: {Nat.is_lt(acc, WD.sc(nb, one)) == True{} : Bool}, +hn: {Nat.is_le(nb, 16n) == True{} : Bool}) -> {FV.below(LS.pk(bs, acc, nb), WD.sc(17n, one)) == True{} : Bool}:
  match bs:
    case Nil{}:
      NL.below_con(acc, Nil{}, WD.sc(17n, one), N.lt_le_trans(acc, WD.sc(nb, one), WD.sc(17n, one), ha, sc_up(nb, 17n, one, N.le_trans(nb, 16n, 17n, hn, {==}))), {==})
    case Con{+b, +bt}:
      match nb:
        case 0n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(0n, B)), 8n, lt_in(one, h1, 0n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 1n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(1n, B)), 9n, lt_in(one, h1, 1n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 2n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(2n, B)), 10n, lt_in(one, h1, 2n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 3n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(3n, B)), 11n, lt_in(one, h1, 3n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 4n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(4n, B)), 12n, lt_in(one, h1, 4n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 5n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(5n, B)), 13n, lt_in(one, h1, 5n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 6n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(6n, B)), 14n, lt_in(one, h1, 6n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 7n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(7n, B)), 15n, lt_in(one, h1, 7n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 8n:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(8n, B)), 16n, lt_in(one, h1, 8n, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})
        case 9n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 256n)
          +q = Nat.div(B, 256n)
          NL.below_con(Nat.add(acc, LS.shl(9n, r)), LS.pk(bt, q, 0n), WD.sc(17n, one), lt_in(one, h1, 9n, 8n, acc, r, ha, modk_lt(one, h1, 8n, B)), pk_below(one, h1, bt, q, 0n, div_ltk(8n, B, WD.sc(0n, one), b8_lt1(one, h1, b)), {==}))
        case 10n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 128n)
          +q = Nat.div(B, 128n)
          NL.below_con(Nat.add(acc, LS.shl(10n, r)), LS.pk(bt, q, 1n), WD.sc(17n, one), lt_in(one, h1, 10n, 7n, acc, r, ha, modk_lt(one, h1, 7n, B)), pk_below(one, h1, bt, q, 1n, div_ltk(7n, B, WD.sc(1n, one), b8_lt1(one, h1, b)), {==}))
        case 11n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 64n)
          +q = Nat.div(B, 64n)
          NL.below_con(Nat.add(acc, LS.shl(11n, r)), LS.pk(bt, q, 2n), WD.sc(17n, one), lt_in(one, h1, 11n, 6n, acc, r, ha, modk_lt(one, h1, 6n, B)), pk_below(one, h1, bt, q, 2n, div_ltk(6n, B, WD.sc(2n, one), b8_lt1(one, h1, b)), {==}))
        case 12n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 32n)
          +q = Nat.div(B, 32n)
          NL.below_con(Nat.add(acc, LS.shl(12n, r)), LS.pk(bt, q, 3n), WD.sc(17n, one), lt_in(one, h1, 12n, 5n, acc, r, ha, modk_lt(one, h1, 5n, B)), pk_below(one, h1, bt, q, 3n, div_ltk(5n, B, WD.sc(3n, one), b8_lt1(one, h1, b)), {==}))
        case 13n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 16n)
          +q = Nat.div(B, 16n)
          NL.below_con(Nat.add(acc, LS.shl(13n, r)), LS.pk(bt, q, 4n), WD.sc(17n, one), lt_in(one, h1, 13n, 4n, acc, r, ha, modk_lt(one, h1, 4n, B)), pk_below(one, h1, bt, q, 4n, div_ltk(4n, B, WD.sc(4n, one), b8_lt1(one, h1, b)), {==}))
        case 14n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 8n)
          +q = Nat.div(B, 8n)
          NL.below_con(Nat.add(acc, LS.shl(14n, r)), LS.pk(bt, q, 5n), WD.sc(17n, one), lt_in(one, h1, 14n, 3n, acc, r, ha, modk_lt(one, h1, 3n, B)), pk_below(one, h1, bt, q, 5n, div_ltk(3n, B, WD.sc(5n, one), b8_lt1(one, h1, b)), {==}))
        case 15n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 4n)
          +q = Nat.div(B, 4n)
          NL.below_con(Nat.add(acc, LS.shl(15n, r)), LS.pk(bt, q, 6n), WD.sc(17n, one), lt_in(one, h1, 15n, 2n, acc, r, ha, modk_lt(one, h1, 2n, B)), pk_below(one, h1, bt, q, 6n, div_ltk(2n, B, WD.sc(6n, one), b8_lt1(one, h1, b)), {==}))
        case 16n:
          +B = LS.b8(b)
          +r = Nat.mod(B, 2n)
          +q = Nat.div(B, 2n)
          NL.below_con(Nat.add(acc, LS.shl(16n, r)), LS.pk(bt, q, 7n), WD.sc(17n, one), lt_in(one, h1, 16n, 1n, acc, r, ha, modk_lt(one, h1, 1n, B)), pk_below(one, h1, bt, q, 7n, div_ltk(1n, B, WD.sc(7n, one), b8_lt1(one, h1, b)), {==}))
        case 17n+m:
          Empty.absurd({FV.below(LS.pk(Con{b, bt}, acc, 17n+m), WD.sc(17n, one)) == True{} : Bool}, L.false_true(hn))

# the number of limbs of n bytes entering above nb buffered bits
def pkn(n: Nat, +nb: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+k:
      match nb:
        case 0n:
          pkn(k, 8n)
        case 1n:
          pkn(k, 9n)
        case 2n:
          pkn(k, 10n)
        case 3n:
          pkn(k, 11n)
        case 4n:
          pkn(k, 12n)
        case 5n:
          pkn(k, 13n)
        case 6n:
          pkn(k, 14n)
        case 7n:
          pkn(k, 15n)
        case 8n:
          pkn(k, 16n)
        case 9n:
          1n+pkn(k, 0n)
        case 10n:
          1n+pkn(k, 1n)
        case 11n:
          1n+pkn(k, 2n)
        case 12n:
          1n+pkn(k, 3n)
        case 13n:
          1n+pkn(k, 4n)
        case 14n:
          1n+pkn(k, 5n)
        case 15n:
          1n+pkn(k, 6n)
        case 16n:
          1n+pkn(k, 7n)
        case 17n+m:
          1n+pkn(k, 8n)

def pk_len(+bs: List<&2, U32>, +acc: Nat, +nb: Nat) -> {PS.ln(LS.pk(bs, acc, nb)) == pkn(PS.ln(LS.nat_of(bs)), nb) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      match nb:
        case 0n:
          pk_len(bt, Nat.add(acc, LS.shl(0n, LS.b8(b))), 8n)
        case 1n:
          pk_len(bt, Nat.add(acc, LS.shl(1n, LS.b8(b))), 9n)
        case 2n:
          pk_len(bt, Nat.add(acc, LS.shl(2n, LS.b8(b))), 10n)
        case 3n:
          pk_len(bt, Nat.add(acc, LS.shl(3n, LS.b8(b))), 11n)
        case 4n:
          pk_len(bt, Nat.add(acc, LS.shl(4n, LS.b8(b))), 12n)
        case 5n:
          pk_len(bt, Nat.add(acc, LS.shl(5n, LS.b8(b))), 13n)
        case 6n:
          pk_len(bt, Nat.add(acc, LS.shl(6n, LS.b8(b))), 14n)
        case 7n:
          pk_len(bt, Nat.add(acc, LS.shl(7n, LS.b8(b))), 15n)
        case 8n:
          pk_len(bt, Nat.add(acc, LS.shl(8n, LS.b8(b))), 16n)
        case 9n:
          +q = Nat.div(LS.b8(b), 256n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 0n)), pkn(PS.ln(LS.nat_of(bt)), 0n), pk_len(bt, q, 0n))
        case 10n:
          +q = Nat.div(LS.b8(b), 128n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 1n)), pkn(PS.ln(LS.nat_of(bt)), 1n), pk_len(bt, q, 1n))
        case 11n:
          +q = Nat.div(LS.b8(b), 64n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 2n)), pkn(PS.ln(LS.nat_of(bt)), 2n), pk_len(bt, q, 2n))
        case 12n:
          +q = Nat.div(LS.b8(b), 32n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 3n)), pkn(PS.ln(LS.nat_of(bt)), 3n), pk_len(bt, q, 3n))
        case 13n:
          +q = Nat.div(LS.b8(b), 16n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 4n)), pkn(PS.ln(LS.nat_of(bt)), 4n), pk_len(bt, q, 4n))
        case 14n:
          +q = Nat.div(LS.b8(b), 8n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 5n)), pkn(PS.ln(LS.nat_of(bt)), 5n), pk_len(bt, q, 5n))
        case 15n:
          +q = Nat.div(LS.b8(b), 4n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 6n)), pkn(PS.ln(LS.nat_of(bt)), 6n), pk_len(bt, q, 6n))
        case 16n:
          +q = Nat.div(LS.b8(b), 2n)
          N.succ_cong(PS.ln(LS.pk(bt, q, 7n)), pkn(PS.ln(LS.nat_of(bt)), 7n), pk_len(bt, q, 7n))
        case 17n+m:
          N.succ_cong(PS.ln(LS.pk(bt, LS.b8(b), 8n)), pkn(PS.ln(LS.nat_of(bt)), 8n), pk_len(bt, LS.b8(b), 8n))

# n bytes have length n
def bytes_len(+n: Nat, +bs: List<&2, U32>, +h: {FS.bytes_ok(n, bs) == True{} : Bool}) -> {PS.ln(LS.nat_of(bs)) == n : Nat}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({PS.ln(LS.nat_of(Con{x, xt})) == 0n : Nat}, L.false_true(h))
    case 1n+m Nil{}:
      Empty.absurd({PS.ln(LS.nat_of(Nil{})) == 1n+m : Nat}, L.false_true(h))
    case 1n+ +m Con{+x, +xt}:
      N.succ_cong(PS.ln(LS.nat_of(xt)), m, bytes_len(m, xt, L.and_right(Nat.is_lt(U32.to_nat(x), 256n), FS.bytes_ok(m, xt), h)))

# ---- the first n limbs ----

def fit_len(+n: Nat, +xs: List<&2, Nat>) -> {PS.ln(LS.fit(n, xs)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      N.succ_cong(PS.ln(LS.fit(m, LS.ltl(xs))), m, fit_len(m, LS.ltl(xs)))

def fit_below(+n: Nat, +xs: List<&2, Nat>, +b: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool}, +h: {FV.below(xs, b) == True{} : Bool}) -> {FV.below(LS.fit(n, xs), b) == True{} : Bool}:
  match n xs:
    case 0n _:
      {==}
    case 1n+ +m Nil{}:
      NL.below_con(0n, LS.fit(m, Nil{}), b, hb, fit_below(m, Nil{}, b, hb, {==}))
    case 1n+ +m Con{+x, +xt}:
      NL.below_con(x, LS.fit(m, xt), b, NL.below_head(x, xt, b, h), fit_below(m, xt, b, hb, NL.below_tail(x, xt, b, h)))

def fit_nil(+n: Nat) -> {FV.lv(LS.fit(n, Nil{})) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => C.shift(17n, t), FV.lv(LS.fit(m, Nil{})), 0n, fit_nil(m))

# the value of the first n limbs
def fit_val(+n: Nat, +xs: List<&2, Nat>) -> {FV.lv(LS.fit(n, xs)) == FV.lv(LS.take(n, xs)) : Nat}:
  match n xs:
    case 0n _:
      {==}
    case 1n+ +m Nil{}:
      fit_nil(1n+m)
    case 1n+ +m Con{+x, +xt}:
      M.cong_r(x, C.shift(17n, FV.lv(LS.fit(m, xt))), C.shift(17n, FV.lv(LS.take(m, xt))), M.cong_sc(17n, FV.lv(LS.fit(m, xt)), FV.lv(LS.take(m, xt)), fit_val(m, xt)))

# a list of n limbs is its first n limbs
def fit_id(+n: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == n : Nat}) -> {LS.fit(n, xs) == xs : List<&2, Nat>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({LS.fit(0n, Con{x, xt}) == Con{x, xt} : List<&2, Nat>}, N.succ_zero(PS.ln(xt), hl))
    case 1n+m Nil{}:
      Empty.absurd({LS.fit(1n+m, Nil{}) == Nil{} : List<&2, Nat>}, N.zero_succ(m, hl))
    case 1n+ +m Con{+x, +xt}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, t => Con{x, t}, LS.fit(m, xt), xt, fit_id(m, xt, N.succ_inj(PS.ln(xt), m, hl)))

# ---- 17-bit limbs to bytes ----

def byte_val(+a: Nat) -> {U32.to_nat(LS.byte(a)) == Nat.mod(a, 256n) : Nat}:
  U.to_nat_from_nat(Nat.mod(a, 256n), 8n, {==}, NR.dm_lt(255n, a))

def byte_lt(+a: Nat) -> {Nat.is_lt(U32.to_nat(LS.byte(a)), 256n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, 256n) == True{} : Bool}, Nat.mod(a, 256n), U32.to_nat(LS.byte(a)), sy(U32.to_nat(LS.byte(a)), Nat.mod(a, 256n), byte_val(a)), NR.dm_lt(255n, a))

# a byte holds a value below 2^8
def byte_id(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +h: {Nat.is_lt(a, WD.sc(8n, one)) == True{} : Bool}) -> {U32.to_nat(LS.byte(a)) == a : Nat}:
  tr(U32.to_nat(LS.byte(a)), Nat.mod(a, 256n), a, byte_val(a), mod256(a, L.subst(Nat, o => {Nat.is_lt(a, WD.sc(8n, o)) == True{} : Bool}, one, 1n, h1, h)))

# one byte leaves: byte(a) + 2^8 w == a + 2^8 t for w == a div 256 + t
def bstep(+a: Nat, +w: Nat, +t: Nat, +e: {w == Nat.add(Nat.div(a, 256n), t) : Nat}) -> {Nat.add(U32.to_nat(LS.byte(a)), WD.sc(8n, w)) == Nat.add(a, WD.sc(8n, t)) : Nat}:
  +q = Nat.div(a, 256n)
  +r = Nat.mod(a, 256n)
  +e1 = M.cong_add(U32.to_nat(LS.byte(a)), r, WD.sc(8n, w), Nat.add(WD.sc(8n, q), WD.sc(8n, t)), byte_val(a), tr(WD.sc(8n, w), WD.sc(8n, Nat.add(q, t)), Nat.add(WD.sc(8n, q), WD.sc(8n, t)), M.cong_sc(8n, w, Nat.add(q, t), e), sy(Nat.add(WD.sc(8n, q), WD.sc(8n, t)), WD.sc(8n, Nat.add(q, t)), M.sc_add(8n, q, t))))
  tr(Nat.add(U32.to_nat(LS.byte(a)), WD.sc(8n, w)), Nat.add(r, Nat.add(WD.sc(8n, q), WD.sc(8n, t))), Nat.add(a, WD.sc(8n, t)), e1, tr(Nat.add(r, Nat.add(WD.sc(8n, q), WD.sc(8n, t))), Nat.add(Nat.add(r, WD.sc(8n, q)), WD.sc(8n, t)), Nat.add(a, WD.sc(8n, t)), sy(Nat.add(Nat.add(r, WD.sc(8n, q)), WD.sc(8n, t)), Nat.add(r, Nat.add(WD.sc(8n, q), WD.sc(8n, t))), N.add_assoc(r, WD.sc(8n, q), WD.sc(8n, t))), M.cong_l(Nat.add(r, WD.sc(8n, q)), a, WD.sc(8n, t), dmk(8n, a))))

# the first byte b0 == c and the rest w == x1 + s: b0 + 2^8 w == c + (2^8 x1 + 2^8 s)
def upv(+b0: Nat, +c: Nat, +w: Nat, +x1: Nat, +s: Nat, +e0: {b0 == c : Nat}, +e1: {w == Nat.add(x1, s) : Nat}) -> {Nat.add(b0, WD.sc(8n, w)) == Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, s))) : Nat}:
  tr(Nat.add(b0, WD.sc(8n, w)), Nat.add(c, WD.sc(8n, w)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, s))), M.cong_l(b0, c, WD.sc(8n, w), e0), emitw(8n, c, w, x1, s, e1))

# the value, for limbs below 2^17 and a buffer acc < 2^nb, nb <= 7
def up_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +acc: Nat, +nb: Nat, +hx: {FV.below(xs, WD.sc(17n, one)) == True{} : Bool}, +ha: {Nat.is_lt(acc, WD.sc(nb, one)) == True{} : Bool}, +hn: {Nat.is_le(nb, 7n) == True{} : Bool}) -> {FS.value(LS.up(xs, acc, nb)) == Nat.add(acc, WD.sc(nb, FV.lv(xs))) : Nat}:
  match xs:
    case Nil{}:
      +h8 = N.lt_le_trans(acc, WD.sc(nb, one), WD.sc(8n, one), ha, sc_up(nb, 8n, one, N.le_trans(nb, 7n, 8n, hn, {==})))
      tr(Nat.add(U32.to_nat(LS.byte(acc)), 0n), Nat.add(acc, 0n), Nat.add(acc, WD.sc(nb, 0n)), M.cong_l(U32.to_nat(LS.byte(acc)), acc, 0n, byte_id(one, h1, acc, h8)), M.cong_r(acc, 0n, WD.sc(nb, 0n), sy(WD.sc(nb, 0n), 0n, sc_zero(nb))))
    case Con{+x, +xt}:
      match nb:
        case 0n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 256n)
          +x1 = Nat.div(x, 256n)
          +c = Nat.add(acc, LS.shl(0n, r))
          +hx1 = div_ltk(8n, x, WD.sc(9n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 1n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 1n, ht, div_ltk(8n, x1, WD.sc(1n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 0n, 8n, acc, r, ha, modk_lt(one, h1, 8n, x)))
          +e1 = bstep(x1, W, WD.sc(1n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 0n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(1n, V))))), Nat.add(acc, WD.sc(0n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(1n, V)), e0, e1), emitv(0n, acc, r, WD.sc(8n, x1), x, WD.sc(17n, V), dmk(8n, x)))
        case 1n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 128n)
          +x1 = Nat.div(x, 128n)
          +c = Nat.add(acc, LS.shl(1n, r))
          +hx1 = div_ltk(7n, x, WD.sc(10n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 2n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 2n, ht, div_ltk(8n, x1, WD.sc(2n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 1n, 7n, acc, r, ha, modk_lt(one, h1, 7n, x)))
          +e1 = bstep(x1, W, WD.sc(2n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 1n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(2n, V))))), Nat.add(acc, WD.sc(1n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(2n, V)), e0, e1), emitv(1n, acc, r, WD.sc(7n, x1), x, WD.sc(17n, V), dmk(7n, x)))
        case 2n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 64n)
          +x1 = Nat.div(x, 64n)
          +c = Nat.add(acc, LS.shl(2n, r))
          +hx1 = div_ltk(6n, x, WD.sc(11n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 3n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 3n, ht, div_ltk(8n, x1, WD.sc(3n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 2n, 6n, acc, r, ha, modk_lt(one, h1, 6n, x)))
          +e1 = bstep(x1, W, WD.sc(3n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 2n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(3n, V))))), Nat.add(acc, WD.sc(2n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(3n, V)), e0, e1), emitv(2n, acc, r, WD.sc(6n, x1), x, WD.sc(17n, V), dmk(6n, x)))
        case 3n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 32n)
          +x1 = Nat.div(x, 32n)
          +c = Nat.add(acc, LS.shl(3n, r))
          +hx1 = div_ltk(5n, x, WD.sc(12n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 4n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 4n, ht, div_ltk(8n, x1, WD.sc(4n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 3n, 5n, acc, r, ha, modk_lt(one, h1, 5n, x)))
          +e1 = bstep(x1, W, WD.sc(4n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 3n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(4n, V))))), Nat.add(acc, WD.sc(3n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(4n, V)), e0, e1), emitv(3n, acc, r, WD.sc(5n, x1), x, WD.sc(17n, V), dmk(5n, x)))
        case 4n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 16n)
          +x1 = Nat.div(x, 16n)
          +c = Nat.add(acc, LS.shl(4n, r))
          +hx1 = div_ltk(4n, x, WD.sc(13n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 5n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 5n, ht, div_ltk(8n, x1, WD.sc(5n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 4n, 4n, acc, r, ha, modk_lt(one, h1, 4n, x)))
          +e1 = bstep(x1, W, WD.sc(5n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 4n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(5n, V))))), Nat.add(acc, WD.sc(4n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(5n, V)), e0, e1), emitv(4n, acc, r, WD.sc(4n, x1), x, WD.sc(17n, V), dmk(4n, x)))
        case 5n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 8n)
          +x1 = Nat.div(x, 8n)
          +c = Nat.add(acc, LS.shl(5n, r))
          +hx1 = div_ltk(3n, x, WD.sc(14n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 6n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 6n, ht, div_ltk(8n, x1, WD.sc(6n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 5n, 3n, acc, r, ha, modk_lt(one, h1, 3n, x)))
          +e1 = bstep(x1, W, WD.sc(6n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 5n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(6n, V))))), Nat.add(acc, WD.sc(5n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(6n, V)), e0, e1), emitv(5n, acc, r, WD.sc(3n, x1), x, WD.sc(17n, V), dmk(3n, x)))
        case 6n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 4n)
          +x1 = Nat.div(x, 4n)
          +c = Nat.add(acc, LS.shl(6n, r))
          +hx1 = div_ltk(2n, x, WD.sc(15n, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), 7n))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), 7n, ht, div_ltk(8n, x1, WD.sc(7n, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 6n, 2n, acc, r, ha, modk_lt(one, h1, 2n, x)))
          +e1 = bstep(x1, W, WD.sc(7n, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, 6n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(7n, V))))), Nat.add(acc, WD.sc(6n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(7n, V)), e0, e1), emitv(6n, acc, r, WD.sc(2n, x1), x, WD.sc(17n, V), dmk(2n, x)))
        case 7n:
          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
          +r = Nat.mod(x, 2n)
          +x1 = Nat.div(x, 2n)
          +x2 = Nat.div(x1, 256n)
          +c = Nat.add(acc, LS.shl(7n, r))
          +hx1 = div_ltk(1n, x, WD.sc(16n, one), hX)
          +W = FS.value(LS.up(xt, 0n, 0n))
          +ih = up_val(one, h1, xt, 0n, 0n, ht, PW.sc_pos(0n, one, h1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, 7n, 1n, acc, r, ha, modk_lt(one, h1, 1n, x)))
          +W2 = Nat.add(U32.to_nat(LS.byte(x2)), WD.sc(8n, W))
          +e2 = M.cong_add(U32.to_nat(LS.byte(x2)), x2, WD.sc(8n, W), WD.sc(8n, V), byte_id(one, h1, x2, div_ltk(8n, x1, WD.sc(8n, one), hx1)), M.cong_sc(8n, W, V, ih))
          +e1 = bstep(x1, W2, WD.sc(8n, V), e2)
          tr(FS.value(LS.up(Con{x, xt}, acc, 7n)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(8n, V))))), Nat.add(acc, WD.sc(7n, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W2)), x1, WD.sc(8n, WD.sc(8n, V)), e0, e1), emitv(7n, acc, r, WD.sc(1n, x1), x, WD.sc(17n, V), dmk(1n, x)))
        case 8n+m:
          Empty.absurd({FS.value(LS.up(Con{x, xt}, acc, 8n+m)) == Nat.add(acc, WD.sc(8n+m, FV.lv(Con{x, xt}))) : Nat}, L.false_true(hn))

# every byte is below 256
def up_below(+xs: List<&2, Nat>, +acc: Nat, +nb: Nat) -> {FV.below(LS.nat_of(LS.up(xs, acc, nb)), 256n) == True{} : Bool}:
  match xs:
    case Nil{}:
      NL.below_con(U32.to_nat(LS.byte(acc)), Nil{}, 256n, byte_lt(acc), {==})
    case Con{+x, +xt}:
      match nb:
        case 0n:
          +x1 = Nat.div(x, 256n)
          +c = Nat.add(acc, LS.shl(0n, Nat.mod(x, 256n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 1n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 1n)))
        case 1n:
          +x1 = Nat.div(x, 128n)
          +c = Nat.add(acc, LS.shl(1n, Nat.mod(x, 128n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 2n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 2n)))
        case 2n:
          +x1 = Nat.div(x, 64n)
          +c = Nat.add(acc, LS.shl(2n, Nat.mod(x, 64n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 3n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 3n)))
        case 3n:
          +x1 = Nat.div(x, 32n)
          +c = Nat.add(acc, LS.shl(3n, Nat.mod(x, 32n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 4n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 4n)))
        case 4n:
          +x1 = Nat.div(x, 16n)
          +c = Nat.add(acc, LS.shl(4n, Nat.mod(x, 16n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 5n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 5n)))
        case 5n:
          +x1 = Nat.div(x, 8n)
          +c = Nat.add(acc, LS.shl(5n, Nat.mod(x, 8n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 6n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 6n)))
        case 6n:
          +x1 = Nat.div(x, 4n)
          +c = Nat.add(acc, LS.shl(6n, Nat.mod(x, 4n)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), 7n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), 7n)))
        case 7n:
          +x1 = Nat.div(x, 2n)
          +x2 = Nat.div(x1, 256n)
          +c = Nat.add(acc, LS.shl(7n, Nat.mod(x, 2n)))
          +T = LS.nat_of(LS.up(xt, 0n, 0n))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), Con{U32.to_nat(LS.byte(x2)), T}}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), Con{U32.to_nat(LS.byte(x2)), T}, 256n, byte_lt(x1), NL.below_con(U32.to_nat(LS.byte(x2)), T, 256n, byte_lt(x2), up_below(xt, 0n, 0n))))
        case 8n+ +m:
          NL.below_con(U32.to_nat(LS.byte(acc)), LS.nat_of(LS.up(xt, x, 0n)), 256n, byte_lt(acc), up_below(xt, x, 0n))

# the number of bytes of n limbs entering above nb buffered bits
def upn(n: Nat, +nb: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+k:
      match nb:
        case 0n:
          2n+upn(k, 1n)
        case 1n:
          2n+upn(k, 2n)
        case 2n:
          2n+upn(k, 3n)
        case 3n:
          2n+upn(k, 4n)
        case 4n:
          2n+upn(k, 5n)
        case 5n:
          2n+upn(k, 6n)
        case 6n:
          2n+upn(k, 7n)
        case 7n:
          3n+upn(k, 0n)
        case 8n+m:
          1n+upn(k, 0n)

def up_len(+xs: List<&2, Nat>, +acc: Nat, +nb: Nat) -> {PS.ln(LS.nat_of(LS.up(xs, acc, nb))) == upn(PS.ln(xs), nb) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match nb:
        case 0n:
          +a2 = Nat.div(Nat.div(x, 256n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 1n))), upn(PS.ln(xt), 1n), up_len(xt, a2, 1n))
        case 1n:
          +a2 = Nat.div(Nat.div(x, 128n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 2n))), upn(PS.ln(xt), 2n), up_len(xt, a2, 2n))
        case 2n:
          +a2 = Nat.div(Nat.div(x, 64n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 3n))), upn(PS.ln(xt), 3n), up_len(xt, a2, 3n))
        case 3n:
          +a2 = Nat.div(Nat.div(x, 32n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 4n))), upn(PS.ln(xt), 4n), up_len(xt, a2, 4n))
        case 4n:
          +a2 = Nat.div(Nat.div(x, 16n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 5n))), upn(PS.ln(xt), 5n), up_len(xt, a2, 5n))
        case 5n:
          +a2 = Nat.div(Nat.div(x, 8n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 6n))), upn(PS.ln(xt), 6n), up_len(xt, a2, 6n))
        case 6n:
          +a2 = Nat.div(Nat.div(x, 4n), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, 7n))), upn(PS.ln(xt), 7n), up_len(xt, a2, 7n))
        case 7n:
          Equal.cong(Nat, Nat, t => 3n+t, PS.ln(LS.nat_of(LS.up(xt, 0n, 0n))), upn(PS.ln(xt), 0n), up_len(xt, 0n, 0n))
        case 8n+ +m:
          Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.nat_of(LS.up(xt, x, 0n))), upn(PS.ln(xt), 0n), up_len(xt, x, 0n))

# n values below 256 are n bytes
def bytes_of(+n: Nat, +bs: List<&2, U32>, +hl: {PS.ln(LS.nat_of(bs)) == n : Nat}, +h: {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}) -> {FS.bytes_ok(n, bs) == True{} : Bool}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({FS.bytes_ok(0n, Con{x, xt}) == True{} : Bool}, N.succ_zero(PS.ln(LS.nat_of(xt)), hl))
    case 1n+m Nil{}:
      Empty.absurd({FS.bytes_ok(1n+m, Nil{}) == True{} : Bool}, N.zero_succ(m, hl))
    case 1n+ +m Con{+x, +xt}:
      L.and_intro(Nat.is_lt(U32.to_nat(x), 256n), FS.bytes_ok(m, xt), NL.below_head(U32.to_nat(x), LS.nat_of(xt), 256n, h), bytes_of(m, xt, N.succ_inj(PS.ln(LS.nat_of(xt)), m, hl), NL.below_tail(U32.to_nat(x), LS.nat_of(xt), 256n, h)))
