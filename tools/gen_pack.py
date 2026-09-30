#!/usr/bin/env python3
"""Write the byte/limb regrouping of src/crypto/curve25519/limbs.bend (pk, up:
the block between the GEN-PACK markers) and proofs/crypto/fe/pack.bend.

pk reads bytes into 17-bit limbs and up writes 17-bit limbs as bytes through
a bit buffer whose size is matched literally, so every shift is a closed
small constant; this script writes one case per buffer size, and the same
cases in the proofs.

  python3 tools/gen_pack.py            rewrite both
  python3 tools/gen_pack.py --check    fail if either is out of date
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src/crypto/curve25519/limbs.bend'
PRF = ROOT / 'proofs/crypto/fe/pack.bend'
BEGIN, END = '# ---- GEN-PACK begin (tools/gen_pack.py) ----\n', '# ---- GEN-PACK end ----\n'


def src():
    o = ['''
# 2^n x
def shl(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      Nat.double(shl(m, x))

# a byte as a Nat (below 256 whatever the U32 holds)
def b8(b: U32) -> Nat:
  Nat.mod(U32.to_nat(b), 256n)

# the 17-bit limbs of a byte string, least significant first: acc holds
# the nb low bits not yet written (nb <= 16). A byte enters above them;
# once 17 bits are there, a limb leaves (the buffer and the byte's low
# 17 - nb bits) and the byte's other bits stay. The last limb holds the
# bits left over.
def pk(bs: List<&2, U32>, acc: Nat, +nb: Nat) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Con{acc, Nil{}}
    case Con{b, bt}:
      match nb:''']
    for i in range(9):
        o.append('        case %dn:\n          pk(bt, Nat.add(acc, shl(%dn, b8(b))), %dn)' % (i, i, i + 8))
    for j in range(9, 17):
        K = 1 << (17 - j)
        o.append('        case %dn:\n          +B = b8(b)\n          Con{Nat.add(acc, shl(%dn, Nat.mod(B, %dn))), pk(bt, Nat.div(B, %dn), %dn)}' % (j, j, K, K, j - 9))
    o.append('''        case 17n+m:
          Con{acc, pk(bt, b8(b), 8n)}

def byte(+a: Nat) -> U32:
  U32.from_nat(Nat.mod(a, 256n))

# the bytes of 17-bit limbs, least significant first: acc holds the nb low
# bits not yet written (nb <= 7). The limb's low 8 - nb bits complete a
# byte, its next 8 bits are a byte, and the rest stays (nb + 1 bits; at
# nb = 7 they are a third byte). The last byte holds the bits left over.
def up(xs: List<&2, Nat>, acc: Nat, +nb: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Con{byte(acc), Nil{}}
    case Con{+x, xt}:
      match nb:''')
    for i in range(7):
        K = 1 << (8 - i)
        o.append('        case %dn:\n          +x1 = Nat.div(x, %dn)\n          Con{byte(Nat.add(acc, shl(%dn, Nat.mod(x, %dn)))), Con{byte(x1), up(xt, Nat.div(x1, 256n), %dn)}}' % (i, K, i, K, i + 1))
    o.append('''        case 7n:
          +x1 = Nat.div(x, 2n)
          Con{byte(Nat.add(acc, shl(7n, Nat.mod(x, 2n)))), Con{byte(x1), Con{byte(Nat.div(x1, 256n)), up(xt, 0n, 0n)}}}
        case 8n+m:
          Con{byte(acc), up(xt, x, 0n)}

''')
    return '\n'.join(o)


HDR = '''import Base
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

'''


def proofs():
    o = [HDR]
    # pk_val
    o.append('''# the value, for bytes below 256
def pk_val(+bs: List<&2, U32>, +acc: Nat, +nb: Nat, +hb: {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}, +hn: {Nat.is_le(nb, 16n) == True{} : Bool}) -> {FV.lv(LS.pk(bs, acc, nb)) == Nat.add(acc, WD.sc(nb, FS.value(bs))) : Nat}:
  match bs:
    case Nil{}:
      M.cong_r(acc, 0n, WD.sc(nb, 0n), sy(WD.sc(nb, 0n), 0n, sc_zero(nb)))
    case Con{+b, +bt}:
      match nb:''')
    pre = '''          +B = LS.b8(b)
          +V = FS.value(bt)
          +ht = NL.below_tail(U32.to_nat(b), LS.nat_of(bt), 256n, hb)
          +eB = b8_id(b, NL.below_head(U32.to_nat(b), LS.nat_of(bt), 256n, hb))
'''
    for i in range(9):
        o.append('        case %dn:\n' % i + pre + '''          +P = FV.lv(LS.pk(bt, Nat.add(acc, LS.shl(%dn, B)), %dn))
          L.subst(Nat, z => {P == Nat.add(acc, WD.sc(%dn, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, lo(8n, %dn, acc, B, V, P, pk_val(bt, Nat.add(acc, LS.shl(%dn, B)), %dn, ht, {==})))''' % (i, i + 8, i, i, i, i + 8))
    for j in range(9, 17):
        k = 17 - j
        K = 1 << k
        o.append('        case %dn:\n' % j + pre + '''          +r = Nat.mod(B, %dn)
          +q = Nat.div(B, %dn)
          +a = Nat.add(acc, LS.shl(%dn, r))
          +P = FV.lv(LS.pk(bt, q, %dn))
          +x1 = emitw(17n, a, P, q, WD.sc(%dn, V), pk_val(bt, q, %dn, ht, {==}))
          +x2 = emitv(%dn, acc, r, WD.sc(%dn, q), B, WD.sc(8n, V), dmk(%dn, B))
          L.subst(Nat, z => {Nat.add(a, WD.sc(17n, P)) == Nat.add(acc, WD.sc(%dn, Nat.add(z, WD.sc(8n, V)))) : Nat}, B, U32.to_nat(b), eB, tr(Nat.add(a, WD.sc(17n, P)), Nat.add(a, Nat.add(WD.sc(17n, q), WD.sc(17n, WD.sc(%dn, V)))), Nat.add(acc, WD.sc(%dn, Nat.add(B, WD.sc(8n, V)))), x1, x2))''' % (K, K, j, j - 9, j - 9, j - 9, j, k, k, j, j - 9, j))
    o.append('''        case 17n+m:
          Empty.absurd({FV.lv(LS.pk(Con{b, bt}, acc, 17n+m)) == Nat.add(acc, WD.sc(17n+m, FS.value(Con{b, bt}))) : Nat}, L.false_true(hn))

# every limb is below 2^17, for a buffer acc < 2^nb
def pk_below(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +acc: Nat, +nb: Nat, +ha: {Nat.is_lt(acc, WD.sc(nb, one)) == True{} : Bool}, +hn: {Nat.is_le(nb, 16n) == True{} : Bool}) -> {FV.below(LS.pk(bs, acc, nb), WD.sc(17n, one)) == True{} : Bool}:
  match bs:
    case Nil{}:
      NL.below_con(acc, Nil{}, WD.sc(17n, one), N.lt_le_trans(acc, WD.sc(nb, one), WD.sc(17n, one), ha, sc_up(nb, 17n, one, N.le_trans(nb, 16n, 17n, hn, {==}))), {==})
    case Con{+b, +bt}:
      match nb:''')
    for i in range(9):
        o.append('''        case %dn:
          +B = LS.b8(b)
          pk_below(one, h1, bt, Nat.add(acc, LS.shl(%dn, B)), %dn, lt_in(one, h1, %dn, 8n, acc, B, ha, b8_lt1(one, h1, b)), {==})''' % (i, i, i + 8, i))
    for j in range(9, 17):
        k = 17 - j
        K = 1 << k
        o.append('''        case %dn:
          +B = LS.b8(b)
          +r = Nat.mod(B, %dn)
          +q = Nat.div(B, %dn)
          NL.below_con(Nat.add(acc, LS.shl(%dn, r)), LS.pk(bt, q, %dn), WD.sc(17n, one), lt_in(one, h1, %dn, %dn, acc, r, ha, modk_lt(one, h1, %dn, B)), pk_below(one, h1, bt, q, %dn, div_ltk(%dn, B, WD.sc(%dn, one), b8_lt1(one, h1, b)), {==}))''' % (j, K, K, j, j - 9, j, k, k, j - 9, k, j - 9))
    o.append('''        case 17n+m:
          Empty.absurd({FV.below(LS.pk(Con{b, bt}, acc, 17n+m), WD.sc(17n, one)) == True{} : Bool}, L.false_true(hn))

# the number of limbs of n bytes entering above nb buffered bits
def pkn(n: Nat, +nb: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+k:
      match nb:''')
    for i in range(9):
        o.append('        case %dn:\n          pkn(k, %dn)' % (i, i + 8))
    for j in range(9, 17):
        o.append('        case %dn:\n          1n+pkn(k, %dn)' % (j, j - 9))
    o.append('''        case 17n+m:
          1n+pkn(k, 8n)

def pk_len(+bs: List<&2, U32>, +acc: Nat, +nb: Nat) -> {PS.ln(LS.pk(bs, acc, nb)) == pkn(PS.ln(LS.nat_of(bs)), nb) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      match nb:''')
    for i in range(9):
        o.append('        case %dn:\n          pk_len(bt, Nat.add(acc, LS.shl(%dn, LS.b8(b))), %dn)' % (i, i, i + 8))
    for j in range(9, 17):
        K = 1 << (17 - j)
        o.append('        case %dn:\n          +q = Nat.div(LS.b8(b), %dn)\n          N.succ_cong(PS.ln(LS.pk(bt, q, %dn)), pkn(PS.ln(LS.nat_of(bt)), %dn), pk_len(bt, q, %dn))' % (j, K, j - 9, j - 9, j - 9))
    o.append('''        case 17n+m:
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
      match nb:''')
    upre = '''          +V = FV.lv(xt)
          +hX = NL.below_head(x, xt, WD.sc(17n, one), hx)
          +ht = NL.below_tail(x, xt, WD.sc(17n, one), hx)
'''
    for i in range(7):
        k = 8 - i
        K = 1 << k
        o.append('        case %dn:\n' % i + upre + '''          +r = Nat.mod(x, %dn)
          +x1 = Nat.div(x, %dn)
          +c = Nat.add(acc, LS.shl(%dn, r))
          +hx1 = div_ltk(%dn, x, WD.sc(%dn, one), hX)
          +W = FS.value(LS.up(xt, Nat.div(x1, 256n), %dn))
          +ih = up_val(one, h1, xt, Nat.div(x1, 256n), %dn, ht, div_ltk(8n, x1, WD.sc(%dn, one), hx1), {==})
          +e0 = byte_id(one, h1, c, lt_in(one, h1, %dn, %dn, acc, r, ha, modk_lt(one, h1, %dn, x)))
          +e1 = bstep(x1, W, WD.sc(%dn, V), ih)
          tr(FS.value(LS.up(Con{x, xt}, acc, %dn)), Nat.add(c, Nat.add(WD.sc(8n, x1), WD.sc(8n, WD.sc(8n, WD.sc(%dn, V))))), Nat.add(acc, WD.sc(%dn, Nat.add(x, C.shift(17n, V)))), upv(U32.to_nat(LS.byte(c)), c, Nat.add(U32.to_nat(LS.byte(x1)), WD.sc(8n, W)), x1, WD.sc(8n, WD.sc(%dn, V)), e0, e1), emitv(%dn, acc, r, WD.sc(%dn, x1), x, WD.sc(17n, V), dmk(%dn, x)))''' % (K, K, i, k, 9 + i, i + 1, i + 1, i + 1, i, k, k, i + 1, i, i + 1, i, i + 1, i, k, k))
    o.append('        case 7n:\n' + upre + '''          +r = Nat.mod(x, 2n)
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
      match nb:''')
    for i in range(7):
        K = 1 << (8 - i)
        o.append('''        case %dn:
          +x1 = Nat.div(x, %dn)
          +c = Nat.add(acc, LS.shl(%dn, Nat.mod(x, %dn)))
          +T = LS.nat_of(LS.up(xt, Nat.div(x1, 256n), %dn))
          NL.below_con(U32.to_nat(LS.byte(c)), Con{U32.to_nat(LS.byte(x1)), T}, 256n, byte_lt(c), NL.below_con(U32.to_nat(LS.byte(x1)), T, 256n, byte_lt(x1), up_below(xt, Nat.div(x1, 256n), %dn)))''' % (i, K, i, K, i + 1, i + 1))
    o.append('''        case 7n:
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
      match nb:''')
    for i in range(7):
        o.append('        case %dn:\n          2n+upn(k, %dn)' % (i, i + 1))
    o.append('''        case 7n:
          3n+upn(k, 0n)
        case 8n+m:
          1n+upn(k, 0n)

def up_len(+xs: List<&2, Nat>, +acc: Nat, +nb: Nat) -> {PS.ln(LS.nat_of(LS.up(xs, acc, nb))) == upn(PS.ln(xs), nb) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match nb:''')
    for i in range(7):
        K = 1 << (8 - i)
        o.append('''        case %dn:
          +a2 = Nat.div(Nat.div(x, %dn), 256n)
          Equal.cong(Nat, Nat, t => 2n+t, PS.ln(LS.nat_of(LS.up(xt, a2, %dn))), upn(PS.ln(xt), %dn), up_len(xt, a2, %dn))''' % (i, K, i + 1, i + 1, i + 1))
    o.append('''        case 7n:
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
''')
    return '\n'.join(o)


def main():
    s = SRC.read_text()
    a, b = s.index(BEGIN) + len(BEGIN), s.index(END)
    news = s[:a] + src() + s[b:]
    newp = proofs()
    if '--check' in sys.argv:
        if s != news or PRF.read_text() != newp:
            print('limbs.bend or pack.bend is out of date: run python3 tools/gen_pack.py')
            return 1
        return 0
    SRC.write_text(news)
    PRF.write_text(newp)
    return 0


if __name__ == '__main__':
    sys.exit(main())
