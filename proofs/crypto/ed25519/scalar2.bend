import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/x25519.bend as SX
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/typed/width.bend as WI
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../curve25519/consts.bend as K
import ../curve25519/fieldops.bend as FO
import ../curve25519/cong.bend as G
import ../curve25519/xbits.bend as XB
import ./scalar.bend as SC

# The double-and-add loop over the bits of a byte string (mac), reduce and
# mul_add of src/crypto/ed25519/scalar.bend, for a modulus M = 1 + mm with
# the constant cp = 2^256 - M as a parameter:
#   value(mac(n, bs, s, acc)) == (2^n acc + (bs mod 2^n) s) mod M

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def shift_sc(+k: Nat, +x: Nat) -> {C.shift(k, x) == WD.sc(k, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, x), WD.sc(p, x), shift_sc(p, x))

# bit t joins the low t bits
def low_step(+t: Nat, +V: Nat) -> {C.low(1n+t, V) == Nat.add(C.low(t, V), WD.sc(t, C.bit(C.high(t, V)))) : Nat}:
  match t:
    case 0n:
      N.add_zero(C.bit(V))
    case 1n+ +q:
      +hV = C.half(V)
      +lo = C.low(q, hV)
      +S = WD.sc(q, C.bit(C.high(q, hV)))
      +ih = low_step(q, hV)
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(C.bit(V), Nat.double(z)), C.low(1n+q, hV), Nat.add(lo, S), ih)
      +e2 = M.cong_r(C.bit(V), Nat.double(Nat.add(lo, S)), Nat.add(Nat.double(lo), Nat.double(S)), NA.double_add(lo, S))
      +e3 = Equal.sym(Nat, Nat.add(Nat.add(C.bit(V), Nat.double(lo)), Nat.double(S)), Nat.add(C.bit(V), Nat.add(Nat.double(lo), Nat.double(S))), NA.add_assoc(C.bit(V), Nat.double(lo), Nat.double(S)))
      Equal.trans(Nat, Nat.add(C.bit(V), Nat.double(C.low(1n+q, hV))), Nat.add(C.bit(V), Nat.double(Nat.add(lo, S))), Nat.add(Nat.add(C.bit(V), Nat.double(lo)), Nat.double(S)), e1, Equal.trans(Nat, Nat.add(C.bit(V), Nat.double(Nat.add(lo, S))), Nat.add(C.bit(V), Nat.add(Nat.double(lo), Nat.double(S))), Nat.add(Nat.add(C.bit(V), Nat.double(lo)), Nat.double(S)), e2, e3))

# a byte string's value fits its bit count
def byte_fits(+bs: List<&2, U32>, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {C.high(X.bitlen(bs), FS.value(bs)) == 0n : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      +V = FS.value(bt)
      +hbl = N.le_lt_succ(v(b), 255n, LM.lea_head(b, bt, 255n, hb))
      +e1 = WI.high_comp(X.bitlen(bt), 8n, Nat.add(v(b), C.shift(8n, V)))
      +e2 = Equal.cong(Nat, Nat, z => C.high(X.bitlen(bt), z), C.high(8n, Nat.add(v(b), C.shift(8n, V))), V, WI.high_uniq(8n, v(b), V, hbl))
      Equal.trans(Nat, C.high(Nat.add(8n, X.bitlen(bt)), Nat.add(v(b), C.shift(8n, V))), C.high(X.bitlen(bt), V), 0n, Equal.trans(Nat, C.high(Nat.add(8n, X.bitlen(bt)), Nat.add(v(b), C.shift(8n, V))), C.high(X.bitlen(bt), C.high(8n, Nat.add(v(b), C.shift(8n, V)))), C.high(X.bitlen(bt), V), e1, e2), byte_fits(bt, LM.lea_tail(b, bt, 255n, hb)))

def low_all(+bs: List<&2, U32>, +hb: {LM.lea(bs, 255n) == True{} : Bool}) -> {C.low(X.bitlen(bs), FS.value(bs)) == FS.value(bs) : Nat}:
  WI.low_fit(X.bitlen(bs), FS.value(bs), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.high(X.bitlen(bs), FS.value(bs)), 0n, byte_fits(bs, hb)))

# ---- mac with its constant as a parameter ----

def macg(n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>, +cp: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+ +t:
      +a2 = SC.addg(acc, acc, cp)
      macg(t, bs, s, SC.addg(a2, F.select(X.kbit(bs, t), F.zero(), s), cp), cp)

def mac_eq(+n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>) -> {ESC.mac(n, bs, s, acc) == macg(n, bs, s, acc, ESC.comp_l()) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +t:
      mac_eq(t, bs, s, ESC.addm(ESC.addm(acc, acc), F.select(X.kbit(bs, t), F.zero(), s)))

# the selected addend: bit * s
def sel_okb(+one: Nat, +h1: {one == 1n : Nat}, +kb: U32, +b: Nat, +hk: {v(kb) == b : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +s: List<&2, U32>, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}) -> {LM.okb(32n, F.select(kb, F.zero(), s), 255n) == True{} : Bool}:
  match b:
    case 0n:
      %Equal.sym(U32, kb, 0, XB.u0(kb, hk)) : {LM.okb(32n, F.select(_, F.zero(), s), 255n) == True{} : Bool}
      %Equal.sym(List<&2, U32>, F.select(0, F.zero(), s), F.zero(), FO.select0(one, h1, 32n, F.zero(), s, {==}, hs)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      {==}
    case 1n:
      %Equal.sym(U32, kb, 1, XB.u1(kb, hk)) : {LM.okb(32n, F.select(_, F.zero(), s), 255n) == True{} : Bool}
      %Equal.sym(List<&2, U32>, F.select(1, F.zero(), s), s, FO.select1(one, h1, 32n, F.zero(), s, {==}, hs)) : {LM.okb(32n, _, 255n) == True{} : Bool}
      hs
    case 2n+q:
      Empty.absurd({LM.okb(32n, F.select(kb, F.zero(), s), 255n) == True{} : Bool}, L.false_true(hb))

def sel_val(+one: Nat, +h1: {one == 1n : Nat}, +kb: U32, +b: Nat, +hk: {v(kb) == b : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +s: List<&2, U32>, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}) -> {FS.value(F.select(kb, F.zero(), s)) == Nat.mul(b, FS.value(s)) : Nat}:
  match b:
    case 0n:
      %Equal.sym(U32, kb, 0, XB.u0(kb, hk)) : {FS.value(F.select(_, F.zero(), s)) == 0n : Nat}
      %Equal.sym(List<&2, U32>, F.select(0, F.zero(), s), F.zero(), FO.select0(one, h1, 32n, F.zero(), s, {==}, hs)) : {FS.value(_) == 0n : Nat}
      {==}
    case 1n:
      %Equal.sym(U32, kb, 1, XB.u1(kb, hk)) : {FS.value(F.select(_, F.zero(), s)) == Nat.mul(1n, FS.value(s)) : Nat}
      %Equal.sym(List<&2, U32>, F.select(1, F.zero(), s), s, FO.select1(one, h1, 32n, F.zero(), s, {==}, hs)) : {FS.value(_) == Nat.mul(1n, FS.value(s)) : Nat}
      Equal.sym(Nat, Nat.mul(1n, FS.value(s)), FS.value(s), AR.one_mul(FS.value(s)))
    case 2n+q:
      Empty.absurd({FS.value(F.select(kb, F.zero(), s)) == Nat.mul(2n+q, FS.value(s)) : Nat}, L.false_true(hb))

def sel_lt(+mm: Nat, +b: Nat, +S: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +ls: {Nat.is_lt(S, 1n+mm) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(b, S), 1n+mm) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n:
      L.subst(Nat, z => {Nat.is_lt(z, 1n+mm) == True{} : Bool}, S, Nat.mul(1n, S), Equal.sym(Nat, Nat.mul(1n, S), S, AR.one_mul(S)), ls)
    case 2n+q:
      Empty.absurd({Nat.is_lt(Nat.mul(2n+q, S), 1n+mm) == True{} : Bool}, L.false_true(hb))

def mac_okb(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == SC.T(one) : Nat}, +n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}) -> {LM.okb(32n, macg(n, bs, s, acc, cp), 255n) == True{} : Bool}:
  match n:
    case 0n:
      ha
    case 1n+ +t:
      +a2 = SC.addg(acc, acc, cp)
      +o2 = SC.addg_okb(one, h1, mm, cp, hk, hv, acc, acc, ha, ha)
      +sel = F.select(X.kbit(bs, t), F.zero(), s)
      +os = sel_okb(one, h1, X.kbit(bs, t), SX.kbit(FS.value(bs), t), XB.kbit_val(bs, t, hbs), XB.kbit_le(bs, t, hbs), s, hs)
      mac_okb(one, h1, mm, cp, hk, hv, t, bs, s, SC.addg(a2, sel, cp), hbs, hs, SC.addg_okb(one, h1, mm, cp, hk, hv, a2, sel, o2, os))

def mac_lt(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +h2: {Nat.is_le(Nat.add(1n+mm, 1n+mm), SC.T(one)) == True{} : Bool}, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == SC.T(one) : Nat}, +n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+mm) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}, +la: {Nat.is_lt(FS.value(acc), 1n+mm) == True{} : Bool}) -> G.ceq(mm, FS.value(macg(n, bs, s, acc, cp)), Nat.add(WD.sc(n, FS.value(acc)), Nat.mul(C.low(n, FS.value(bs)), FS.value(s)))):
  match n:
    case 0n:
      G.c_eq(mm, FS.value(acc), Nat.add(FS.value(acc), Nat.mul(0n, FS.value(s))), Equal.sym(Nat, Nat.add(FS.value(acc), 0n), FS.value(acc), N.add_zero(FS.value(acc))))
    case 1n+ +t:
      +P = {1n+mm : Nat}
      +V = FS.value(bs)
      +S = FS.value(s)
      +AA = FS.value(acc)
      +bt = SX.kbit(V, t)
      +a2 = SC.addg(acc, acc, cp)
      +o2 = SC.addg_okb(one, h1, mm, cp, hk, hv, acc, acc, ha, ha)
      +v2 = SC.addg_val(one, h1, mm, h2, cp, hk, hv, acc, acc, ha, ha, la, la)
      +l2 = L.subst(Nat, z => {Nat.is_lt(z, P) == True{} : Bool}, Nat.mod(Nat.add(AA, AA), P), FS.value(a2), Equal.sym(Nat, FS.value(a2), Nat.mod(Nat.add(AA, AA), P), v2), SC.lt_mod(mm, Nat.add(AA, AA)))
      +sel = F.select(X.kbit(bs, t), F.zero(), s)
      +hkv = XB.kbit_val(bs, t, hbs)
      +hkb = XB.kbit_le(bs, t, hbs)
      +os = sel_okb(one, h1, X.kbit(bs, t), bt, hkv, hkb, s, hs)
      +vs = sel_val(one, h1, X.kbit(bs, t), bt, hkv, hkb, s, hs)
      +lsel = L.subst(Nat, z => {Nat.is_lt(z, P) == True{} : Bool}, Nat.mul(bt, S), FS.value(sel), Equal.sym(Nat, FS.value(sel), Nat.mul(bt, S), vs), sel_lt(mm, bt, S, hkb, ls))
      +acc2 = SC.addg(a2, sel, cp)
      +o3 = SC.addg_okb(one, h1, mm, cp, hk, hv, a2, sel, o2, os)
      +v3 = SC.addg_val(one, h1, mm, h2, cp, hk, hv, a2, sel, o2, os, l2, lsel)
      +l3 = L.subst(Nat, z => {Nat.is_lt(z, P) == True{} : Bool}, Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), P), FS.value(acc2), Equal.sym(Nat, FS.value(acc2), Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), P), v3), SC.lt_mod(mm, Nat.add(FS.value(a2), FS.value(sel))))
      +W = Nat.add(Nat.add(AA, AA), Nat.mul(bt, S))
      +c3 = G.c_trans(mm, FS.value(acc2), Nat.add(FS.value(a2), FS.value(sel)), W, G.c_trans(mm, FS.value(acc2), Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), P), Nat.add(FS.value(a2), FS.value(sel)), G.c_eq(mm, FS.value(acc2), Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), P), v3), G.c_mod(mm, Nat.add(FS.value(a2), FS.value(sel)))), G.c_add(mm, FS.value(a2), Nat.add(AA, AA), FS.value(sel), Nat.mul(bt, S), G.c_trans(mm, FS.value(a2), Nat.mod(Nat.add(AA, AA), P), Nat.add(AA, AA), G.c_eq(mm, FS.value(a2), Nat.mod(Nat.add(AA, AA), P), v2), G.c_mod(mm, Nat.add(AA, AA))), G.c_eq(mm, FS.value(sel), Nat.mul(bt, S), vs)))
      +ih = mac_lt(one, h1, mm, h2, cp, hk, hv, t, bs, s, acc2, hbs, hs, ls, o3, l3)
      +lo = C.low(t, V)
      # sc(t, acc2) == sc(t, W) mod M
      +c4 = G.c_trans(mm, WD.sc(t, FS.value(acc2)), Nat.mul(FS.value(acc2), WD.sc(t, 1n)), WD.sc(t, W), G.c_eq(mm, WD.sc(t, FS.value(acc2)), Nat.mul(FS.value(acc2), WD.sc(t, 1n)), Equal.sym(Nat, Nat.mul(FS.value(acc2), WD.sc(t, 1n)), WD.sc(t, FS.value(acc2)), AR.mul_sc(t, FS.value(acc2)))), G.c_trans(mm, Nat.mul(FS.value(acc2), WD.sc(t, 1n)), Nat.mul(W, WD.sc(t, 1n)), WD.sc(t, W), G.c_mul(mm, FS.value(acc2), W, WD.sc(t, 1n), WD.sc(t, 1n), c3, G.c_refl(mm, WD.sc(t, 1n))), G.c_eq(mm, Nat.mul(W, WD.sc(t, 1n)), WD.sc(t, W), AR.mul_sc(t, W))))
      +c5 = G.c_add(mm, WD.sc(t, FS.value(acc2)), WD.sc(t, W), Nat.mul(lo, S), Nat.mul(lo, S), c4, G.c_refl(mm, Nat.mul(lo, S)))
      # sc(t, 2A + b S) + lo S == sc(1+t, A) + low(1+t) S
      +f1 = Equal.sym(Nat, Nat.add(WD.sc(t, Nat.add(AA, AA)), WD.sc(t, Nat.mul(bt, S))), WD.sc(t, W), M.sc_add(t, Nat.add(AA, AA), Nat.mul(bt, S)))
      +f2 = M.cong_add(WD.sc(t, Nat.add(AA, AA)), WD.sc(1n+t, AA), WD.sc(t, Nat.mul(bt, S)), Nat.mul(WD.sc(t, bt), S), Equal.trans(Nat, WD.sc(t, Nat.add(AA, AA)), Nat.add(WD.sc(t, AA), WD.sc(t, AA)), WD.sc(1n+t, AA), Equal.sym(Nat, Nat.add(WD.sc(t, AA), WD.sc(t, AA)), WD.sc(t, Nat.add(AA, AA)), M.sc_add(t, AA, AA)), M.sc_dbl(t, AA)), AR.sc_mul(t, bt, S))
      +f3 = Equal.trans(Nat, Nat.add(Nat.add(WD.sc(1n+t, AA), Nat.mul(WD.sc(t, bt), S)), Nat.mul(lo, S)), Nat.add(WD.sc(1n+t, AA), Nat.add(Nat.mul(WD.sc(t, bt), S), Nat.mul(lo, S))), Nat.add(WD.sc(1n+t, AA), Nat.mul(C.low(1n+t, V), S)), NA.add_assoc(WD.sc(1n+t, AA), Nat.mul(WD.sc(t, bt), S), Nat.mul(lo, S)), M.cong_r(WD.sc(1n+t, AA), Nat.add(Nat.mul(WD.sc(t, bt), S), Nat.mul(lo, S)), Nat.mul(C.low(1n+t, V), S), Equal.trans(Nat, Nat.add(Nat.mul(WD.sc(t, bt), S), Nat.mul(lo, S)), Nat.mul(Nat.add(WD.sc(t, bt), lo), S), Nat.mul(C.low(1n+t, V), S), Equal.sym(Nat, Nat.mul(Nat.add(WD.sc(t, bt), lo), S), Nat.add(Nat.mul(WD.sc(t, bt), S), Nat.mul(lo, S)), NA.mul_add_right(WD.sc(t, bt), lo, S)), Equal.cong(Nat, Nat, z => Nat.mul(z, S), Nat.add(WD.sc(t, bt), lo), C.low(1n+t, V), Equal.trans(Nat, Nat.add(WD.sc(t, bt), lo), Nat.add(lo, WD.sc(t, bt)), C.low(1n+t, V), NA.add_comm(WD.sc(t, bt), lo), Equal.sym(Nat, C.low(1n+t, V), Nat.add(lo, WD.sc(t, bt)), low_step(t, V)))))))
      +f = Equal.trans(Nat, Nat.add(WD.sc(t, W), Nat.mul(lo, S)), Nat.add(Nat.add(WD.sc(1n+t, AA), Nat.mul(WD.sc(t, bt), S)), Nat.mul(lo, S)), Nat.add(WD.sc(1n+t, AA), Nat.mul(C.low(1n+t, V), S)), M.cong_l(WD.sc(t, W), Nat.add(WD.sc(1n+t, AA), Nat.mul(WD.sc(t, bt), S)), Nat.mul(lo, S), Equal.trans(Nat, WD.sc(t, W), Nat.add(WD.sc(t, Nat.add(AA, AA)), WD.sc(t, Nat.mul(bt, S))), Nat.add(WD.sc(1n+t, AA), Nat.mul(WD.sc(t, bt), S)), f1, f2)), f3)
      G.c_trans(mm, FS.value(macg(t, bs, s, acc2, cp)), Nat.add(WD.sc(t, FS.value(acc2)), Nat.mul(lo, S)), Nat.add(WD.sc(1n+t, AA), Nat.mul(C.low(1n+t, V), S)), ih, G.c_trans(mm, Nat.add(WD.sc(t, FS.value(acc2)), Nat.mul(lo, S)), Nat.add(WD.sc(t, W), Nat.mul(lo, S)), Nat.add(WD.sc(1n+t, AA), Nat.mul(C.low(1n+t, V), S)), c5, G.c_eq(mm, Nat.add(WD.sc(t, W), Nat.mul(lo, S)), Nat.add(WD.sc(1n+t, AA), Nat.mul(C.low(1n+t, V), S)), f)))

def mac_below(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +h2: {Nat.is_le(Nat.add(1n+mm, 1n+mm), SC.T(one)) == True{} : Bool}, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == SC.T(one) : Nat}, +n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+mm) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}, +la: {Nat.is_lt(FS.value(acc), 1n+mm) == True{} : Bool}) -> {Nat.is_lt(FS.value(macg(n, bs, s, acc, cp)), 1n+mm) == True{} : Bool}:
  match n:
    case 0n:
      la
    case 1n+ +t:
      +a2 = SC.addg(acc, acc, cp)
      +o2 = SC.addg_okb(one, h1, mm, cp, hk, hv, acc, acc, ha, ha)
      +v2 = SC.addg_val(one, h1, mm, h2, cp, hk, hv, acc, acc, ha, ha, la, la)
      +l2 = L.subst(Nat, z => {Nat.is_lt(z, 1n+mm) == True{} : Bool}, Nat.mod(Nat.add(FS.value(acc), FS.value(acc)), 1n+mm), FS.value(a2), Equal.sym(Nat, FS.value(a2), Nat.mod(Nat.add(FS.value(acc), FS.value(acc)), 1n+mm), v2), SC.lt_mod(mm, Nat.add(FS.value(acc), FS.value(acc))))
      +bt = SX.kbit(FS.value(bs), t)
      +sel = F.select(X.kbit(bs, t), F.zero(), s)
      +hkv = XB.kbit_val(bs, t, hbs)
      +hkb = XB.kbit_le(bs, t, hbs)
      +os = sel_okb(one, h1, X.kbit(bs, t), bt, hkv, hkb, s, hs)
      +vs = sel_val(one, h1, X.kbit(bs, t), bt, hkv, hkb, s, hs)
      +lsel = L.subst(Nat, z => {Nat.is_lt(z, 1n+mm) == True{} : Bool}, Nat.mul(bt, FS.value(s)), FS.value(sel), Equal.sym(Nat, FS.value(sel), Nat.mul(bt, FS.value(s)), vs), sel_lt(mm, bt, FS.value(s), hkb, ls))
      +acc2 = SC.addg(a2, sel, cp)
      +v3 = SC.addg_val(one, h1, mm, h2, cp, hk, hv, a2, sel, o2, os, l2, lsel)
      +l3 = L.subst(Nat, z => {Nat.is_lt(z, 1n+mm) == True{} : Bool}, Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), 1n+mm), FS.value(acc2), Equal.sym(Nat, FS.value(acc2), Nat.mod(Nat.add(FS.value(a2), FS.value(sel)), 1n+mm), v3), SC.lt_mod(mm, Nat.add(FS.value(a2), FS.value(sel))))
      mac_below(one, h1, mm, h2, cp, hk, hv, t, bs, s, acc2, hbs, hs, ls, SC.addg_okb(one, h1, mm, cp, hk, hv, a2, sel, o2, os), l3)

# the exact value: the loop result is reduced
def mac_val(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +h2: {Nat.is_le(Nat.add(1n+mm, 1n+mm), SC.T(one)) == True{} : Bool}, +cp: List<&2, U32>, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(K.valo(one, cp), 1n+mm) == SC.T(one) : Nat}, +n: Nat, +bs: List<&2, U32>, +s: List<&2, U32>, +acc: List<&2, U32>, +hbs: {LM.lea(bs, 255n) == True{} : Bool}, +hs: {LM.okb(32n, s, 255n) == True{} : Bool}, +ls: {Nat.is_lt(FS.value(s), 1n+mm) == True{} : Bool}, +ha: {LM.okb(32n, acc, 255n) == True{} : Bool}, +la: {Nat.is_lt(FS.value(acc), 1n+mm) == True{} : Bool}) -> {FS.value(macg(n, bs, s, acc, cp)) == Nat.mod(Nat.add(WD.sc(n, FS.value(acc)), Nat.mul(C.low(n, FS.value(bs)), FS.value(s))), 1n+mm) : Nat}:
  +r = FS.value(macg(n, bs, s, acc, cp))
  Equal.trans(Nat, r, Nat.mod(r, 1n+mm), Nat.mod(Nat.add(WD.sc(n, FS.value(acc)), Nat.mul(C.low(n, FS.value(bs)), FS.value(s))), 1n+mm), Equal.sym(Nat, Nat.mod(r, 1n+mm), r, NR.mod_of(0n, mm, r, mac_below(one, h1, mm, h2, cp, hk, hv, n, bs, s, acc, hbs, hs, ls, ha, la))), mac_lt(one, h1, mm, h2, cp, hk, hv, n, bs, s, acc, hbs, hs, ls, ha, la))
