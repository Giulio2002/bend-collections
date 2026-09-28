import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32div.bend as UD
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/u64/u64div.bend as PD
import ./num.bend as M

# Limb lists: their value (FS.value, radix 2^8), shapes and bounds, the U32
# steps of the field code, and the carry pass (src/crypto/curve25519/field.bend
# `carry`): value(limbs) + 2^(8 n) carry_out == value(xs) + carry_in, every
# limb below 2^8, and every U32 sum below 2^32 (no wrap; the invariants of
# Fiat-Crypto's carry chains, Erbsen et al. 2019, and of HACL*'s
# Hacl.Spec.Curve25519.Field51 carry_wide).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# 2^(8 len(xs)) x
def sh(xs: List<&2, U32>, +x: Nat) -> Nat:
  match xs:
    case Nil{}:
      x
    case Con{h, t}:
      C.shift(8n, sh(t, x))

# 2^(8 n) x
def shn(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      C.shift(8n, shn(m, x))

# exactly n limbs, each at most b
def okb(n: Nat, xs: List<&2, U32>, +b: Nat) -> Bool:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          True{}
        case Con{x, xt}:
          False{}
    case 1n+m:
      match xs:
        case Nil{}:
          False{}
        case Con{x, xt}:
          Bool.and(Nat.is_le(U32.to_nat(x), b), okb(m, xt, b))

# every limb at most b
def lea(xs: List<&2, U32>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      Bool.and(Nat.is_le(U32.to_nat(x), b), lea(xt, b))

def cl(r: F.Cr) -> List<&2, U32>:
  match r:
    case F.Cr{a, c}:
      a

def cc(r: F.Cr) -> U32:
  match r:
    case F.Cr{a, c}:
      c

# ---- shapes ----

def okb_head(+n: Nat, +h: U32, +t: List<&2, U32>, +b: Nat, +e: {okb(1n+n, Con{h, t}, b) == True{} : Bool}) -> {Nat.is_le(v(h), b) == True{} : Bool}:
  L.and_left(Nat.is_le(v(h), b), okb(n, t, b), e)

def okb_tail(+n: Nat, +h: U32, +t: List<&2, U32>, +b: Nat, +e: {okb(1n+n, Con{h, t}, b) == True{} : Bool}) -> {okb(n, t, b) == True{} : Bool}:
  L.and_right(Nat.is_le(v(h), b), okb(n, t, b), e)

def okb_lea(+n: Nat, +xs: List<&2, U32>, +b: Nat, +e: {okb(n, xs, b) == True{} : Bool}) -> {lea(xs, b) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({lea(Con{x, xt}, b) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({lea(Nil{}, b) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+x, +xt}:
      L.and_intro(Nat.is_le(v(x), b), lea(xt, b), okb_head(m, x, xt, b, e), okb_lea(m, xt, b, okb_tail(m, x, xt, b, e)))

def lea_head(+h: U32, +t: List<&2, U32>, +b: Nat, +e: {lea(Con{h, t}, b) == True{} : Bool}) -> {Nat.is_le(v(h), b) == True{} : Bool}:
  L.and_left(Nat.is_le(v(h), b), lea(t, b), e)

def lea_tail(+h: U32, +t: List<&2, U32>, +b: Nat, +e: {lea(Con{h, t}, b) == True{} : Bool}) -> {lea(t, b) == True{} : Bool}:
  L.and_right(Nat.is_le(v(h), b), lea(t, b), e)

# a weaker bound
def lea_mono(+xs: List<&2, U32>, +b: Nat, +c: Nat, +hb: {Nat.is_le(b, c) == True{} : Bool}, +e: {lea(xs, b) == True{} : Bool}) -> {lea(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      L.and_intro(Nat.is_le(v(x), c), lea(xt, c), N.le_trans(v(x), b, c, lea_head(x, xt, b, e), hb), lea_mono(xt, b, c, hb, lea_tail(x, xt, b, e)))

def sh_okb(+n: Nat, +xs: List<&2, U32>, +b: Nat, +x: Nat, +e: {okb(n, xs, b) == True{} : Bool}) -> {sh(xs, x) == shn(n, x) : Nat}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({sh(Con{y, yt}, x) == x : Nat}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({x == shn(1n+m, x) : Nat}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      Equal.cong(Nat, Nat, z => C.shift(8n, z), sh(yt, x), shn(m, x), sh_okb(m, yt, b, x, okb_tail(m, y, yt, b, e)))

# the spec's tight (bytes_ok 32: limbs below 256) is okb 32 with bound 255
def bytes_okb(+n: Nat, +xs: List<&2, U32>, +e: {FS.bytes_ok(n, xs) == True{} : Bool}) -> {okb(n, xs, 255n) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({okb(0n, Con{y, yt}, 255n) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({okb(1n+m, Nil{}, 255n) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      +h = L.and_left(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt), e)
      +t = L.and_right(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt), e)
      L.and_intro(Nat.is_le(v(y), 255n), okb(m, yt, 255n), N.lt_succ_le(v(y), 255n, h), bytes_okb(m, yt, t))

def okb_bytes(+n: Nat, +xs: List<&2, U32>, +e: {okb(n, xs, 255n) == True{} : Bool}) -> {FS.bytes_ok(n, xs) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({FS.bytes_ok(0n, Con{y, yt}) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({FS.bytes_ok(1n+m, Nil{}) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      L.and_intro(Nat.is_lt(v(y), 256n), FS.bytes_ok(m, yt), N.le_lt_succ(v(y), 255n, okb_head(m, y, yt, 255n, e)), okb_bytes(m, yt, okb_tail(m, y, yt, 255n, e)))

# ---- constants ----

def k256(+one: Nat, +h1: {one == 1n : Nat}) -> {256n == WD.sc(8n, one) : Nat}:
  L.subst(Nat, o => {256n == WD.sc(8n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})

def sc_pos1(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(0n, WD.sc(k, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(0n, WD.sc(k, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WD.sc_pos(k))

# 2^k < 2^(k+1)
def sc_lt_succ(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(WD.sc(k, one), WD.sc(1n+k, one)) == True{} : Bool}:
  +x = WD.sc(k, one)
  +a = N.lt_add_left(0n, x, x, sc_pos1(k, one, h1))
  %N.add_zero(x) : {Nat.is_lt(_, WD.sc(1n+k, one)) == True{} : Bool}
  %M.sc_dbl(k, one) : {Nat.is_lt(Nat.add(x, 0n), _) == True{} : Bool}
  a

# 2^a < 2^(d + 1 + a)
def sc_lt(+d: Nat, +a: Nat, +one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(WD.sc(a, one), WD.sc(Nat.add(d, 1n+a), one)) == True{} : Bool}:
  N.lt_le_trans(WD.sc(a, one), WD.sc(1n+a, one), WD.sc(Nat.add(d, 1n+a), one), sc_lt_succ(a, one, h1), M.sc_mono(d, 1n+a, one))

# ---- U32 steps ----

def add_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.add(v(x), v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.add(x, y)) == Nat.add(v(x), v(y)) : Nat}:
  PD.add32(one, h1, x, y, h)

def mul_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +h: {Nat.is_lt(Nat.mul(v(x), v(y)), WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.mul(x, y)) == Nat.mul(v(x), v(y)) : Nat}:
  PD.mul32(one, h1, x, y, h)

def mod256(+x: U32) -> {v(U32.mod(x, 256)) == Nat.mod(v(x), 256n) : Nat}:
  UD.mod_nat(x, 256, {==})

def div256(+x: U32) -> {v(U32.div(x, 256)) == Nat.div(v(x), 256n) : Nat}:
  UD.div_nat(x, 256, {==})

def m256(+x: Nat) -> {Nat.mul(x, 256n) == C.shift(8n, x) : Nat}:
  PD.mul_pow(1n, {==}, 8n, x, 256n, {==})

# n == (n mod 256) + 2^8 (n div 256)
def dm256(+n: Nat) -> {Nat.add(Nat.mod(n, 256n), C.shift(8n, Nat.div(n, 256n))) == n : Nat}:
  +e = Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 256n), 256n), Nat.mod(n, 256n)), NR.dm_eq(255n, n))
  +e2 = Equal.trans(Nat, Nat.add(Nat.mod(n, 256n), C.shift(8n, Nat.div(n, 256n))), Nat.add(Nat.mod(n, 256n), Nat.mul(Nat.div(n, 256n), 256n)), Nat.add(Nat.mul(Nat.div(n, 256n), 256n), Nat.mod(n, 256n)), M.cong_r(Nat.mod(n, 256n), C.shift(8n, Nat.div(n, 256n)), Nat.mul(Nat.div(n, 256n), 256n), Equal.sym(Nat, Nat.mul(Nat.div(n, 256n), 256n), C.shift(8n, Nat.div(n, 256n)), m256(Nat.div(n, 256n)))), NA.add_comm(Nat.mod(n, 256n), Nat.mul(Nat.div(n, 256n), 256n)))
  Equal.trans(Nat, Nat.add(Nat.mod(n, 256n), C.shift(8n, Nat.div(n, 256n))), Nat.add(Nat.mul(Nat.div(n, 256n), 256n), Nat.mod(n, 256n)), n, e2, e)

# a U32 split into its low byte and the rest
def split_v(+s: U32) -> {Nat.add(v(U32.mod(s, 256)), C.shift(8n, v(U32.div(s, 256)))) == v(s) : Nat}:
  %Equal.sym(Nat, v(U32.mod(s, 256)), Nat.mod(v(s), 256n), mod256(s)) : {Nat.add(_, C.shift(8n, v(U32.div(s, 256)))) == v(s) : Nat}
  %Equal.sym(Nat, v(U32.div(s, 256)), Nat.div(v(s), 256n), div256(s)) : {Nat.add(Nat.mod(v(s), 256n), C.shift(8n, _)) == v(s) : Nat}
  dm256(v(s))

def lo_le(+s: U32) -> {Nat.is_le(v(U32.mod(s, 256)), 255n) == True{} : Bool}:
  %Equal.sym(Nat, v(U32.mod(s, 256)), Nat.mod(v(s), 256n), mod256(s)) : {Nat.is_le(_, 255n) == True{} : Bool}
  N.lt_succ_le(Nat.mod(v(s), 256n), 255n, NR.dm_lt(255n, v(s)))

# (s div 256) < 2^k when s < 2^(k + 8)
def hi_lt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +s: U32, +h: {Nat.is_lt(v(s), WD.sc(Nat.add(k, 8n), one)) == True{} : Bool}) -> {Nat.is_lt(v(U32.div(s, 256)), WD.sc(k, one)) == True{} : Bool}:
  %Equal.sym(Nat, v(U32.div(s, 256)), Nat.div(v(s), 256n), div256(s)) : {Nat.is_lt(_, WD.sc(k, one)) == True{} : Bool}
  +n = v(s)
  +q = Nat.div(n, 256n)
  +r = Nat.mod(n, 256n)
  +e = NR.dm_eq(255n, n)
  +h2 = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(Nat.add(k, 8n), one)) == True{} : Bool}, n, Nat.add(Nat.mul(q, 256n), r), e, h)
  +h3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(q, 256n), r), z) == True{} : Bool}, WD.sc(Nat.add(k, 8n), one), WD.sc(k, WD.sc(8n, one)), AR.sc_idx(k, 8n, one), h2)
  +h4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(q, 256n), r), WD.sc(k, z)) == True{} : Bool}, WD.sc(8n, one), 256n, Equal.sym(Nat, 256n, WD.sc(8n, one), k256(one, h1)), h3)
  AR.quot_lt(k, one, h1, q, 256n, r, h4)

# ---- the carry pass ----

def cl_con(+l: U32, +r: F.Cr) -> {cl(F.carry_con(l, r)) == Con{l, cl(r)} : List<&2, U32>}:
  match r:
    case F.Cr{a, c}:
      {==}

def cc_con(+l: U32, +r: F.Cr) -> {cc(F.carry_con(l, r)) == cc(r) : U32}:
  match r:
    case F.Cr{a, c}:
      {==}

# carry-in at most 2^21 and a limb at most 2^28: their sum is below 2^29
def s_lt(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +hx: {Nat.is_le(v(x), WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(v(x), v(c)), WD.sc(29n, one)) == True{} : Bool}:
  +c28 = N.lt_le(v(c), WD.sc(28n, one), N.le_lt_trans(v(c), WD.sc(21n, one), WD.sc(28n, one), hc, sc_lt(6n, 21n, one, h1)))
  +lt = N.le_lt_trans(Nat.add(v(x), v(c)), Nat.add(WD.sc(28n, one), WD.sc(21n, one)), Nat.add(WD.sc(28n, one), WD.sc(28n, one)), M.le_add2(v(x), v(c), WD.sc(28n, one), WD.sc(21n, one), hx, hc), N.lt_add_left(WD.sc(21n, one), WD.sc(28n, one), WD.sc(28n, one), sc_lt(6n, 21n, one, h1)))
  %M.sc_dbl(28n, one) : {Nat.is_lt(Nat.add(v(x), v(c)), _) == True{} : Bool}
  lt

def s_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +hx: {Nat.is_le(v(x), WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {v(U32.add(x, c)) == Nat.add(v(x), v(c)) : Nat}:
  add_v(one, h1, x, c, N.lt_trans(Nat.add(v(x), v(c)), WD.sc(29n, one), WD.sc(32n, one), s_lt(one, h1, x, c, hx, hc), sc_lt(2n, 29n, one, h1)))

def c_next(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +c: U32, +hx: {Nat.is_le(v(x), WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {Nat.is_le(v(U32.div(U32.add(x, c), 256)), WD.sc(21n, one)) == True{} : Bool}:
  +s = U32.add(x, c)
  +hs = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(29n, one)) == True{} : Bool}, Nat.add(v(x), v(c)), v(s), Equal.sym(Nat, v(s), Nat.add(v(x), v(c)), s_v(one, h1, x, c, hx, hc)), s_lt(one, h1, x, c, hx, hc))
  N.lt_le(v(U32.div(s, 256)), WD.sc(21n, one), hi_lt(21n, one, h1, s, hs))

# value(limbs) + 2^(8 n) carry_out == value(xs) + carry_in
def carry_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +c: U32, +hx: {lea(xs, WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {Nat.add(FS.value(cl(F.carry(xs, c))), sh(xs, v(cc(F.carry(xs, c))))) == Nat.add(FS.value(xs), v(c)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hh = lea_head(h, t, WD.sc(28n, one), hx)
      +ht = lea_tail(h, t, WD.sc(28n, one), hx)
      +s = U32.add(h, c)
      +lo = U32.mod(s, 256)
      +hi = U32.div(s, 256)
      +r = F.carry(t, hi)
      +ih = carry_val(one, h1, t, hi, ht, c_next(one, h1, h, c, hh, hc))
      %Equal.sym(List<&2, U32>, cl(F.carry_con(lo, r)), Con{lo, cl(r)}, cl_con(lo, r)) : {Nat.add(FS.value(_), C.shift(8n, sh(t, v(cc(F.carry_con(lo, r)))))) == Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)) : Nat}
      %Equal.sym(U32, cc(F.carry_con(lo, r)), cc(r), cc_con(lo, r)) : {Nat.add(FS.value(Con{lo, cl(r)}), C.shift(8n, sh(t, v(_)))) == Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)) : Nat}
      +A = FS.value(cl(r))
      +B = sh(t, v(cc(r)))
      +e1 = Equal.trans(Nat, Nat.add(Nat.add(v(lo), C.shift(8n, A)), C.shift(8n, B)), Nat.add(v(lo), Nat.add(C.shift(8n, A), C.shift(8n, B))), Nat.add(v(lo), C.shift(8n, Nat.add(A, B))), NA.add_assoc(v(lo), C.shift(8n, A), C.shift(8n, B)), M.cong_r(v(lo), Nat.add(C.shift(8n, A), C.shift(8n, B)), C.shift(8n, Nat.add(A, B)), M.sc_add(8n, A, B)))
      +e2 = M.cong_r(v(lo), C.shift(8n, Nat.add(A, B)), C.shift(8n, Nat.add(FS.value(t), v(hi))), M.cong_sc(8n, Nat.add(A, B), Nat.add(FS.value(t), v(hi)), ih))
      +e3 = Equal.trans(Nat, Nat.add(v(lo), C.shift(8n, Nat.add(FS.value(t), v(hi)))), Nat.add(v(lo), Nat.add(C.shift(8n, FS.value(t)), C.shift(8n, v(hi)))), Nat.add(Nat.add(v(lo), C.shift(8n, v(hi))), C.shift(8n, FS.value(t))), M.cong_r(v(lo), C.shift(8n, Nat.add(FS.value(t), v(hi))), Nat.add(C.shift(8n, FS.value(t)), C.shift(8n, v(hi))), Equal.sym(Nat, Nat.add(C.shift(8n, FS.value(t)), C.shift(8n, v(hi))), C.shift(8n, Nat.add(FS.value(t), v(hi))), M.sc_add(8n, FS.value(t), v(hi)))),
        Equal.trans(Nat, Nat.add(v(lo), Nat.add(C.shift(8n, FS.value(t)), C.shift(8n, v(hi)))), Nat.add(v(lo), Nat.add(C.shift(8n, v(hi)), C.shift(8n, FS.value(t)))), Nat.add(Nat.add(v(lo), C.shift(8n, v(hi))), C.shift(8n, FS.value(t))), M.cong_r(v(lo), Nat.add(C.shift(8n, FS.value(t)), C.shift(8n, v(hi))), Nat.add(C.shift(8n, v(hi)), C.shift(8n, FS.value(t))), NA.add_comm(C.shift(8n, FS.value(t)), C.shift(8n, v(hi)))), Equal.sym(Nat, Nat.add(Nat.add(v(lo), C.shift(8n, v(hi))), C.shift(8n, FS.value(t))), Nat.add(v(lo), Nat.add(C.shift(8n, v(hi)), C.shift(8n, FS.value(t)))), NA.add_assoc(v(lo), C.shift(8n, v(hi)), C.shift(8n, FS.value(t))))))
      +e4 = M.cong_l(Nat.add(v(lo), C.shift(8n, v(hi))), v(s), C.shift(8n, FS.value(t)), split_v(s))
      +e5 = M.cong_l(v(s), Nat.add(v(h), v(c)), C.shift(8n, FS.value(t)), s_v(one, h1, h, c, hh, hc))
      +e6 = Equal.trans(Nat, Nat.add(Nat.add(v(h), v(c)), C.shift(8n, FS.value(t))), Nat.add(v(h), Nat.add(v(c), C.shift(8n, FS.value(t)))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), NA.add_assoc(v(h), v(c), C.shift(8n, FS.value(t))),
        Equal.trans(Nat, Nat.add(v(h), Nat.add(v(c), C.shift(8n, FS.value(t)))), Nat.add(v(h), Nat.add(C.shift(8n, FS.value(t)), v(c))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), M.cong_r(v(h), Nat.add(v(c), C.shift(8n, FS.value(t))), Nat.add(C.shift(8n, FS.value(t)), v(c)), NA.add_comm(v(c), C.shift(8n, FS.value(t)))), Equal.sym(Nat, Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), Nat.add(v(h), Nat.add(C.shift(8n, FS.value(t)), v(c))), NA.add_assoc(v(h), C.shift(8n, FS.value(t)), v(c)))))
      Equal.trans(Nat, Nat.add(Nat.add(v(lo), C.shift(8n, A)), C.shift(8n, B)), Nat.add(v(lo), C.shift(8n, Nat.add(A, B))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), e1,
        Equal.trans(Nat, Nat.add(v(lo), C.shift(8n, Nat.add(A, B))), Nat.add(v(lo), C.shift(8n, Nat.add(FS.value(t), v(hi)))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), e2,
          Equal.trans(Nat, Nat.add(v(lo), C.shift(8n, Nat.add(FS.value(t), v(hi)))), Nat.add(Nat.add(v(lo), C.shift(8n, v(hi))), C.shift(8n, FS.value(t))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), e3,
            Equal.trans(Nat, Nat.add(Nat.add(v(lo), C.shift(8n, v(hi))), C.shift(8n, FS.value(t))), Nat.add(v(s), C.shift(8n, FS.value(t))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), e4,
              Equal.trans(Nat, Nat.add(v(s), C.shift(8n, FS.value(t))), Nat.add(Nat.add(v(h), v(c)), C.shift(8n, FS.value(t))), Nat.add(Nat.add(v(h), C.shift(8n, FS.value(t))), v(c)), e5, e6)))))

# every output limb below 2^8, the same count
def carry_ok(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +c: U32, +hn: {okb(n, xs, WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {okb(n, cl(F.carry(xs, c)), 255n) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({okb(0n, cl(F.carry(Con{y, yt}, c)), 255n) == True{} : Bool}, L.false_true(hn))
    case 1n+m Nil{}:
      Empty.absurd({okb(1n+m, cl(F.carry(Nil{}, c)), 255n) == True{} : Bool}, L.false_true(hn))
    case 1n+ +m Con{+h, +t}:
      +hh = okb_head(m, h, t, WD.sc(28n, one), hn)
      +ht = okb_tail(m, h, t, WD.sc(28n, one), hn)
      +s = U32.add(h, c)
      +lo = U32.mod(s, 256)
      +r = F.carry(t, U32.div(s, 256))
      %Equal.sym(List<&2, U32>, cl(F.carry_con(lo, r)), Con{lo, cl(r)}, cl_con(lo, r)) : {okb(1n+m, _, 255n) == True{} : Bool}
      L.and_intro(Nat.is_le(v(lo), 255n), okb(m, cl(r), 255n), lo_le(s), carry_ok(one, h1, m, t, U32.div(s, 256), ht, c_next(one, h1, h, c, hh, hc)))

# the carry out is at most 2^21
def carry_cb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +c: U32, +hx: {lea(xs, WD.sc(28n, one)) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {Nat.is_le(v(cc(F.carry(xs, c))), WD.sc(21n, one)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hc
    case Con{+h, +t}:
      +hh = lea_head(h, t, WD.sc(28n, one), hx)
      +ht = lea_tail(h, t, WD.sc(28n, one), hx)
      +s = U32.add(h, c)
      +lo = U32.mod(s, 256)
      +r = F.carry(t, U32.div(s, 256))
      %Equal.sym(U32, cc(F.carry_con(lo, r)), cc(r), cc_con(lo, r)) : {Nat.is_le(v(_), WD.sc(21n, one)) == True{} : Bool}
      carry_cb(one, h1, t, U32.div(s, 256), ht, c_next(one, h1, h, c, hh, hc))
