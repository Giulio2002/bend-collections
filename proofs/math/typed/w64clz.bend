import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/u32.bend as U
import ../natural/arith.bend as NR
import ../natural/bits.bend as BT
import ./natfuel.bend as NF
import ./w64sqrt.bend as W64S
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./width.bend as WW
import ./u32laws.bend as LW

# Leading zeros: bitlen(x) on a word is M.bit_length(x) (a binary search on
# the top bit, each step halving the width: 16, 8, 4, 2, 1), and clz(a) is
# 64 - bit_length(a) (Mathlib Nat.size / Nat.log2 characterisation
# 2^(L - 1) <= n < 2^L, via bit_length(n) == k + bit_length(n / 2^k)).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

# bit_length(1 + np) == 1 + bit_length(half(1 + np))
def bl_succ(+np: Nat) -> {M.bit_length(1n+np) == 1n+M.bit_length(C.half(1n+np)) : Nat}:
  +d = Nat.div(1n+np, 2n)
  +hd = NF.half_le(np)
  +e1 = Equal.trans(Nat, M.bit_length_go(np, d, 1n), 1n+M.bit_length_go(np, d, 0n), 1n+M.bit_length_go(d, d, 0n), BT.go_acc(np, d, 0n), Equal.cong(Nat, Nat, z => 1n+z, M.bit_length_go(np, d, 0n), M.bit_length_go(d, d, 0n), NF.bl_fuel(np, d, d, 0n, NF.bends_self(np, d, hd), NF.bends_self(d, d, N.le_refl(d)))))
  Equal.trans(Nat, M.bit_length(1n+np), 1n+M.bit_length(d), 1n+M.bit_length(C.half(1n+np)), e1, Equal.cong(Nat, Nat, z => 1n+M.bit_length(z), d, C.half(1n+np), Equal.sym(Nat, C.half(1n+np), d, WA.half_div(1n+np))))

def high0(+p: Nat) -> {C.high(p, 0n) == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      high0(q)

# high(k, n) >= 1: bit_length(n) == k + bit_length(high(k, n))
def bl_high(+k: Nat, +n: Nat, +h: {Nat.is_le(1n, C.high(k, n)) == True{} : Bool}) -> {M.bit_length(n) == Nat.add(k, M.bit_length(C.high(k, n))) : Nat}:
  match k n:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      Empty.absurd({M.bit_length(0n) == Nat.add(1n+p, M.bit_length(C.high(1n+p, 0n))) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, C.high(p, 0n), 0n, high0(p), h))))
    case 1n+ +p 1n+ +np:
      Equal.trans(Nat, M.bit_length(1n+np), 1n+M.bit_length(C.half(1n+np)), 1n+Nat.add(p, M.bit_length(C.high(p, C.half(1n+np)))), bl_succ(np), Equal.cong(Nat, Nat, z => 1n+z, M.bit_length(C.half(1n+np)), Nat.add(p, M.bit_length(C.high(p, C.half(1n+np)))), bl_high(p, C.half(1n+np), h)))

def hp_c(+k: Nat, +y: Nat, +h: {Nat.is_le(C.pow2(k), y) == True{} : Bool}, +q: Nat, +hq: {C.high(k, y) == q : Nat}) -> {Nat.is_le(1n, q) == True{} : Bool}:
  match q:
    case 0n:
      +e = Equal.trans(Nat, y, Nat.add(C.low(k, y), C.shift(k, C.high(k, y))), C.low(k, y), WW.low_high(k, y), Equal.trans(Nat, Nat.add(C.low(k, y), C.shift(k, C.high(k, y))), Nat.add(C.low(k, y), C.shift(k, 0n)), C.low(k, y), Equal.cong(Nat, Nat, z => Nat.add(C.low(k, y), C.shift(k, z)), C.high(k, y), 0n, hq), Equal.trans(Nat, Nat.add(C.low(k, y), C.shift(k, 0n)), Nat.add(C.low(k, y), 0n), C.low(k, y), Equal.cong(Nat, Nat, z => Nat.add(C.low(k, y), z), C.shift(k, 0n), 0n, WW.shift_zero(k)), N.add_zero(C.low(k, y)))))
      +hl = L.subst(Nat, z => {Nat.is_lt(z, C.pow2(k)) == True{} : Bool}, C.low(k, y), y, Equal.sym(Nat, y, C.low(k, y), e), WW.low_lt(k, y))
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(y, C.pow2(k)), False{}, Equal.sym(Bool, Nat.is_lt(y, C.pow2(k)), True{}, hl), N.le_not_lt(y, C.pow2(k), h))))
    case 1n+r:
      N.zero_le(r)

# 2^k <= y: high(k, y) >= 1
def high_pos(+k: Nat, +y: Nat, +h: {Nat.is_le(C.pow2(k), y) == True{} : Bool}) -> {Nat.is_le(1n, C.high(k, y)) == True{} : Bool}:
  hp_c(k, y, h, C.high(k, y), {==})

# ---- the binary search of bitlen ----

def P1(st: Nat & U32) -> Nat:
  (+b, +y) = st
  b

def P2(st: Nat & U32) -> U32:
  (+b, +y) = st
  y

def INV(+k: Nat, +n: Nat, st: Nat & U32) -> Type:
  {M.bit_length(n) == Nat.add(P1(st), M.bit_length(v(P2(st)))) : Nat} & {C.fits(k, v(P2(st))) == True{} : Bool}

def eta_step(+k: Nat, st: Nat & U32) -> {X.bl_step(k, st) == X.bl_step(k, (P1(st), P2(st))) : Nat & U32}:
  match st:
    case Tuple{+b, +y}:
      {==}

def eta_fin(st: Nat & U32) -> {X.bl_fin(st) == X.bl_fin((P1(st), P2(st))) : Nat}:
  match st:
    case Tuple{+b, +y}:
      {==}

def blstep_c(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}, +n: Nat, +base: Nat, +y: U32, +hy: {C.fits(Nat.add(k, k), v(y)) == True{} : Bool}, +inv: {M.bit_length(n) == Nat.add(base, M.bit_length(v(y))) : Nat}, +c: Bool, +hc: {U32.is_le(X.pow2(k), y) == c : Bool}) -> INV(k, n, X.bl_pick(y, X.pow2(k), k, base, c)):
  match c:
    case True{}:
      +hle = L.subst(Nat, z => {Nat.is_le(z, v(y)) == True{} : Bool}, v(X.pow2(k)), C.pow2(k), SH.p2v(k, hk), Equal.trans(Bool, Nat.is_le(v(X.pow2(k)), v(y)), U32.is_le(X.pow2(k), y), True{}, Equal.sym(Bool, U32.is_le(X.pow2(k), y), Nat.is_le(v(X.pow2(k)), v(y)), W64S.is_le_nat(X.pow2(k), y)), hc))
      +hh = C.high(k, v(y))
      +ed = SH.div_p2(y, k, hk)
      +eb = bl_high(k, v(y), high_pos(k, v(y), hle))
      +e1 = Equal.trans(Nat, M.bit_length(n), Nat.add(base, Nat.add(k, M.bit_length(hh))), Nat.add(Nat.add(base, k), M.bit_length(v(U32.div(y, X.pow2(k))))), Equal.trans(Nat, M.bit_length(n), Nat.add(base, M.bit_length(v(y))), Nat.add(base, Nat.add(k, M.bit_length(hh))), inv, Equal.cong(Nat, Nat, z => Nat.add(base, z), M.bit_length(v(y)), Nat.add(k, M.bit_length(hh)), eb)), Equal.trans(Nat, Nat.add(base, Nat.add(k, M.bit_length(hh))), Nat.add(Nat.add(base, k), M.bit_length(hh)), Nat.add(Nat.add(base, k), M.bit_length(v(U32.div(y, X.pow2(k))))), Equal.sym(Nat, Nat.add(Nat.add(base, k), M.bit_length(hh)), Nat.add(base, Nat.add(k, M.bit_length(hh))), NA.add_assoc(base, k, M.bit_length(hh))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(base, k), M.bit_length(z)), hh, v(U32.div(y, X.pow2(k))), Equal.sym(Nat, v(U32.div(y, X.pow2(k))), hh, ed))))
      +f1 = L.subst(Nat, z => {C.fits(k, z) == True{} : Bool}, hh, v(U32.div(y, X.pow2(k))), Equal.sym(Nat, v(U32.div(y, X.pow2(k))), hh, ed), SH.fits_high(k, k, v(y), hy))
      (e1, f1)
    case False{}:
      +nl = Equal.trans(Bool, Nat.is_le(C.pow2(k), v(y)), Nat.is_le(v(X.pow2(k)), v(y)), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, v(y)), C.pow2(k), v(X.pow2(k)), Equal.sym(Nat, v(X.pow2(k)), C.pow2(k), SH.p2v(k, hk))), Equal.trans(Bool, Nat.is_le(v(X.pow2(k)), v(y)), U32.is_le(X.pow2(k), y), False{}, Equal.sym(Bool, U32.is_le(X.pow2(k), y), Nat.is_le(v(X.pow2(k)), v(y)), W64S.is_le_nat(X.pow2(k), y)), hc))
      (inv, WW.fits_of_lt(k, v(y), N.not_le_lt(C.pow2(k), v(y), nl)))

def blstep(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}, +n: Nat, +b: Nat, +y: U32, +hi: {M.bit_length(n) == Nat.add(b, M.bit_length(v(y))) : Nat}, +hy: {C.fits(Nat.add(k, k), v(y)) == True{} : Bool}) -> INV(k, n, X.bl_step(k, (b, y))):
  blstep_c(k, hk, n, b, y, hy, hi, U32.is_le(X.pow2(k), y), {==})

def small_c(+y: U32, +c: Bool, +hc: {U32.is_lt(y, 1) == c : Bool}, +nv: Nat, +hnv: {v(y) == nv : Nat}, +hy: {C.fits(1n, v(y)) == True{} : Bool}) -> {v(Bool.pick(U32, c, y, 1)) == M.bit_length(v(y)) : Nat}:
  match c nv:
    case True{} 0n:
      Equal.trans(Nat, v(y), 0n, M.bit_length(v(y)), hnv, Equal.cong(Nat, Nat, z => M.bit_length(z), 0n, v(y), Equal.sym(Nat, v(y), 0n, hnv)))
    case False{} 1n:
      Equal.cong(Nat, Nat, z => M.bit_length(z), 1n, v(y), Equal.sym(Nat, v(y), 1n, hnv))
    case True{} 1n+m:
      +h0 = Equal.trans(Bool, Nat.is_lt(1n+m, 1n), Nat.is_lt(v(y), v(1)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, 1n), 1n+m, v(y), Equal.sym(Nat, v(y), 1n+m, hnv)), Equal.trans(Bool, Nat.is_lt(v(y), v(1)), U32.is_lt(y, 1), True{}, Equal.sym(Bool, U32.is_lt(y, 1), Nat.is_lt(v(y), v(1)), U.is_lt_nat(y, 1)), hc))
      Empty.absurd({v(Bool.pick(U32, True{}, y, 1)) == M.bit_length(v(y)) : Nat}, N.lt_zero_absurd(m, h0))
    case False{} 0n:
      +h0 = Equal.trans(Bool, Nat.is_lt(0n, 1n), Nat.is_lt(v(y), v(1)), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, 1n), 0n, v(y), Equal.sym(Nat, v(y), 0n, hnv)), Equal.trans(Bool, Nat.is_lt(v(y), v(1)), U32.is_lt(y, 1), False{}, Equal.sym(Bool, U32.is_lt(y, 1), Nat.is_lt(v(y), v(1)), U.is_lt_nat(y, 1)), hc))
      Empty.absurd({v(Bool.pick(U32, False{}, y, 1)) == M.bit_length(v(y)) : Nat}, true_ne_false(h0))
    case False{} 2n+m:
      +h0 = L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, v(y), 2n+m, hnv, hy)
      Empty.absurd({v(Bool.pick(U32, False{}, y, 1)) == M.bit_length(v(y)) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, h0)))



def S0(+x: U32) -> Nat & U32:
  (0n, x)
def S1(+x: U32) -> Nat & U32:
  X.bl_step(16n, (P1(S0(x)), P2(S0(x))))
def S2(+x: U32) -> Nat & U32:
  X.bl_step(8n, (P1(S1(x)), P2(S1(x))))
def S3(+x: U32) -> Nat & U32:
  X.bl_step(4n, (P1(S2(x)), P2(S2(x))))
def S4(+x: U32) -> Nat & U32:
  X.bl_step(2n, (P1(S3(x)), P2(S3(x))))
def S5(+x: U32) -> Nat & U32:
  X.bl_step(1n, (P1(S4(x)), P2(S4(x))))

def bl_fin_v(+x: U32, p: INV(1n, v(x), S5(x))) -> {X.bl_fin(S5(x)) == M.bit_length(v(x)) : Nat}:
  (a, b) = p
  +em = small_c(P2(S5(x)), U32.is_lt(P2(S5(x)), 1), {==}, v(P2(S5(x))), {==}, b)
  Equal.trans(Nat, X.bl_fin(S5(x)), X.bl_fin((P1(S5(x)), P2(S5(x)))), M.bit_length(v(x)), eta_fin(S5(x)), Equal.trans(Nat, Nat.add(P1(S5(x)), v(U32.min(P2(S5(x)), 1))), Nat.add(P1(S5(x)), M.bit_length(v(P2(S5(x))))), M.bit_length(v(x)), Equal.cong(Nat, Nat, z => Nat.add(P1(S5(x)), z), v(U32.min(P2(S5(x)), 1)), M.bit_length(v(P2(S5(x)))), em), Equal.sym(Nat, M.bit_length(v(x)), Nat.add(P1(S5(x)), M.bit_length(v(P2(S5(x))))), a)))

def bstep2(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}, +n: Nat, +b: Nat, +y: U32, p: {M.bit_length(n) == Nat.add(b, M.bit_length(v(y))) : Nat} & {C.fits(Nat.add(k, k), v(y)) == True{} : Bool}) -> INV(k, n, X.bl_step(k, (b, y))):
  (a, c) = p
  blstep(k, hk, n, b, y, a, c)

def Q1(+x: U32) -> INV(16n, v(x), S1(x)):
  blstep(16n, {==}, v(x), 0n, x, {==}, LW.vb(x))

def Q2(+x: U32) -> INV(8n, v(x), S2(x)):
  bstep2(8n, {==}, v(x), P1(S1(x)), P2(S1(x)), Q1(x))

def Q3(+x: U32) -> INV(4n, v(x), S3(x)):
  bstep2(4n, {==}, v(x), P1(S2(x)), P2(S2(x)), Q2(x))

def Q4(+x: U32) -> INV(2n, v(x), S4(x)):
  bstep2(2n, {==}, v(x), P1(S3(x)), P2(S3(x)), Q3(x))

def Q5(+x: U32) -> INV(1n, v(x), S5(x)):
  bstep2(1n, {==}, v(x), P1(S4(x)), P2(S4(x)), Q4(x))

def eta_chain(+x: U32) -> {X.bitlen(x) == X.bl_fin(S5(x)) : Nat}:
  +e1 = {{==} : {X.bl_step(16n, (0n, x)) == S1(x) : Nat & U32}}
  +e2 = Equal.trans(Nat & U32, X.bl_step(8n, X.bl_step(16n, (0n, x))), X.bl_step(8n, S1(x)), S2(x), Equal.cong(Nat & U32, Nat & U32, z => X.bl_step(8n, z), X.bl_step(16n, (0n, x)), S1(x), e1), eta_step(8n, S1(x)))
  +e3 = Equal.trans(Nat & U32, X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x)))), X.bl_step(4n, S2(x)), S3(x), Equal.cong(Nat & U32, Nat & U32, z => X.bl_step(4n, z), X.bl_step(8n, X.bl_step(16n, (0n, x))), S2(x), e2), eta_step(4n, S2(x)))
  +e4 = Equal.trans(Nat & U32, X.bl_step(2n, X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x))))), X.bl_step(2n, S3(x)), S4(x), Equal.cong(Nat & U32, Nat & U32, z => X.bl_step(2n, z), X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x)))), S3(x), e3), eta_step(2n, S3(x)))
  +e5 = Equal.trans(Nat & U32, X.bl_step(1n, X.bl_step(2n, X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x)))))), X.bl_step(1n, S4(x)), S5(x), Equal.cong(Nat & U32, Nat & U32, z => X.bl_step(1n, z), X.bl_step(2n, X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x))))), S4(x), e4), eta_step(1n, S4(x)))
  Equal.cong(Nat & U32, Nat, z => X.bl_fin(z), X.bl_step(1n, X.bl_step(2n, X.bl_step(4n, X.bl_step(8n, X.bl_step(16n, (0n, x)))))), S5(x), e5)

def bitlen_v(+x: U32) -> {X.bitlen(x) == M.bit_length(v(x)) : Nat}:
  Equal.trans(Nat, X.bitlen(x), X.bl_fin(S5(x)), M.bit_length(v(x)), eta_chain(x), bl_fin_v(x, Q5(x)))

# ---- clz ----

def not_t(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

def not_f(+x: Bool, +h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(h))

def clz_c(+l: U32, +h: U32, +c: Bool, +hc: {Bool.not(U32.is_zero(h)) == c : Bool}) -> {X.clz_pick(WU.U64{l, h}, c) == Nat.sub(64n, M.bit_length(SW.value(WU.U64{l, h}))) : Nat}:
  match c:
    case True{}:
      +hz = Equal.trans(Bool, Nat.is_eq(v(h), 0n), U32.is_zero(h), False{}, Equal.sym(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h)), not_t(U32.is_zero(h), hc))
      +eh = WW.high_u(32n, v(l), v(h), LW.vb(l))
      +h1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, v(h), C.high(32n, SW.value(WU.U64{l, h})), Equal.sym(Nat, C.high(32n, SW.value(WU.U64{l, h})), v(h), eh), WA.pos_ne(v(h), hz))
      +eb = Equal.trans(Nat, M.bit_length(SW.value(WU.U64{l, h})), Nat.add(32n, M.bit_length(C.high(32n, SW.value(WU.U64{l, h})))), Nat.add(32n, M.bit_length(v(h))), bl_high(32n, SW.value(WU.U64{l, h}), h1), Equal.cong(Nat, Nat, z => Nat.add(32n, M.bit_length(z)), C.high(32n, SW.value(WU.U64{l, h})), v(h), eh))
      Equal.trans(Nat, Nat.sub(32n, X.bitlen(h)), Nat.sub(32n, M.bit_length(v(h))), Nat.sub(64n, M.bit_length(SW.value(WU.U64{l, h}))), Equal.cong(Nat, Nat, z => Nat.sub(32n, z), X.bitlen(h), M.bit_length(v(h)), bitlen_v(h)), Equal.trans(Nat, Nat.sub(32n, M.bit_length(v(h))), Nat.sub(64n, Nat.add(32n, M.bit_length(v(h)))), Nat.sub(64n, M.bit_length(SW.value(WU.U64{l, h}))), Equal.sym(Nat, Nat.sub(64n, Nat.add(32n, M.bit_length(v(h)))), Nat.sub(32n, M.bit_length(v(h))), NR.sub_cancel_l(32n, 32n, M.bit_length(v(h)))), Equal.cong(Nat, Nat, z => Nat.sub(64n, z), Nat.add(32n, M.bit_length(v(h))), M.bit_length(SW.value(WU.U64{l, h})), Equal.sym(Nat, M.bit_length(SW.value(WU.U64{l, h})), Nat.add(32n, M.bit_length(v(h))), eb))))
    case False{}:
      +hz = Equal.trans(Bool, Nat.is_eq(v(h), 0n), U32.is_zero(h), True{}, Equal.sym(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h)), not_f(U32.is_zero(h), hc))
      +ev = Equal.trans(Nat, SW.value(WU.U64{l, h}), Nat.add(v(l), C.shift(32n, 0n)), v(l), Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), v(h), 0n, N.eq_from_is_eq(v(h), 0n, hz)), Equal.trans(Nat, Nat.add(v(l), C.shift(32n, 0n)), Nat.add(v(l), 0n), v(l), Equal.cong(Nat, Nat, z => Nat.add(v(l), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(l))))
      Equal.trans(Nat, Nat.sub(64n, X.bitlen(l)), Nat.sub(64n, M.bit_length(v(l))), Nat.sub(64n, M.bit_length(SW.value(WU.U64{l, h}))), Equal.cong(Nat, Nat, z => Nat.sub(64n, z), X.bitlen(l), M.bit_length(v(l)), bitlen_v(l)), Equal.cong(Nat, Nat, z => Nat.sub(64n, M.bit_length(z)), v(l), SW.value(WU.U64{l, h}), Equal.sym(Nat, SW.value(WU.U64{l, h}), v(l), ev)))

def clz_value(+a: WU.U64) -> SW.Clz.value(a):
  match a:
    case WU.U64{+l, +h}:
      clz_c(l, h, Bool.not(U32.is_zero(h)), {==})
