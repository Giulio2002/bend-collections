import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/natural.bend as NS
import ../../../src/math/w64.bend as X
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/lemmas/spec/numeric.bend as S
import ../u64/u64div.bend as PD
import ../natural/proof.bend as NP
import ./w64mul.bend as WM
import ./u32.bend as U32P

# Isqrt32.value of spec/math/w64.bend: floor(sqrt(x)) of a U32 from ANY
# estimate r <= 2^16 - 1. The F32 square root only picks the start; the
# down loop (r - 1 while r^2 > x) and the up loop (r + 1 while r < 2^16 - 1
# and (r + 1)^2 <= x) are proved to reach the unique r with
# r^2 <= x < (r + 1)^2 within their fuel for every start, so the result never
# depends on F32 (Base's F32 primitives are opaque to the checker). The shape
# is the estimate-and-correct square root of Why3's WhyMP mpn_sqrtrem and of
# Mathlib's Nat.sqrt correctness (Nat.sqrt_le', Nat.lt_succ_sqrt').

def v(+x: U32) -> Nat:
  UD.v(x)

def sq(+n: Nat) -> Nat:
  Nat.mul(n, n)

# ---- 2^16 - 1 ----

def mz(+p: Nat) -> {WD.uw(p, WD.mask(p, 0n)) == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.cong(Nat, Nat, t => Nat.double(t), WD.uw(q, WD.mask(q, 0n)), 0n, mz(q))

def mval(+n: Nat, +k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {1n+WD.uw(n, WD.mask(n, k)) == WD.sc(k, one) : Nat}:
  match n k:
    case 0n 0n:
      Equal.sym(Nat, one, 1n, h1)
    case 0n 1n+j:
      Empty.absurd({1n+WD.uw(0n, WD.mask(0n, 1n+j)) == WD.sc(1n+j, one) : Nat}, U32P.true_ne_false(Equal.sym(Bool, False{}, True{}, hk)))
    case 1n+ +p 0n:
      %Equal.sym(Nat, WD.uw(p, WD.mask(p, 0n)), 0n, mz(p)) : {1n+Nat.add(0n, Nat.double(_)) == WD.sc(0n, one) : Nat}
      Equal.sym(Nat, one, 1n, h1)
    case 1n+ +p 1n+ +j:
      Equal.cong(Nat, Nat, t => Nat.double(t), 1n+WD.uw(p, WD.mask(p, j)), WD.sc(j, one), mval(p, j, one, h1, hk))

def mask_v(+k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, k)} : U32}) -> {1n+v(m) == WD.sc(k, one) : Nat}:
  +e = L.subst(U32, z => {v(z) == WD.uw(32n, WD.mask(32n, k)) : Nat}, U32{WD.mask(32n, k)}, m, Equal.sym(U32, m, U32{WD.mask(32n, k)}, pm), UD.vw(WD.mask(32n, k)))
  Equal.trans(Nat, 1n+v(m), 1n+WD.uw(32n, WD.mask(32n, k)), WD.sc(k, one), N.succ_cong(v(m), WD.uw(32n, WD.mask(32n, k)), e), mval(32n, k, one, h1, hk))

# 1 + v(m) == 2^16 for m the 16-bit mask
def m16(+one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}) -> {1n+v(m) == WD.sc(16n, one) : Nat}:
  mask_v(16n, {==}, one, h1, m, pm)

# ---- exact squares below 2^16 ----

def sq_exact(+one: Nat, +h1: {one == 1n : Nat}, +r: U32, +hb: {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}) -> {v(U32.mul(r, r)) == sq(v(r)) : Nat}:
  PD.mul32(one, h1, r, r, WM.prod_lt(one, h1, v(r), v(r), hb, hb))

def is_le_nat(+a: U32, +b: U32) -> {U32.is_le(a, b) == Nat.is_le(v(a), v(b)) : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(v(a), v(b)), U.u32_cmp(a, b)) : {Cmp.is_le(_) == Nat.is_le(v(a), v(b)) : Bool}
  {==}

# ---- down: r - 1 while r^2 > x ----

def DN(+one: Nat, +x: U32, +r: U32) -> Type:
  {Nat.is_le(sq(v(r)), v(x)) == True{} : Bool} & {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}

def lt_sq(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +r: U32, +hb: {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}) -> {U32.is_lt(x, U32.mul(r, r)) == Nat.is_lt(v(x), sq(v(r))) : Bool}:
  L.subst(Nat, z => {U32.is_lt(x, U32.mul(r, r)) == Nat.is_lt(v(x), z) : Bool}, v(U32.mul(r, r)), sq(v(r)), sq_exact(one, h1, r, hb), U.is_lt_nat(x, U32.mul(r, r)))

def dn(+fu: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32, +r: U32, +hf: {Nat.is_lt(v(r), fu) == True{} : Bool}, +hb: {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}, +cb: Bool, +hc: {U32.is_lt(x, U32.mul(r, r)) == cb : Bool}, +nval: Nat, +hnr: {v(r) == nval : Nat}) -> {Nat.is_le(sq(v(X.down32(fu, x, r, cb))), v(x)) == True{} : Bool} & {Nat.is_lt(v(X.down32(fu, x, r, cb)), WD.sc(16n, one)) == True{} : Bool}:
  match fu:
    case 0n:
      Empty.absurd({Nat.is_le(sq(v(X.down32(0n, x, r, cb))), v(x)) == True{} : Bool} & {Nat.is_lt(v(X.down32(0n, x, r, cb)), WD.sc(16n, one)) == True{} : Bool}, N.lt_zero_absurd(v(r), hf))
    case 1n+ +g:
      match cb:
        case False{}:
          +hc2 = Equal.trans(Bool, Nat.is_lt(v(x), sq(v(r))), U32.is_lt(x, U32.mul(r, r)), False{}, Equal.sym(Bool, U32.is_lt(x, U32.mul(r, r)), Nat.is_lt(v(x), sq(v(r))), lt_sq(one, h1, x, r, hb)), hc)
          (N.not_lt_le(v(x), sq(v(r)), hc2), hb)
        case True{}:
          match nval:
            case 0n:
              +hc2 = Equal.trans(Bool, Nat.is_lt(v(x), sq(v(r))), U32.is_lt(x, U32.mul(r, r)), True{}, Equal.sym(Bool, U32.is_lt(x, U32.mul(r, r)), Nat.is_lt(v(x), sq(v(r))), lt_sq(one, h1, x, r, hb)), hc)
              +h0 = L.subst(Nat, z => {Nat.is_lt(v(x), sq(z)) == True{} : Bool}, v(r), 0n, hnr, hc2)
              Empty.absurd({Nat.is_le(sq(v(X.down32(1n+g, x, r, True{}))), v(x)) == True{} : Bool} & {Nat.is_lt(v(X.down32(1n+g, x, r, True{})), WD.sc(16n, one)) == True{} : Bool}, N.lt_zero_absurd(v(x), h0))
            case 1n+ +rp:
              +r1 = U32.sub(r, 1)
              +e1 = Equal.trans(Nat, v(r1), Nat.sub(v(r), 1n), rp, U.sub_nat(r, 1, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+rp, v(r), Equal.sym(Nat, v(r), 1n+rp, hnr), N.zero_le(rp))), Equal.trans(Nat, Nat.sub(v(r), 1n), Nat.sub(1n+rp, 1n), rp, Equal.cong(Nat, Nat, t => Nat.sub(t, 1n), v(r), 1n+rp, hnr), N.sub_zero(rp)))
              +hf1 = L.subst(Nat, z => {Nat.is_lt(z, g) == True{} : Bool}, rp, v(r1), Equal.sym(Nat, v(r1), rp, e1), L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, v(r), 1n+rp, hnr, hf))
              +hb1 = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, rp, v(r1), Equal.sym(Nat, v(r1), rp, e1), N.lt_trans(rp, 1n+rp, WD.sc(16n, one), N.lt_succ(rp), L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, v(r), 1n+rp, hnr, hb)))
              dn(g, one, h1, x, r1, hf1, hb1, U32.is_lt(x, U32.mul(r1, r1)), {==}, rp, e1)

# ---- up: r + 1 while r < m and (r + 1)^2 <= x, m == 2^16 - 1 symbolic ----

def up_okg(+x: U32, +r: U32, +m: U32) -> Bool:
  Bool.and(U32.is_lt(r, m), U32.is_le(U32.mul(U32.add(r, 1), U32.add(r, 1)), x))

def up32g(fuel: Nat, +x: U32, +r: U32, up: Bool, +m: U32) -> U32:
  match fuel up:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      up32g(f, x, U32.add(r, 1), up_okg(x, U32.add(r, 1), m), m)

def impl_up(+fuel: Nat, +x: U32, +r: U32, +up: Bool) -> {X.up32(fuel, x, r, up) == up32g(fuel, x, r, up, 65535) : U32}:
  match fuel up:
    case 0n _:
      {==}
    case 1n+ +f False{}:
      {==}
    case 1n+ +f True{}:
      impl_up(f, x, U32.add(r, 1), X.up_ok(x, U32.add(r, 1)))

def lt_to_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  N.lt_succ_le_succ(a, b, h)

# where the up loop stops, x < (r + 1)^2
def up_stop(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +r: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +hle: {Nat.is_le(v(r), v(m)) == True{} : Bool}, +b: Bool, +hb2: {U32.is_le(U32.mul(U32.add(r, 1), U32.add(r, 1)), x) == b : Bool}, +a: Bool, +ha: {U32.is_lt(r, m) == a : Bool}, +hstop: {Bool.and(a, b) == False{} : Bool}) -> {Nat.is_lt(v(x), sq(1n+v(r))) == True{} : Bool}:
  match a:
    case False{}:
      +em = m16(one, h1, m, pm)
      +nl = Equal.trans(Bool, Nat.is_lt(v(r), v(m)), U32.is_lt(r, m), False{}, Equal.sym(Bool, U32.is_lt(r, m), Nat.is_lt(v(r), v(m)), U.is_lt_nat(r, m)), ha)
      +er = N.le_antisym(v(r), v(m), hle, N.not_lt_le(v(r), v(m), nl))
      +e1 = Equal.trans(Nat, 1n+v(r), 1n+v(m), WD.sc(16n, one), N.succ_cong(v(r), v(m), er), em)
      +ex = L.subst(Nat, z => {Nat.is_lt(v(x), z) == True{} : Bool}, WD.sc(32n, one), sq(1n+v(r)), Equal.sym(Nat, sq(1n+v(r)), WD.sc(32n, one), Equal.trans(Nat, sq(1n+v(r)), Nat.mul(WD.sc(16n, one), WD.sc(16n, one)), WD.sc(32n, one), Equal.trans(Nat, sq(1n+v(r)), Nat.mul(WD.sc(16n, one), 1n+v(r)), Nat.mul(WD.sc(16n, one), WD.sc(16n, one)), Equal.cong(Nat, Nat, t => Nat.mul(t, 1n+v(r)), 1n+v(r), WD.sc(16n, one), e1), Equal.cong(Nat, Nat, t => Nat.mul(WD.sc(16n, one), t), 1n+v(r), WD.sc(16n, one), e1)), WM.sq_sc(16n, one, h1))), UD.vb(one, h1, x))
      ex
    case True{}:
      +em = m16(one, h1, m, pm)
      +lt = Equal.trans(Bool, Nat.is_lt(v(r), v(m)), U32.is_lt(r, m), True{}, Equal.sym(Bool, U32.is_lt(r, m), Nat.is_lt(v(r), v(m)), U.is_lt_nat(r, m)), ha)
      +b16 = N.lt_le_trans(v(r), v(m), WD.sc(16n, one), lt, N.lt_le(v(m), WD.sc(16n, one), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), WD.sc(16n, one), em, N.lt_succ(v(m)))))
      +r1 = U32.add(r, 1)
      +bs = N.le_lt_trans(1n+v(r), v(m), WD.sc(16n, one), lt_to_le(v(r), v(m), lt), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), WD.sc(16n, one), em, N.lt_succ(v(m))))
      +a1 = Equal.trans(Nat, Nat.add(v(r), 1n), 1n+Nat.add(v(r), 0n), 1n+v(r), NA.add_succ(v(r), 0n), N.succ_cong(Nat.add(v(r), 0n), v(r), N.add_zero(v(r))))
      +lt32 = N.lt_le_trans(Nat.add(v(r), 1n), WD.sc(16n, one), WD.sc(32n, one), L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, 1n+v(r), Nat.add(v(r), 1n), Equal.sym(Nat, Nat.add(v(r), 1n), 1n+v(r), a1), bs), AR.le_sc(16n, WD.sc(16n, one)))
      +e1 = Equal.trans(Nat, v(r1), Nat.add(v(r), 1n), 1n+v(r), PD.add32(one, h1, r, 1, lt32), a1)
      +bs1 = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, 1n+v(r), v(r1), Equal.sym(Nat, v(r1), 1n+v(r), e1), bs)
      +esq = Equal.trans(Nat, v(U32.mul(r1, r1)), sq(v(r1)), sq(1n+v(r)), sq_exact(one, h1, r1, bs1), Equal.cong(Nat, Nat, t => sq(t), v(r1), 1n+v(r), e1))
      +nb = Equal.trans(Bool, Nat.is_le(sq(1n+v(r)), v(x)), U32.is_le(U32.mul(r1, r1), x), False{}, Equal.sym(Bool, U32.is_le(U32.mul(r1, r1), x), Nat.is_le(sq(1n+v(r)), v(x)), L.subst(Nat, z => {U32.is_le(U32.mul(r1, r1), x) == Nat.is_le(z, v(x)) : Bool}, v(U32.mul(r1, r1)), sq(1n+v(r)), esq, is_le_nat(U32.mul(r1, r1), x))), Equal.trans(Bool, U32.is_le(U32.mul(r1, r1), x), b, False{}, hb2, hstop))
      N.not_le_lt(sq(1n+v(r)), v(x), nb)

def and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, U32P.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

def and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, U32P.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

# b - a == 1 + (b - (a + 1)) for a < b
def sub_succ_r(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.sub(b, a) == 1n+Nat.sub(b, 1n+a) : Nat}:
  match b:
    case 0n:
      Empty.absurd({Nat.sub(0n, a) == 1n+Nat.sub(0n, 1n+a) : Nat}, N.lt_zero_absurd(a, h))
    case 1n+ +bp:
      N.sub_succ_left(bp, a, N.lt_succ_le(a, bp, h))

# r + 1 below 2^16 when r < m == 2^16 - 1: its value and its exact square
def succ_v(+one: Nat, +h1: {one == 1n : Nat}, +r: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +lt: {Nat.is_lt(v(r), v(m)) == True{} : Bool}) -> {v(U32.add(r, 1)) == 1n+v(r) : Nat}:
  +em = m16(one, h1, m, pm)
  +bs = N.le_lt_trans(1n+v(r), v(m), WD.sc(16n, one), lt_to_le(v(r), v(m), lt), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), WD.sc(16n, one), em, N.lt_succ(v(m))))
  +a1 = Equal.trans(Nat, Nat.add(v(r), 1n), 1n+Nat.add(v(r), 0n), 1n+v(r), NA.add_succ(v(r), 0n), N.succ_cong(Nat.add(v(r), 0n), v(r), N.add_zero(v(r))))
  +lt32 = N.lt_le_trans(Nat.add(v(r), 1n), WD.sc(16n, one), WD.sc(32n, one), L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, 1n+v(r), Nat.add(v(r), 1n), Equal.sym(Nat, Nat.add(v(r), 1n), 1n+v(r), a1), bs), AR.le_sc(16n, WD.sc(16n, one)))
  Equal.trans(Nat, v(U32.add(r, 1)), Nat.add(v(r), 1n), 1n+v(r), PD.add32(one, h1, r, 1, lt32), a1)

def up(+fu: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: U32, +r: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +hf: {Nat.is_lt(Nat.sub(v(m), v(r)), fu) == True{} : Bool}, +hle: {Nat.is_le(v(r), v(m)) == True{} : Bool}, +hs: {Nat.is_le(sq(v(r)), v(x)) == True{} : Bool}, +ub: Bool, +hub: {up_okg(x, r, m) == ub : Bool}) -> {Nat.is_le(sq(v(up32g(fu, x, r, ub, m))), v(x)) == True{} : Bool} & {Nat.is_lt(v(x), sq(1n+v(up32g(fu, x, r, ub, m)))) == True{} : Bool}:
  match fu:
    case 0n:
      Empty.absurd({Nat.is_le(sq(v(up32g(0n, x, r, ub, m))), v(x)) == True{} : Bool} & {Nat.is_lt(v(x), sq(1n+v(up32g(0n, x, r, ub, m)))) == True{} : Bool}, N.lt_zero_absurd(Nat.sub(v(m), v(r)), hf))
    case 1n+ +g:
      match ub:
        case False{}:
          (hs, up_stop(one, h1, x, r, m, pm, hle, U32.is_le(U32.mul(U32.add(r, 1), U32.add(r, 1)), x), {==}, U32.is_lt(r, m), {==}, hub))
        case True{}:
          +r1 = U32.add(r, 1)
          +ha = and_l(U32.is_lt(r, m), U32.is_le(U32.mul(r1, r1), x), hub)
          +hb = and_r(U32.is_lt(r, m), U32.is_le(U32.mul(r1, r1), x), hub)
          +lt = Equal.trans(Bool, Nat.is_lt(v(r), v(m)), U32.is_lt(r, m), True{}, Equal.sym(Bool, U32.is_lt(r, m), Nat.is_lt(v(r), v(m)), U.is_lt_nat(r, m)), ha)
          +e1 = succ_v(one, h1, r, m, pm, lt)
          +em = m16(one, h1, m, pm)
          +bs1 = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(16n, one)) == True{} : Bool}, 1n+v(r), v(r1), Equal.sym(Nat, v(r1), 1n+v(r), e1), N.le_lt_trans(1n+v(r), v(m), WD.sc(16n, one), lt_to_le(v(r), v(m), lt), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), WD.sc(16n, one), em, N.lt_succ(v(m)))))
          +esq = sq_exact(one, h1, r1, bs1)
          +hs1 = L.subst(Nat, z => {Nat.is_le(z, v(x)) == True{} : Bool}, v(U32.mul(r1, r1)), sq(v(r1)), esq, Equal.trans(Bool, Nat.is_le(v(U32.mul(r1, r1)), v(x)), U32.is_le(U32.mul(r1, r1), x), True{}, Equal.sym(Bool, U32.is_le(U32.mul(r1, r1), x), Nat.is_le(v(U32.mul(r1, r1)), v(x)), is_le_nat(U32.mul(r1, r1), x)), hb))
          +hle1 = L.subst(Nat, z => {Nat.is_le(z, v(m)) == True{} : Bool}, 1n+v(r), v(r1), Equal.sym(Nat, v(r1), 1n+v(r), e1), lt_to_le(v(r), v(m), lt))
          +hf0 = L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, Nat.sub(v(m), v(r)), 1n+Nat.sub(v(m), 1n+v(r)), sub_succ_r(v(r), v(m), lt), hf)
          +hf1 = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), z), g) == True{} : Bool}, 1n+v(r), v(r1), Equal.sym(Nat, v(r1), 1n+v(r), e1), hf0)
          up(g, one, h1, x, r1, m, pm, hf1, hle1, hs1, up_okg(x, r1, m), {==})

# ---- the integer square root is unique ----

def pow_sq(+a: Nat) -> {Nat.pow(a, 2n) == sq(a) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.mul(a, t), Nat.mul(a, 1n), a, NA.mul_one(a))

def sq_mono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(sq(a), sq(b)) == True{} : Bool}:
  N.le_trans(sq(a), Nat.mul(a, b), sq(b), WM.le_mul_r(a, a, b, h), AR.mul_le(a, b, b, h))

# r^2 <= n < (s + 1)^2 gives r <= s
def root_le(+r: Nat, +s: Nat, +n: Nat, +hr: {Nat.is_le(sq(r), n) == True{} : Bool}, +hs: {Nat.is_lt(n, sq(1n+s)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(s, r) == c : Bool}) -> {Nat.is_le(r, s) == True{} : Bool}:
  match c:
    case False{}:
      N.not_lt_le(s, r, hc)
    case True{}:
      +le = sq_mono(1n+s, r, N.lt_succ_le_succ(s, r, hc))
      +nn = N.lt_le_trans(n, sq(1n+s), n, hs, N.le_trans(sq(1n+s), sq(r), n, le, hr))
      Empty.absurd({Nat.is_le(r, s) == True{} : Bool}, U32P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(n, n), False{}, Equal.sym(Bool, Nat.is_lt(n, n), True{}, nn), N.lt_irrefl(n))))

def root_uniq(+r: Nat, +s: Nat, +n: Nat, +h1: {Nat.is_le(sq(r), n) == True{} : Bool}, +h2: {Nat.is_lt(n, sq(1n+r)) == True{} : Bool}, +h3: {Nat.is_le(sq(s), n) == True{} : Bool}, +h4: {Nat.is_lt(n, sq(1n+s)) == True{} : Bool}) -> {r == s : Nat}:
  N.le_antisym(r, s, root_le(r, s, n, h1, h4, Nat.is_lt(s, r), {==}), root_le(s, r, n, h3, h2, Nat.is_lt(r, s), {==}))

# a root r with r^2 <= n < (r + 1)^2 is M.isqrt(n)
def is_isqrt(+r: Nat, +n: Nat, +h1: {Nat.is_le(sq(r), n) == True{} : Bool}, +h2: {Nat.is_lt(n, sq(1n+r)) == True{} : Bool}) -> {r == M.isqrt(n) : Nat}:
  +q = M.isqrt(n)
  +a = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.pow(q, 2n), sq(q), pow_sq(q), NP.isqrt_le(n))
  +b = L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, Nat.pow(1n+q, 2n), sq(1n+q), pow_sq(1n+q), NP.isqrt_lt_succ(n))
  root_uniq(r, q, n, h1, h2, a, b)

# ---- the clamped estimate ----

def min_le(+e: U32, +m: U32, +c: Bool, +hc: {U32.is_lt(e, m) == c : Bool}) -> {Nat.is_le(v(Bool.pick(U32, c, e, m)), v(m)) == True{} : Bool}:
  match c:
    case True{}:
      N.lt_le(v(e), v(m), Equal.trans(Bool, Nat.is_lt(v(e), v(m)), U32.is_lt(e, m), True{}, Equal.sym(Bool, U32.is_lt(e, m), Nat.is_lt(v(e), v(m)), U.is_lt_nat(e, m)), hc))
    case False{}:
      N.le_refl(v(m))

# ---- floor(sqrt(x)) from any start below 2^16 ----

def lt16(+one: Nat, +h1: {one == 1n : Nat}, +r: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +h: {Nat.is_le(v(r), v(m)) == True{} : Bool}) -> {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}:
  N.le_lt_trans(v(r), v(m), WD.sc(16n, one), h, L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), WD.sc(16n, one), m16(one, h1, m, pm), N.lt_succ(v(m))))

def le16(+one: Nat, +h1: {one == 1n : Nat}, +r: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +h: {Nat.is_lt(v(r), WD.sc(16n, one)) == True{} : Bool}) -> {Nat.is_le(v(r), v(m)) == True{} : Bool}:
  N.lt_succ_le(v(r), v(m), L.subst(Nat, z => {Nat.is_lt(v(r), z) == True{} : Bool}, WD.sc(16n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), WD.sc(16n, one), m16(one, h1, m, pm)), h))

def RES(+fu: Nat, +x: U32, +r: U32, +m: U32) -> Nat:
  v(up32g(fu, x, r, up_okg(x, r, m), m))

def main_fin(+x: U32, +rd: U32, +m: U32, +fu: Nat, q: {Nat.is_le(sq(v(up32g(fu, x, rd, up_okg(x, rd, m), m))), v(x)) == True{} : Bool} & {Nat.is_lt(v(x), sq(1n+v(up32g(fu, x, rd, up_okg(x, rd, m), m)))) == True{} : Bool}) -> {v(up32g(fu, x, rd, up_okg(x, rd, m), m)) == M.isqrt(v(x)) : Nat}:
  (h3, h4) = q
  is_isqrt(v(up32g(fu, x, rd, up_okg(x, rd, m), m)), v(x), h3, h4)

def main_up(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +rd: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, p: {Nat.is_le(sq(v(rd)), v(x)) == True{} : Bool} & {Nat.is_lt(v(rd), WD.sc(16n, one)) == True{} : Bool}) -> {v(up32g(1n+U32.to_nat(U32.sub(m, rd)), x, rd, up_okg(x, rd, m), m)) == M.isqrt(v(x)) : Nat}:
  (hsq, hbd) = p
  +hle = le16(one, h1, rd, m, pm, hbd)
  +es = U.sub_nat(m, rd, hle)
  +hf = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), v(rd)), 1n+z) == True{} : Bool}, Nat.sub(v(m), v(rd)), v(U32.sub(m, rd)), Equal.sym(Nat, v(U32.sub(m, rd)), Nat.sub(v(m), v(rd)), es), N.lt_succ(Nat.sub(v(m), v(rd))))
  main_fin(x, rd, m, 1n+v(U32.sub(m, rd)), up(1n+v(U32.sub(m, rd)), one, h1, x, rd, m, pm, hf, hle, hsq, up_okg(x, rd, m), {==}))

def main_sqrt(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +r0: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}, +hr0: {Nat.is_le(v(r0), v(m)) == True{} : Bool}) -> {v(up32g(1n+U32.to_nat(U32.sub(m, X.down32(1n+U32.to_nat(r0), x, r0, U32.is_lt(x, U32.mul(r0, r0))))), x, X.down32(1n+U32.to_nat(r0), x, r0, U32.is_lt(x, U32.mul(r0, r0))), up_okg(x, X.down32(1n+U32.to_nat(r0), x, r0, U32.is_lt(x, U32.mul(r0, r0))), m), m)) == M.isqrt(v(x)) : Nat}:
  main_up(one, h1, x, X.down32(1n+U32.to_nat(r0), x, r0, U32.is_lt(x, U32.mul(r0, r0))), m, pm, dn(1n+v(r0), one, h1, x, r0, N.lt_succ(v(r0)), lt16(one, h1, r0, m, pm, hr0), U32.is_lt(x, U32.mul(r0, r0)), {==}, v(r0), {==}))

# from any estimate e, clamped to m == 2^16 - 1
def main_est(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +e: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 16n)} : U32}) -> {v(up32g(1n+U32.to_nat(U32.sub(m, X.down32(1n+U32.to_nat(U32.min(e, m)), x, U32.min(e, m), U32.is_lt(x, U32.mul(U32.min(e, m), U32.min(e, m)))))), x, X.down32(1n+U32.to_nat(U32.min(e, m)), x, U32.min(e, m), U32.is_lt(x, U32.mul(U32.min(e, m), U32.min(e, m)))), up_okg(x, X.down32(1n+U32.to_nat(U32.min(e, m)), x, U32.min(e, m), U32.is_lt(x, U32.mul(U32.min(e, m), U32.min(e, m)))), m), m)) == M.isqrt(v(x)) : Nat}:
  main_sqrt(one, h1, x, U32.min(e, m), m, pm, min_le(e, m, U32.is_lt(e, m), {==}))

# Isqrt32.value: floor(sqrt(x)) for every U32, whatever the F32 estimate is
def isqrt32_value(+x: U32) -> SW.Isqrt32.value(x):
  +r0 = U32.min(F32.to_u32(F32.sqrt(U32.to_f32(x))), 65535)
  +rd = X.down32(1n+U32.to_nat(r0), x, r0, U32.is_lt(x, U32.mul(r0, r0)))
  %Equal.sym(U32, X.up32(1n+U32.to_nat(U32.sub(65535, rd)), x, rd, X.up_ok(x, rd)), up32g(1n+U32.to_nat(U32.sub(65535, rd)), x, rd, X.up_ok(x, rd), 65535), impl_up(1n+U32.to_nat(U32.sub(65535, rd)), x, rd, X.up_ok(x, rd))) : {U32.to_nat(_) == M.isqrt(U32.to_nat(x)) : Nat}
  main_est(1n, {==}, x, F32.to_u32(F32.sqrt(U32.to_f32(x))), 65535, {==})
