import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ./w64mul.bend as W64M
import ./w64sqrt.bend as W64S
import ./w64add.bend as WA
import ./width.bend as WW
import ./u32laws.bend as LW

# Isqrt.value of spec/math/w64.bend: the 64-bit integer square root from any
# 32-bit estimate, down while r^2 > n and up while (r + 1)^2 <= n (the Why3
# gallery's isqrt loop invariant r^2 <= n < (r + 1)^2; Mathlib Nat.sqrt_le',
# Nat.lt_succ_sqrt'); the estimate's accuracy only bounds the run time.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def sq(+n: Nat) -> Nat:
  Nat.mul(n, n)

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

# r^2 > n
def ovs(+n: WU.U64, +r: U32) -> {X.sq_over(n, r) == Nat.is_lt(SW.value(n), sq(v(r))) : Bool}:
  Equal.trans(Bool, X.lt(n, X.mul32(r, r)), Nat.is_lt(SW.value(n), SW.value(X.mul32(r, r))), Nat.is_lt(SW.value(n), sq(v(r))), WA.lt_value(n, X.mul32(r, r)), Equal.cong(Nat, Bool, z => Nat.is_lt(SW.value(n), z), SW.value(X.mul32(r, r)), sq(v(r)), W64M.mul32_value(r, r)))

def dn64(+fu: Nat, +n: WU.U64, +r: U32, +cb: Bool, +nr: Nat, +hf: {Nat.is_lt(v(r), fu) == True{} : Bool}, +hc: {X.sq_over(n, r) == cb : Bool}, +hnr: {v(r) == nr : Nat}) -> {Nat.is_le(sq(v(X.down64(fu, n, r, cb))), SW.value(n)) == True{} : Bool}:
  match fu cb nr:
    case 0n _ _:
      Empty.absurd({Nat.is_le(sq(v(X.down64(0n, n, r, cb))), SW.value(n)) == True{} : Bool}, N.lt_zero_absurd(v(r), hf))
    case 1n+g False{} _:
      N.not_lt_le(SW.value(n), sq(v(r)), Equal.trans(Bool, Nat.is_lt(SW.value(n), sq(v(r))), X.sq_over(n, r), False{}, Equal.sym(Bool, X.sq_over(n, r), Nat.is_lt(SW.value(n), sq(v(r))), ovs(n, r)), hc))
    case 1n+g True{} 0n:
      +h0 = Equal.trans(Bool, Nat.is_lt(SW.value(n), sq(v(r))), X.sq_over(n, r), True{}, Equal.sym(Bool, X.sq_over(n, r), Nat.is_lt(SW.value(n), sq(v(r))), ovs(n, r)), hc)
      +h1 = L.subst(Nat, z => {Nat.is_lt(SW.value(n), sq(z)) == True{} : Bool}, v(r), 0n, hnr, h0)
      Empty.absurd({Nat.is_le(sq(v(X.down64(1n+g, n, r, True{}))), SW.value(n)) == True{} : Bool}, N.lt_zero_absurd(SW.value(n), h1))
    case 1n+ +g True{} 1n+ +rp:
      +r1 = U32.sub(r, 1)
      +e1 = Equal.trans(Nat, v(r1), Nat.sub(v(r), 1n), rp, U.sub_nat(r, 1, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+rp, v(r), Equal.sym(Nat, v(r), 1n+rp, hnr), N.zero_le(rp))), Equal.trans(Nat, Nat.sub(v(r), 1n), Nat.sub(1n+rp, 1n), rp, Equal.cong(Nat, Nat, t => Nat.sub(t, 1n), v(r), 1n+rp, hnr), N.sub_zero(rp)))
      +hf1 = L.subst(Nat, z => {Nat.is_lt(z, g) == True{} : Bool}, rp, v(r1), Equal.sym(Nat, v(r1), rp, e1), L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, v(r), 1n+rp, hnr, hf))
      dn64(g, n, r1, X.sq_over(n, r1), rp, hf1, {==}, e1)

def up64_okg(+n: WU.U64, +r: U32, +m: U32) -> Bool:
  Bool.and(U32.is_lt(r, m), Bool.not(X.sq_over(n, U32.add(r, 1))))

def up64g(fuel: Nat, +n: WU.U64, +r: U32, up: Bool, +m: U32) -> U32:
  match fuel up:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      up64g(f, n, U32.add(r, 1), up64_okg(n, U32.add(r, 1), m), m)

def impl_up64(+fuel: Nat, +n: WU.U64, +r: U32, +up: Bool) -> {X.up64(fuel, n, r, up) == up64g(fuel, n, r, up, 4294967295) : U32}:
  match fuel up:
    case 0n _:
      {==}
    case 1n+ +f False{}:
      {==}
    case 1n+ +f True{}:
      impl_up64(f, n, U32.add(r, 1), X.up64_ok(n, U32.add(r, 1)))

def not_t(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

def not_not(+c: Bool) -> {Bool.not(Bool.not(c)) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def m32(+one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {1n+v(m) == C.shift(32n, one) : Nat}:
  Equal.trans(Nat, 1n+v(m), WD.sc(32n, one), C.shift(32n, one), W64S.mask_v(32n, {==}, one, h1, m, pm), Equal.sym(Nat, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one)))

def succ_m(+one: Nat, +h1: {one == 1n : Nat}, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +lt: {Nat.is_lt(v(q), v(m)) == True{} : Bool}) -> {v(U32.add(q, 1)) == 1n+v(q) : Nat}:
  +em = m32(one, h1, m, pm)
  +h = N.le_lt_trans(Nat.add(v(q), 1n), v(m), C.shift(32n, one), L.subst(Nat, z => {Nat.is_le(z, v(m)) == True{} : Bool}, 1n+v(q), Nat.add(v(q), 1n), Equal.sym(Nat, Nat.add(v(q), 1n), 1n+v(q), WA.plus1(v(q))), N.lt_succ_le_succ(v(q), v(m), lt)), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), C.shift(32n, one), em, N.lt_succ(v(m))))
  Equal.trans(Nat, v(U32.add(q, 1)), Nat.add(v(q), 1n), 1n+v(q), WA.add_exact(one, h1, q, 1, WW.fits_one(32n, one, h1, Nat.add(v(q), 1n), h)), WA.plus1(v(q)))

def ustop(+one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +hle: {Nat.is_le(v(q), v(m)) == True{} : Bool}, +hX: {Nat.is_lt(SW.value(n), sq(1n+v(m))) == True{} : Bool}, +a: Bool, +ha: {U32.is_lt(q, m) == a : Bool}, +c: Bool, +hcb: {Bool.not(X.sq_over(n, U32.add(q, 1))) == c : Bool}, +hstop: {Bool.and(a, c) == False{} : Bool}) -> {Nat.is_lt(SW.value(n), sq(1n+v(q))) == True{} : Bool}:
  match a c:
    case False{} _:
      +nl = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), False{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +eq = N.le_antisym(v(q), v(m), hle, N.not_lt_le(v(q), v(m), nl))
      L.subst(Nat, z => {Nat.is_lt(SW.value(n), sq(1n+z)) == True{} : Bool}, v(m), v(q), Equal.sym(Nat, v(q), v(m), eq), hX)
    case True{} False{}:
      +lt = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), True{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +e1 = succ_m(one, h1, q, m, pm, lt)
      +ov = Equal.trans(Bool, Nat.is_lt(SW.value(n), sq(v(U32.add(q, 1)))), X.sq_over(n, U32.add(q, 1)), True{}, Equal.sym(Bool, X.sq_over(n, U32.add(q, 1)), Nat.is_lt(SW.value(n), sq(v(U32.add(q, 1)))), ovs(n, U32.add(q, 1))), Equal.trans(Bool, X.sq_over(n, U32.add(q, 1)), Bool.not(Bool.not(X.sq_over(n, U32.add(q, 1)))), True{}, Equal.sym(Bool, Bool.not(Bool.not(X.sq_over(n, U32.add(q, 1)))), X.sq_over(n, U32.add(q, 1)), not_not(X.sq_over(n, U32.add(q, 1)))), Equal.cong(Bool, Bool, t => Bool.not(t), Bool.not(X.sq_over(n, U32.add(q, 1))), False{}, hcb)))
      L.subst(Nat, z => {Nat.is_lt(SW.value(n), sq(z)) == True{} : Bool}, v(U32.add(q, 1)), 1n+v(q), e1, ov)
    case True{} True{}:
      Empty.absurd({Nat.is_lt(SW.value(n), sq(1n+v(q))) == True{} : Bool}, true_ne_false(hstop))

def up64p(+fu: Nat, +one: Nat, +h1: {one == 1n : Nat}, +n: WU.U64, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +ub: Bool, +hf: {Nat.is_lt(Nat.sub(v(m), v(q)), fu) == True{} : Bool}, +hle: {Nat.is_le(v(q), v(m)) == True{} : Bool}, +hs: {Nat.is_le(sq(v(q)), SW.value(n)) == True{} : Bool}, +hX: {Nat.is_lt(SW.value(n), sq(1n+v(m))) == True{} : Bool}, +hub: {up64_okg(n, q, m) == ub : Bool}) -> {Nat.is_le(sq(v(up64g(fu, n, q, ub, m))), SW.value(n)) == True{} : Bool} & {Nat.is_lt(SW.value(n), sq(1n+v(up64g(fu, n, q, ub, m)))) == True{} : Bool}:
  match fu ub:
    case 0n _:
      Empty.absurd({Nat.is_le(sq(v(up64g(0n, n, q, ub, m))), SW.value(n)) == True{} : Bool} & {Nat.is_lt(SW.value(n), sq(1n+v(up64g(0n, n, q, ub, m)))) == True{} : Bool}, N.lt_zero_absurd(Nat.sub(v(m), v(q)), hf))
    case 1n+g False{}:
      (hs, ustop(one, h1, n, q, m, pm, hle, hX, U32.is_lt(q, m), {==}, Bool.not(X.sq_over(n, U32.add(q, 1))), {==}, hub))
    case 1n+ +g True{}:
      +q1 = U32.add(q, 1)
      +ha = W64S.and_l(U32.is_lt(q, m), Bool.not(X.sq_over(n, q1)), hub)
      +hb = W64S.and_r(U32.is_lt(q, m), Bool.not(X.sq_over(n, q1)), hub)
      +lt = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), True{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +e1 = succ_m(one, h1, q, m, pm, lt)
      +nov = not_t(X.sq_over(n, q1), hb)
      +hs1 = N.not_lt_le(SW.value(n), sq(v(q1)), Equal.trans(Bool, Nat.is_lt(SW.value(n), sq(v(q1))), X.sq_over(n, q1), False{}, Equal.sym(Bool, X.sq_over(n, q1), Nat.is_lt(SW.value(n), sq(v(q1))), ovs(n, q1)), nov))
      +hle1 = L.subst(Nat, z => {Nat.is_le(z, v(m)) == True{} : Bool}, 1n+v(q), v(q1), Equal.sym(Nat, v(q1), 1n+v(q), e1), N.lt_succ_le_succ(v(q), v(m), lt))
      +hf0 = L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, Nat.sub(v(m), v(q)), 1n+Nat.sub(v(m), 1n+v(q)), W64S.sub_succ_r(v(q), v(m), lt), hf)
      +hf1 = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), z), g) == True{} : Bool}, 1n+v(q), v(q1), Equal.sym(Nat, v(q1), 1n+v(q), e1), hf0)
      up64p(g, one, h1, n, q1, m, pm, up64_okg(n, q1, m), hf1, hle1, hs1, hX, {==})

def val0(+x: U32) -> {SW.value(WU.U64{x, 0}) == v(x) : Nat}:
  Equal.trans(Nat, Nat.add(v(x), C.shift(32n, 0n)), Nat.add(v(x), 0n), v(x), Equal.cong(Nat, Nat, z => Nat.add(v(x), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(x)))

def isq_fin(+r: U32, +n: Nat, p: {Nat.is_le(sq(v(r)), n) == True{} : Bool} & {Nat.is_lt(n, sq(1n+v(r))) == True{} : Bool}) -> {v(r) == M.isqrt(n) : Nat}:
  (+a, +c) = p
  W64S.is_isqrt(v(r), n, a, c)

def fit64(+l: U32, +h: U32) -> {C.fits(64n, SW.value(WU.U64{l, h})) == True{} : Bool}:
  WW.limbs_fit(32n, 32n, v(l), v(h), LW.vb(l), LW.vb(h))

def big_g(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +r0: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {v(up64g(1n+v(U32.sub(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), up64_okg(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), m), m)) == M.isqrt(SW.value(WU.U64{l, h})) : Nat}:
  +hs = dn64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), N.lt_succ(v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), {==}, {==})
  +em = m32(one, h1, m, pm)
  +hle = N.lt_succ_le(v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))), v(m), L.subst(Nat, z => {Nat.is_lt(v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))), z) == True{} : Bool}, C.shift(32n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), C.shift(32n, one), em), WW.lt_one(32n, one, h1, v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))), LW.vb(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))))))
  +eS = Equal.trans(Nat, C.shift(64n, one), C.shift(32n, C.shift(32n, one)), sq(1n+v(m)), WW.shift_comp(32n, 32n, one), Equal.trans(Nat, C.shift(32n, C.shift(32n, one)), sq(C.shift(32n, one)), sq(1n+v(m)), WW.shift_mul_one(32n, one, h1, C.shift(32n, one)), Equal.cong(Nat, Nat, z => sq(z), C.shift(32n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), C.shift(32n, one), em))))
  +hX = L.subst(Nat, z => {Nat.is_lt(SW.value(WU.U64{l, h}), z) == True{} : Bool}, C.shift(64n, one), sq(1n+v(m)), eS, WW.lt_one(64n, one, h1, SW.value(WU.U64{l, h}), fit64(l, h)))
  +esub = U.sub_nat(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), hle)
  +hf = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), 1n+z) == True{} : Bool}, Nat.sub(v(m), v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), v(U32.sub(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), Equal.sym(Nat, v(U32.sub(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), Nat.sub(v(m), v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), esub), N.lt_succ(Nat.sub(v(m), v(X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))))))
  pr = up64p(1n+v(U32.sub(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), one, h1, WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), m, pm, up64_okg(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), m), hf, hle, hs, hX, {==})
  isq_fin(up64g(1n+v(U32.sub(m, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), up64_okg(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), m), m), SW.value(WU.U64{l, h}), pr)

def big_v(+l: U32, +h: U32, +r0: U32) -> {SW.value(X.isqrt_big(WU.U64{l, h}, r0)) == M.isqrt(SW.value(WU.U64{l, h})) : Nat}:
  +ei = Equal.cong(U32, Nat, z => v(z), X.isqrt64_fix(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))), up64g(1n+v(U32.sub(4294967295, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), up64_okg(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), 4294967295), 4294967295), impl_up64(1n+v(U32.sub(4294967295, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), X.up64_ok(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))))
  Equal.trans(Nat, SW.value(WU.U64{X.isqrt64_fix(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))))), 0}), v(X.isqrt64_fix(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), M.isqrt(SW.value(WU.U64{l, h})), val0(X.isqrt64_fix(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), Equal.trans(Nat, v(X.isqrt64_fix(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), v(up64g(1n+v(U32.sub(4294967295, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))))), WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), up64_okg(WU.U64{l, h}, X.down64(1n+v(X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0})))), WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))), X.sq_over(WU.U64{l, h}, X.q_clamp(X.half(X.add(X.fst_q(X.div32(WU.U64{l, h}, r0)), WU.U64{r0, 0}))))), 4294967295), 4294967295)), M.isqrt(SW.value(WU.U64{l, h})), ei, big_g(1n, {==}, l, h, r0, 4294967295, {==})))

def isqrt_c(+l: U32, +h: U32, +z: Bool, +hz: {U32.is_zero(h) == z : Bool}) -> {SW.value(X.isqrt_pick(WU.U64{l, h}, z)) == M.isqrt(SW.value(WU.U64{l, h})) : Nat}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(v(h), 0n, Equal.trans(Bool, Nat.is_eq(v(h), 0n), U32.is_zero(h), True{}, Equal.sym(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h)), hz))
      +ev = Equal.trans(Nat, SW.value(WU.U64{l, h}), Nat.add(v(l), C.shift(32n, 0n)), v(l), Equal.cong(Nat, Nat, t => Nat.add(v(l), C.shift(32n, t)), v(h), 0n, e0), Equal.trans(Nat, Nat.add(v(l), C.shift(32n, 0n)), Nat.add(v(l), 0n), v(l), Equal.cong(Nat, Nat, t => Nat.add(v(l), t), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(l))))
      Equal.trans(Nat, SW.value(WU.U64{X.isqrt32(l), 0}), v(X.isqrt32(l)), M.isqrt(SW.value(WU.U64{l, h})), val0(X.isqrt32(l)), Equal.trans(Nat, v(X.isqrt32(l)), M.isqrt(v(l)), M.isqrt(SW.value(WU.U64{l, h})), W64S.isqrt32_value(l), Equal.cong(Nat, Nat, t => M.isqrt(t), v(l), SW.value(WU.U64{l, h}), Equal.sym(Nat, SW.value(WU.U64{l, h}), v(l), ev))))
    case False{}:
      big_v(l, h, X.isqrt_est(F32.sqrt(F32.add(F32.mul(U32.to_f32(h), 4294967296.0), U32.to_f32(l)))))

def isqrt_value(+n: WU.U64) -> SW.Isqrt.value(n):
  match n:
    case WU.U64{+l, +h}:
      isqrt_c(l, h, U32.is_zero(h), {==})
