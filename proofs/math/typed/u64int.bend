import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/generic.bend as SG
import ../../../spec/math/natural.bend as NS
import ../../../src/math/generic.bend as G
import ../../../src/math/num.bend as NM
import ../../../src/math/natural.bend as M
import ../../../src/math/instances.bend as I
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./width.bend as WW
import ./u32.bend as U32P
import ./u64laws.bend as LW
import ../../../src/math/u64.bend as WU
import ./natfuel.bend as NF
import ./combnat.bend as CN
import ../../lib/arith.bend as AR2
import ../natural/fact.bend as FA
import ../natural/roots.bend as RT
import ../natural/bits.bend as BT
import ../../../src/math/pow2.bend as P2
import ../pow2/pow2.bend as PP
import ../../../spec/math/natural.bend as S
import ../natural/inverse.bend as IV
import ../natural/proof.bend as NP

# The integer clauses of spec/math/generic.bend at the U64 instance, proved
# from the instance laws of spec/math/instances.bend (proofs/math/typed/
# u32laws.bend): each generic function is simulated on the values and
# compared with the proved Nat function of natural.bend, as Mathlib proves a
# function on a type through its value (Mathlib's Fin / UInt32 lemmas via
# toNat). The same text, read with the U64 laws, proves them at U64.

def v(+x: WU.U64) -> Nat:
  SG.u64_val(x)

def of(+n: Nat) -> WU.U64:
  SG.u64_of(n)

# x is the WU.U64 of its value
def as_of(+x: WU.U64, +n: Nat, +h: {v(x) == n : Nat}) -> {x == of(n) : WU.U64}:
  Equal.trans(WU.U64, x, of(v(x)), of(n), Equal.sym(WU.U64, of(v(x)), x, LW.rt(x)), Equal.cong(Nat, WU.U64, t => of(t), v(x), n, h))

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  U32P.true_ne_false(h)

# ---- isqrt, abs ----

def isqrt_agrees(+n: WU.U64) -> SG.Isqrt.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, n):
  as_of(I.u64_op(NM.Sqrt{n}), M.isqrt(v(n)), LW.ops_sqrt(n))

def abs_identity(+x: WU.U64) -> SG.Abs.identity(~WU.U64, ~I.u64_op, ~I.u64_is, x):
  LW.ops_abs(x)

# ---- divmod ----

def dm(+a: WU.U64, +b: WU.U64, +c: Bool, +hc: {I.u64_is(NM.IsZero{b}) == c : Bool}, +nb: Nat, +hnb: {v(b) == nb : Nat}) -> {G.divmod_ok(~WU.U64, ~I.u64_op, a, b, c) == SG.lift_qr(~WU.U64, ~SG.u64_of, M.divmod(v(a), nb)) : Result<&2, &2, NM.NumError, G.QuotRem<WU.U64>>}:
  match c nb:
    case True{} 0n:
      {==}
    case False{} 0n:
      +hz = Equal.trans(Bool, False{}, I.u64_is(NM.IsZero{b}), Nat.is_eq(0n, 0n), Equal.sym(Bool, I.u64_is(NM.IsZero{b}), False{}, hc), Equal.trans(Bool, I.u64_is(NM.IsZero{b}), Nat.is_eq(v(b), 0n), Nat.is_eq(0n, 0n), LW.tests_is_zero(b), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 0n, hnb)))
      Empty.absurd({G.divmod_ok(~WU.U64, ~I.u64_op, a, b, False{}) == SG.lift_qr(~WU.U64, ~SG.u64_of, M.divmod(v(a), 0n)) : Result<&2, &2, NM.NumError, G.QuotRem<WU.U64>>}, true_ne_false(Equal.sym(Bool, False{}, True{}, hz)))
    case True{} 1n+ +bp:
      +hz = Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{b}), Nat.is_eq(1n+bp, 0n), Equal.sym(Bool, I.u64_is(NM.IsZero{b}), True{}, hc), Equal.trans(Bool, I.u64_is(NM.IsZero{b}), Nat.is_eq(v(b), 0n), Nat.is_eq(1n+bp, 0n), LW.tests_is_zero(b), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 1n+bp, hnb)))
      Empty.absurd({G.divmod_ok(~WU.U64, ~I.u64_op, a, b, True{}) == SG.lift_qr(~WU.U64, ~SG.u64_of, M.divmod(v(a), 1n+bp)) : Result<&2, &2, NM.NumError, G.QuotRem<WU.U64>>}, true_ne_false(hz))
    case False{} 1n+ +bp:
      +hq = Equal.trans(Bool, Nat.is_eq(v(b), 0n), Nat.is_eq(1n+bp, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 1n+bp, hnb), {==})
      +eq = as_of(I.u64_op(NM.Quot{a, b}), Nat.div(v(a), 1n+bp), Equal.trans(Nat, v(I.u64_op(NM.Quot{a, b})), Nat.div(v(a), v(b)), Nat.div(v(a), 1n+bp), LW.ops_quot(a, b, hq), Equal.cong(Nat, Nat, t => Nat.div(v(a), t), v(b), 1n+bp, hnb)))
      +er = as_of(I.u64_op(NM.Rem{a, b}), Nat.mod(v(a), 1n+bp), Equal.trans(Nat, v(I.u64_op(NM.Rem{a, b})), Nat.mod(v(a), v(b)), Nat.mod(v(a), 1n+bp), LW.ops_rem(a, b, hq), Equal.cong(Nat, Nat, t => Nat.mod(v(a), t), v(b), 1n+bp, hnb)))
      %Equal.sym(WU.U64, I.u64_op(NM.Quot{a, b}), of(Nat.div(v(a), 1n+bp)), eq) : {Done{G.TQR{_, I.u64_op(NM.Rem{a, b})}} == Done{G.TQR{of(Nat.div(v(a), 1n+bp)), of(Nat.mod(v(a), 1n+bp))}} : Result<&2, &2, NM.NumError, G.QuotRem<WU.U64>>}
      %Equal.sym(WU.U64, I.u64_op(NM.Rem{a, b}), of(Nat.mod(v(a), 1n+bp)), er) : {Done{G.TQR{of(Nat.div(v(a), 1n+bp)), _}} == Done{G.TQR{of(Nat.div(v(a), 1n+bp)), of(Nat.mod(v(a), 1n+bp))}} : Result<&2, &2, NM.NumError, G.QuotRem<WU.U64>>}
      {==}

def divmod_agrees(+a: WU.U64, +b: WU.U64) -> SG.DivMod.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, a, b):
  dm(a, b, I.u64_is(NM.IsZero{b}), {==}, v(b), {==})

# ---- selections ----

def lt_of(+a: WU.U64, +b: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{a, b}) == c : Bool}) -> {Nat.is_lt(v(a), v(b)) == c : Bool}:
  Equal.trans(Bool, Nat.is_lt(v(a), v(b)), I.u64_is(NM.Lt{a, b}), c, Equal.sym(Bool, I.u64_is(NM.Lt{a, b}), Nat.is_lt(v(a), v(b)), LW.tests_lt(a, b)), hc)

def min_c(+a: WU.U64, +b: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{b, a}) == c : Bool}) -> {G.pick(WU.U64, c, b, a) == of(Nat.min(v(a), v(b))) : WU.U64}:
  match c:
    case True{}:
      as_of(b, Nat.min(v(a), v(b)), Equal.sym(Nat, Nat.min(v(a), v(b)), v(b), U32P.min_of_lt(v(a), v(b), lt_of(b, a, True{}, hc))))
    case False{}:
      as_of(a, Nat.min(v(a), v(b)), Equal.sym(Nat, Nat.min(v(a), v(b)), v(a), U32P.min_of_ge(v(a), v(b), lt_of(b, a, False{}, hc))))

def min_agrees(+a: WU.U64, +b: WU.U64) -> SG.Min.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, a, b):
  min_c(a, b, I.u64_is(NM.Lt{b, a}), {==})

def max_c(+a: WU.U64, +b: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{a, b}) == c : Bool}) -> {G.pick(WU.U64, c, b, a) == of(Nat.max(v(a), v(b))) : WU.U64}:
  match c:
    case True{}:
      as_of(b, Nat.max(v(a), v(b)), Equal.sym(Nat, Nat.max(v(a), v(b)), v(b), U32P.max_of_lt(v(a), v(b), lt_of(a, b, True{}, hc))))
    case False{}:
      as_of(a, Nat.max(v(a), v(b)), Equal.sym(Nat, Nat.max(v(a), v(b)), v(a), U32P.max_of_ge(v(a), v(b), lt_of(a, b, False{}, hc))))

def max_agrees(+a: WU.U64, +b: WU.U64) -> SG.Max.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, a, b):
  max_c(a, b, I.u64_is(NM.Lt{a, b}), {==})

def max_val_c(+x: WU.U64, +lo: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{x, lo}) == c : Bool}) -> {v(G.pick(WU.U64, c, lo, x)) == Nat.max(v(x), v(lo)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.max(v(x), v(lo)), v(lo), U32P.max_of_lt(v(x), v(lo), lt_of(x, lo, True{}, hc)))
    case False{}:
      Equal.sym(Nat, Nat.max(v(x), v(lo)), v(x), U32P.max_of_ge(v(x), v(lo), lt_of(x, lo, False{}, hc)))

def zero_v() -> {v(I.u64_op(NM.ZeroOp{})) == 0n : Nat}:
  LW.ops_zero()

def one_v() -> {v(I.u64_op(NM.One{})) == 1n : Nat}:
  LW.ops_one()

def sign_b(+x: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{x, I.u64_op(NM.ZeroOp{})}) == c : Bool}, +hz: {Nat.is_lt(0n, v(x)) == False{} : Bool}) -> {G.sign_below(~WU.U64, ~I.u64_op, ~I.u64_is, x, c) == of(Nat.min(v(x), 1n)) : WU.U64}:
  match c:
    case True{}:
      +hl = L.subst(Nat, z => {Nat.is_lt(v(x), z) == True{} : Bool}, v(I.u64_op(NM.ZeroOp{})), 0n, zero_v(), lt_of(x, I.u64_op(NM.ZeroOp{}), True{}, hc))
      Empty.absurd({G.sign_below(~WU.U64, ~I.u64_op, ~I.u64_is, x, True{}) == of(Nat.min(v(x), 1n)) : WU.U64}, N.lt_zero_absurd(v(x), hl))
    case False{}:
      as_of(x, Nat.min(v(x), 1n), Equal.sym(Nat, Nat.min(v(x), 1n), v(x), N.min_left(v(x), 1n, U32P.zero_lt_one(v(x), hz))))

def sign_a(+x: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{I.u64_op(NM.ZeroOp{}), x}) == c : Bool}) -> {G.sign_above(~WU.U64, ~I.u64_op, ~I.u64_is, x, c) == of(Nat.min(v(x), 1n)) : WU.U64}:
  match c:
    case True{}:
      +hl = L.subst(Nat, z => {Nat.is_lt(z, v(x)) == True{} : Bool}, v(I.u64_op(NM.ZeroOp{})), 0n, zero_v(), lt_of(I.u64_op(NM.ZeroOp{}), x, True{}, hc))
      +em = N.min_right(v(x), 1n, U32P.pos_ge_one(v(x), hl))
      Equal.trans(WU.U64, I.u64_op(NM.One{}), of(1n), of(Nat.min(v(x), 1n)), as_of(I.u64_op(NM.One{}), 1n, one_v()), Equal.cong(Nat, WU.U64, t => of(t), 1n, Nat.min(v(x), 1n), Equal.sym(Nat, Nat.min(v(x), 1n), 1n, em)))
    case False{}:
      +hl = L.subst(Nat, z => {Nat.is_lt(z, v(x)) == False{} : Bool}, v(I.u64_op(NM.ZeroOp{})), 0n, zero_v(), lt_of(I.u64_op(NM.ZeroOp{}), x, False{}, hc))
      sign_b(x, I.u64_is(NM.Lt{x, I.u64_op(NM.ZeroOp{})}), {==}, hl)

def sign_agrees(+x: WU.U64) -> SG.Sign.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, x):
  sign_a(x, I.u64_is(NM.Lt{I.u64_op(NM.ZeroOp{}), x}), {==})

def clamp_d(+x: WU.U64, +lo: WU.U64, +hi: WU.U64, +c: Bool) -> {G.clamp_ok(~WU.U64, ~I.u64_op, ~I.u64_is, x, lo, hi, c) == SG.lift(~WU.U64, ~SG.u64_of, M.clamp_ok(v(x), v(lo), v(hi), c)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c:
    case True{}:
      {==}
    case False{}:
      +m = G.max(~WU.U64, ~I.u64_op, ~I.u64_is, x, lo)
      +em = max_val_c(x, lo, I.u64_is(NM.Lt{x, lo}), {==})
      %Equal.sym(WU.U64, G.pick(WU.U64, I.u64_is(NM.Lt{hi, m}), hi, m), of(Nat.min(v(m), v(hi))), min_c(m, hi, I.u64_is(NM.Lt{hi, m}), {==})) : {Done{_} == Done{of(Nat.min(Nat.max(v(x), v(lo)), v(hi)))} : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Nat, v(m), Nat.max(v(x), v(lo)), em) : {Done{of(Nat.min(_, v(hi)))} == Done{of(Nat.min(Nat.max(v(x), v(lo)), v(hi)))} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}

def clamp_c(+x: WU.U64, +lo: WU.U64, +hi: WU.U64, +c: Bool, +hc: {I.u64_is(NM.Lt{hi, lo}) == c : Bool}) -> {G.clamp_ok(~WU.U64, ~I.u64_op, ~I.u64_is, x, lo, hi, c) == SG.lift(~WU.U64, ~SG.u64_of, M.clamp(v(x), v(lo), v(hi))) : Result<&2, &2, NM.NumError, WU.U64>}:
  %Equal.sym(Bool, Nat.is_lt(v(hi), v(lo)), c, lt_of(hi, lo, c, hc)) : {G.clamp_ok(~WU.U64, ~I.u64_op, ~I.u64_is, x, lo, hi, c) == SG.lift(~WU.U64, ~SG.u64_of, M.clamp_ok(v(x), v(lo), v(hi), _)) : Result<&2, &2, NM.NumError, WU.U64>}
  clamp_d(x, lo, hi, c)

def clamp_agrees(+x: WU.U64, +lo: WU.U64, +hi: WU.U64) -> SG.Clamp.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, x, lo, hi):
  clamp_c(x, lo, hi, I.u64_is(NM.Lt{hi, lo}), {==})

# ---- gcd: Euclid on the values, then enough fuel ----

def gcd_sim(+f: Nat, +a: WU.U64, +b: WU.U64, +cz: Bool, +nb: Nat, +hcz: {I.u64_is(NM.IsZero{b}) == cz : Bool}, +hnb: {v(b) == nb : Nat}) -> {v(G.gcd_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, a, (b, cz))) == M.gcd_go(f, v(a), nb) : Nat}:
  match f cz nb:
    case 0n _ _:
      {==}
    case 1n+g True{} 0n:
      {==}
    case 1n+g True{} 1n+bp:
      +hz = Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{b}), Nat.is_eq(1n+bp, 0n), Equal.sym(Bool, I.u64_is(NM.IsZero{b}), True{}, hcz), Equal.trans(Bool, I.u64_is(NM.IsZero{b}), Nat.is_eq(v(b), 0n), Nat.is_eq(1n+bp, 0n), LW.tests_is_zero(b), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 1n+bp, hnb)))
      Empty.absurd({v(G.gcd_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, a, (b, True{}))) == M.gcd_go(1n+g, v(a), 1n+bp) : Nat}, true_ne_false(hz))
    case 1n+g False{} 0n:
      +hz = Equal.trans(Bool, False{}, I.u64_is(NM.IsZero{b}), Nat.is_eq(0n, 0n), Equal.sym(Bool, I.u64_is(NM.IsZero{b}), False{}, hcz), Equal.trans(Bool, I.u64_is(NM.IsZero{b}), Nat.is_eq(v(b), 0n), Nat.is_eq(0n, 0n), LW.tests_is_zero(b), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 0n, hnb)))
      Empty.absurd({v(G.gcd_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, a, (b, False{}))) == M.gcd_go(1n+g, v(a), 0n) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, hz)))
    case 1n+ +g False{} 1n+ +bp:
      +rm = I.u64_op(NM.Rem{a, b})
      +hq = Equal.trans(Bool, Nat.is_eq(v(b), 0n), Nat.is_eq(1n+bp, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 1n+bp, hnb), {==})
      +erm = Equal.trans(Nat, v(rm), Nat.mod(v(a), v(b)), Nat.mod(v(a), 1n+bp), LW.ops_rem(a, b, hq), Equal.cong(Nat, Nat, t => Nat.mod(v(a), t), v(b), 1n+bp, hnb))
      +ih = gcd_sim(g, b, rm, I.u64_is(NM.IsZero{rm}), v(rm), {==}, {==})
      Equal.trans(Nat, v(G.gcd_go(~WU.U64, ~I.u64_op, ~I.u64_is, g, b, (rm, I.u64_is(NM.IsZero{rm})))), M.gcd_go(g, v(b), v(rm)), M.gcd_go(g, 1n+bp, Nat.mod(v(a), 1n+bp)), ih, Equal.trans(Nat, M.gcd_go(g, v(b), v(rm)), M.gcd_go(g, 1n+bp, v(rm)), M.gcd_go(g, 1n+bp, Nat.mod(v(a), 1n+bp)), Equal.cong(Nat, Nat, t => M.gcd_go(g, t, v(rm)), v(b), 1n+bp, hnb), Equal.cong(Nat, Nat, t => M.gcd_go(g, 1n+bp, t), v(rm), Nat.mod(v(a), 1n+bp), erm)))

def gcd_val_k(+k: Nat, +hk: {k == 64n : Nat}, +a: WU.U64, +b: WU.U64) -> {v(G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)) == M.gcd(v(a), v(b)) : Nat}:
  +hk2 = L.subst(Nat, z => {Nat.is_le(1n+Nat.double(z), 140n) == True{} : Bool}, 64n, k, Equal.sym(Nat, k, 64n, hk), {==})
  Equal.trans(Nat, v(G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)), M.gcd_go(140n, v(a), v(b)), M.gcd(v(a), v(b)), gcd_sim(140n, a, b, I.u64_is(NM.IsZero{b}), v(b), {==}, {==}), NF.gcd_140(k, v(a), v(b), hk2, LW.val_lt(k, hk, b)))

def gcd_val(+a: WU.U64, +b: WU.U64) -> {v(G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)) == M.gcd(v(a), v(b)) : Nat}:
  gcd_val_k(64n, {==}, a, b)

def gcd_agrees(+a: WU.U64, +b: WU.U64) -> SG.Gcd.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, a, b):
  as_of(G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b), M.gcd(v(a), v(b)), gcd_val(a, b))

# ---- gcd_all: the fold on values ----

def vals(xs: List<&2, WU.U64>) -> List<&2, Nat>:
  SG.vals(~WU.U64, ~SG.u64_val, xs)

def gall(+xs: List<&2, WU.U64>, +acc: WU.U64) -> {v(G.gcd_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, acc)) == M.gcd_all_go(vals(xs), v(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +g = G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, acc, x)
      Equal.trans(Nat, v(G.gcd_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, t, g)), M.gcd_all_go(vals(t), v(g)), M.gcd_all_go(vals(t), M.gcd(v(acc), v(x))), gall(t, g), Equal.cong(Nat, Nat, z => M.gcd_all_go(vals(t), z), v(g), M.gcd(v(acc), v(x)), gcd_val(acc, x)))

def gcd_all_agrees(+xs: List<&2, WU.U64>) -> SG.GcdAll.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, xs):
  +z = I.u64_op(NM.ZeroOp{})
  as_of(G.gcd_all(~WU.U64, ~I.u64_op, ~I.u64_is, xs), M.gcd_all(vals(xs)), Equal.trans(Nat, v(G.gcd_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, z)), M.gcd_all_go(vals(xs), v(z)), M.gcd_all_go(vals(xs), 0n), gall(xs, z), Equal.cong(Nat, Nat, t => M.gcd_all_go(vals(xs), t), v(z), 0n, zero_v())))

# ---- a checked product ----

def mo_of(+q: WU.U64, +b: WU.U64, +n: Nat, +hn: {Nat.mul(v(q), v(b)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {I.u64_is(NM.MulOver{q, b}) == Bool.not(c) : Bool}:
  +e1 = Equal.trans(Bool, I.u64_is(NM.MulOver{q, b}), Bool.not(C.fits(64n, Nat.mul(v(q), v(b)))), Bool.not(C.fits(64n, n)), LW.tests_mul_over(q, b), Equal.cong(Nat, Bool, t => Bool.not(C.fits(64n, t)), Nat.mul(v(q), v(b)), n, hn))
  Equal.trans(Bool, I.u64_is(NM.MulOver{q, b}), Bool.not(C.fits(64n, n)), Bool.not(c), e1, Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, n), c, hc))

def cm(+q: WU.U64, +b: WU.U64, +n: Nat, +hn: {Nat.mul(v(q), v(b)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {G.ok(WU.U64, G.cmul(~WU.U64, ~I.u64_op, ~I.u64_is, q, b)) == SG.checked(~WU.U64, ~SG.u64_of, 64n, n) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c:
    case True{}:
      +hmo2 = mo_of(q, b, n, hn, True{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.MulOver{q, b}), False{}, hmo2) : {G.ok(WU.U64, G.fits(WU.U64, _, I.u64_op(NM.Mul{q, b}))) == SG.checked(~WU.U64, ~SG.u64_of, 64n, n) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Bool, C.fits(64n, n), True{}, hc) : {Done{I.u64_op(NM.Mul{q, b})} == SG.checked_pick(~WU.U64, ~SG.u64_of, n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(WU.U64, I.u64_op(NM.Mul{q, b}), of(n), as_of(I.u64_op(NM.Mul{q, b}), n, Equal.trans(Nat, v(I.u64_op(NM.Mul{q, b})), Nat.mul(v(q), v(b)), n, LW.ops_mul(q, b, hmo2), hn))) : {Done{_} == Done{of(n)} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case False{}:
      +hmo = mo_of(q, b, n, hn, False{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.MulOver{q, b}), True{}, hmo) : {G.ok(WU.U64, G.fits(WU.U64, _, I.u64_op(NM.Mul{q, b}))) == SG.checked(~WU.U64, ~SG.u64_of, 64n, n) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Bool, C.fits(64n, n), False{}, hc) : {Fail{NM.Overflow{}} == SG.checked_pick(~WU.U64, ~SG.u64_of, n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      {==}

# ---- lcm ----

def gpos_d(+ap: Nat, +b: Nat, d: NS.dvd(M.gcd(1n+ap, b), 1n+ap), +g: Nat, +hg: {M.gcd(1n+ap, b) == g : Nat}) -> {Nat.is_eq(M.gcd(1n+ap, b), 0n) == False{} : Bool}:
  (k, e) = d
  match g:
    case 0n:
      +e0 = Equal.trans(Nat, 1n+ap, Nat.mul(k, M.gcd(1n+ap, b)), 0n, e, Equal.trans(Nat, Nat.mul(k, M.gcd(1n+ap, b)), Nat.mul(k, 0n), 0n, Equal.cong(Nat, Nat, t => Nat.mul(k, t), M.gcd(1n+ap, b), 0n, hg), NA.mul_zero(k)))
      Empty.absurd({Nat.is_eq(M.gcd(1n+ap, b), 0n) == False{} : Bool}, N.succ_zero(ap, e0))
    case 1n+gp:
      %Equal.sym(Nat, M.gcd(1n+ap, b), 1n+gp, hg) : {Nat.is_eq(_, 0n) == False{} : Bool}
      {==}

# gcd of a positive number is positive
def gpos(+ap: Nat, +b: Nat) -> {Nat.is_eq(M.gcd(1n+ap, b), 0n) == False{} : Bool}:
  gpos_d(ap, b, NP.divides_left(1n+ap, b), M.gcd(1n+ap, b), {==})

def iz(+a: WU.U64, +n: Nat, +h: {v(a) == n : Nat}) -> {I.u64_is(NM.IsZero{a}) == Nat.is_eq(n, 0n) : Bool}:
  Equal.trans(Bool, I.u64_is(NM.IsZero{a}), Nat.is_eq(v(a), 0n), Nat.is_eq(n, 0n), LW.tests_is_zero(a), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(a), n, h))

def lcmc(+a: WU.U64, +b: WU.U64, +c: Bool, +na: Nat, +nb: Nat, +hc: {Bool.or(I.u64_is(NM.IsZero{a}), I.u64_is(NM.IsZero{b})) == c : Bool}, +hna: {v(a) == na : Nat}, +hnb: {v(b) == nb : Nat}) -> {G.lcm_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, c) == SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(na, nb)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c na nb:
    case True{} 0n _:
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.ZeroOp{}), of(0n), as_of(I.u64_op(NM.ZeroOp{}), 0n, zero_v()))
    case True{} 1n+ap 0n:
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.ZeroOp{}), of(0n), as_of(I.u64_op(NM.ZeroOp{}), 0n, zero_v()))
    case True{} 1n+ +ap 1n+ +bp:
      Empty.absurd({G.lcm_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, True{}) == SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(1n+ap, 1n+bp)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, Bool.or(False{}, I.u64_is(NM.IsZero{b})), False{}, Equal.sym(Bool, Bool.or(False{}, I.u64_is(NM.IsZero{b})), True{}, L.subst(Bool, t => {Bool.or(t, I.u64_is(NM.IsZero{b})) == True{} : Bool}, I.u64_is(NM.IsZero{a}), False{}, iz(a, 1n+ap, hna), hc)), iz(b, 1n+bp, hnb))))
    case False{} 0n _:
      Empty.absurd({G.lcm_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, False{}) == SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(0n, nb)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, Bool.or(True{}, I.u64_is(NM.IsZero{b})), False{}, {==}, L.subst(Bool, t => {Bool.or(t, I.u64_is(NM.IsZero{b})) == False{} : Bool}, I.u64_is(NM.IsZero{a}), True{}, iz(a, 0n, hna), hc))))
    case False{} 1n+ +ap 0n:
      +h2 = L.subst(Bool, t => {Bool.or(t, I.u64_is(NM.IsZero{b})) == False{} : Bool}, I.u64_is(NM.IsZero{a}), False{}, iz(a, 1n+ap, hna), hc)
      Empty.absurd({G.lcm_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, b, False{}) == SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(1n+ap, 0n)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{b}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{b}), True{}, iz(b, 0n, hnb)), h2)))
    case False{} 1n+ +ap 1n+ +bp:
      +g = G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, a, b)
      +gg = M.gcd(1n+ap, 1n+bp)
      +eg = Equal.trans(Nat, v(g), M.gcd(v(a), v(b)), gg, gcd_val(a, b), Equal.trans(Nat, M.gcd(v(a), v(b)), M.gcd(1n+ap, v(b)), gg, Equal.cong(Nat, Nat, t => M.gcd(t, v(b)), v(a), 1n+ap, hna), Equal.cong(Nat, Nat, t => M.gcd(1n+ap, t), v(b), 1n+bp, hnb)))
      +hgz = L.subst(Nat, t => {Nat.is_eq(t, 0n) == False{} : Bool}, gg, v(g), Equal.sym(Nat, v(g), gg, eg), gpos(ap, 1n+bp))
      +q = I.u64_op(NM.Quot{a, g})
      +eq = Equal.trans(Nat, v(q), Nat.div(v(a), v(g)), Nat.div(1n+ap, gg), LW.ops_quot(a, g, hgz), Equal.trans(Nat, Nat.div(v(a), v(g)), Nat.div(1n+ap, v(g)), Nat.div(1n+ap, gg), Equal.cong(Nat, Nat, t => Nat.div(t, v(g)), v(a), 1n+ap, hna), Equal.cong(Nat, Nat, t => Nat.div(1n+ap, t), v(g), gg, eg)))
      +n = Nat.mul(Nat.div(1n+ap, gg), 1n+bp)
      +hn = Equal.trans(Nat, Nat.mul(v(q), v(b)), Nat.mul(Nat.div(1n+ap, gg), v(b)), n, Equal.cong(Nat, Nat, t => Nat.mul(t, v(b)), v(q), Nat.div(1n+ap, gg), eq), Equal.cong(Nat, Nat, t => Nat.mul(Nat.div(1n+ap, gg), t), v(b), 1n+bp, hnb))
      cm(q, b, n, hn, C.fits(64n, n), {==})

def lcm_checked(+a: WU.U64, +b: WU.U64) -> SG.Lcm.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, a, b):
  lcmc(a, b, Bool.or(I.u64_is(NM.IsZero{a}), I.u64_is(NM.IsZero{b})), v(a), v(b), {==}, {==}, {==})

# ---- lcm_all: the fold stops at the first overflow ----

def lall_fail(xs: List<&2, WU.U64>, +e: NM.NumError) -> {G.lcm_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, Fail{e}) == Fail{e} : Result<&2, &2, NM.NumError, WU.U64>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def lgo_false(xs: List<&2, Nat>, +acc: Nat) -> {SG.lcm_go(64n, xs, acc, False{}) == (acc, False{}) : Nat & Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# the fold on an accumulator r == checked(n) (c == fits(32, n))
def lall(+xs: List<&2, WU.U64>, +r: Result<&2, &2, NM.NumError, WU.U64>, +n: Nat, +c: Bool, +hr: {r == SG.checked_pick(~WU.U64, ~SG.u64_of, n, c) : Result<&2, &2, NM.NumError, WU.U64>}, +hc: {C.fits(64n, n) == c : Bool}) -> {G.lcm_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, r) == SG.prefix_fin(~WU.U64, ~SG.u64_of, SG.lcm_go(64n, vals(xs), n, c)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match xs c:
    case Nil{} _:
      hr
    case Con{x, t} False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, r, Fail{NM.Overflow{}}, hr) : {G.lcm_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _) == Fail{NM.Overflow{}} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Con{+x, +t} True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, WU.U64>, r, Done{of(n)}, hr) : {G.lcm_all_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _) == SG.prefix_fin(~WU.U64, ~SG.u64_of, SG.lcm_go(64n, vals(t), M.lcm(n, v(x)), C.fits(64n, M.lcm(n, v(x))))) : Result<&2, &2, NM.NumError, WU.U64>}
      +en = LW.vo(n, hc)
      +el = Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.lcm(~WU.U64, ~I.u64_op, ~I.u64_is, of(n), x), SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(v(of(n)), v(x))), SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(n, v(x))), lcm_checked(of(n), x), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, z => SG.checked(~WU.U64, ~SG.u64_of, 64n, M.lcm(z, v(x))), v(of(n)), n, en))
      lall(t, G.lcm(~WU.U64, ~I.u64_op, ~I.u64_is, of(n), x), M.lcm(n, v(x)), C.fits(64n, M.lcm(n, v(x))), el, {==})

def lcm_all_checked(+xs: List<&2, WU.U64>) -> SG.LcmAll.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, xs):
  lall(xs, Done{I.u64_op(NM.One{})}, 1n, True{}, Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.One{}), of(1n), as_of(I.u64_op(NM.One{}), 1n, one_v())), {==})

# ---- prod: the fold stops at the first overflow ----

def cmul_rel(+q: WU.U64, +x: WU.U64, +n: Nat, +hn: {Nat.mul(v(q), v(x)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {G.cmul(~WU.U64, ~I.u64_op, ~I.u64_is, q, x) == G.fits(WU.U64, Bool.not(c), of(n)) : Maybe<&2, WU.U64>}:
  match c:
    case True{}:
      +hmo = mo_of(q, x, n, hn, True{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.MulOver{q, x}), False{}, hmo) : {G.fits(WU.U64, _, I.u64_op(NM.Mul{q, x})) == Some{of(n)} : Maybe<&2, WU.U64>}
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, I.u64_op(NM.Mul{q, x}), of(n), as_of(I.u64_op(NM.Mul{q, x}), n, Equal.trans(Nat, v(I.u64_op(NM.Mul{q, x})), Nat.mul(v(q), v(x)), n, LW.ops_mul(q, x, hmo), hn)))
    case False{}:
      %Equal.sym(Bool, I.u64_is(NM.MulOver{q, x}), True{}, mo_of(q, x, n, hn, False{}, hc)) : {G.fits(WU.U64, _, I.u64_op(NM.Mul{q, x})) == None{} : Maybe<&2, WU.U64>}
      {==}

def pal(+xs: List<&2, WU.U64>, +r: Maybe<&2, WU.U64>, +n: Nat, +c: Bool, +hr: {r == G.fits(WU.U64, Bool.not(c), of(n)) : Maybe<&2, WU.U64>}, +hc: {C.fits(64n, n) == c : Bool}) -> {G.ok(WU.U64, G.prod_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, r)) == SG.prefix_fin(~WU.U64, ~SG.u64_of, SG.prod_go(64n, vals(xs), n, c)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match xs c:
    case Nil{} True{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, Some{of(n)}, hr) : {G.ok(WU.U64, _) == Done{of(n)} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Nil{} False{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, None{}, hr) : {G.ok(WU.U64, _) == Fail{NM.Overflow{}} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Con{x, t} False{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, None{}, hr) : {G.ok(WU.U64, G.prod_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _)) == Fail{NM.Overflow{}} : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Con{+x, +t} True{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, Some{of(n)}, hr) : {G.ok(WU.U64, G.prod_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _)) == SG.prefix_fin(~WU.U64, ~SG.u64_of, SG.prod_go(64n, vals(t), Nat.mul(n, v(x)), C.fits(64n, Nat.mul(n, v(x))))) : Result<&2, &2, NM.NumError, WU.U64>}
      +hn = Equal.cong(Nat, Nat, z => Nat.mul(z, v(x)), v(of(n)), n, LW.vo(n, hc))
      pal(t, G.cmul(~WU.U64, ~I.u64_op, ~I.u64_is, of(n), x), Nat.mul(n, v(x)), C.fits(64n, Nat.mul(n, v(x))), cmul_rel(of(n), x, Nat.mul(n, v(x)), hn, C.fits(64n, Nat.mul(n, v(x))), {==}), {==})

def prod_checked(+xs: List<&2, WU.U64>) -> SG.Prod.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, xs):
  pal(xs, Some{I.u64_op(NM.One{})}, 1n, True{}, Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, I.u64_op(NM.One{}), of(1n), as_of(I.u64_op(NM.One{}), 1n, one_v())), {==})

# ---- sum: the partial sums only grow ----

def ao_of(+q: WU.U64, +b: WU.U64, +n: Nat, +hn: {Nat.add(v(q), v(b)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {I.u64_is(NM.AddOver{q, b}) == Bool.not(c) : Bool}:
  +e1 = Equal.trans(Bool, I.u64_is(NM.AddOver{q, b}), Bool.not(C.fits(64n, Nat.add(v(q), v(b)))), Bool.not(C.fits(64n, n)), LW.tests_add_over(q, b), Equal.cong(Nat, Bool, t => Bool.not(C.fits(64n, t)), Nat.add(v(q), v(b)), n, hn))
  Equal.trans(Bool, I.u64_is(NM.AddOver{q, b}), Bool.not(C.fits(64n, n)), Bool.not(c), e1, Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, n), c, hc))

def cadd_rel(+q: WU.U64, +x: WU.U64, +n: Nat, +hn: {Nat.add(v(q), v(x)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {G.cadd(~WU.U64, ~I.u64_op, ~I.u64_is, q, x) == G.fits(WU.U64, Bool.not(c), of(n)) : Maybe<&2, WU.U64>}:
  match c:
    case True{}:
      +hao = ao_of(q, x, n, hn, True{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.AddOver{q, x}), False{}, hao) : {G.fits(WU.U64, _, I.u64_op(NM.Add{q, x})) == Some{of(n)} : Maybe<&2, WU.U64>}
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, I.u64_op(NM.Add{q, x}), of(n), as_of(I.u64_op(NM.Add{q, x}), n, Equal.trans(Nat, v(I.u64_op(NM.Add{q, x})), Nat.add(v(q), v(x)), n, LW.ops_add(q, x, hao), hn)))
    case False{}:
      %Equal.sym(Bool, I.u64_is(NM.AddOver{q, x}), True{}, ao_of(q, x, n, hn, False{}, hc)) : {G.fits(WU.U64, _, I.u64_op(NM.Add{q, x})) == None{} : Maybe<&2, WU.U64>}
      {==}

# a value that does not fit stays unfit when it grows
def unfit_mono(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}, +hf: {C.fits(k, a) == False{} : Bool}) -> {C.fits(k, b) == False{} : Bool}:
  +na = Equal.trans(Bool, Nat.is_lt(a, C.pow2(k)), C.fits(k, a), False{}, Equal.sym(Bool, C.fits(k, a), Nat.is_lt(a, C.pow2(k)), WW.fits_lt(k, a)), hf)
  Equal.trans(Bool, C.fits(k, b), Nat.is_lt(b, C.pow2(k)), False{}, WW.fits_lt(k, b), N.le_not_lt(b, C.pow2(k), N.le_trans(C.pow2(k), a, b, N.not_lt_le(a, C.pow2(k), na), h)))

def sal(+xs: List<&2, WU.U64>, +r: Maybe<&2, WU.U64>, +n: Nat, +c: Bool, +hr: {r == G.fits(WU.U64, Bool.not(c), of(n)) : Maybe<&2, WU.U64>}, +hc: {C.fits(64n, n) == c : Bool}) -> {G.ok(WU.U64, G.sum_go(~WU.U64, ~I.u64_op, ~I.u64_is, xs, r)) == SG.checked(~WU.U64, ~SG.u64_of, 64n, Nat.add(n, NS.lsum(vals(xs)))) : Result<&2, &2, NM.NumError, WU.U64>}:
  match xs c:
    case Nil{} True{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, Some{of(n)}, hr) : {G.ok(WU.U64, _) == SG.checked(~WU.U64, ~SG.u64_of, 64n, Nat.add(n, 0n)) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Nat, Nat.add(n, 0n), n, N.add_zero(n)) : {Done{of(n)} == SG.checked(~WU.U64, ~SG.u64_of, 64n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Bool, C.fits(64n, n), True{}, hc) : {Done{of(n)} == SG.checked_pick(~WU.U64, ~SG.u64_of, n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Nil{} False{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, None{}, hr) : {G.ok(WU.U64, _) == SG.checked(~WU.U64, ~SG.u64_of, 64n, Nat.add(n, 0n)) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Nat, Nat.add(n, 0n), n, N.add_zero(n)) : {Fail{NM.Overflow{}} == SG.checked(~WU.U64, ~SG.u64_of, 64n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      %Equal.sym(Bool, C.fits(64n, n), False{}, hc) : {Fail{NM.Overflow{}} == SG.checked_pick(~WU.U64, ~SG.u64_of, n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Con{x, t} False{}:
      %Equal.sym(Maybe<&2, WU.U64>, r, None{}, hr) : {G.ok(WU.U64, G.sum_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _)) == SG.checked(~WU.U64, ~SG.u64_of, 64n, Nat.add(n, NS.lsum(vals(Con{x, t})))) : Result<&2, &2, NM.NumError, WU.U64>}
      +s = Nat.add(n, NS.lsum(vals(Con{x, t})))
      %Equal.sym(Bool, C.fits(64n, s), False{}, unfit_mono(64n, n, s, N.le_add_right(n, NS.lsum(vals(Con{x, t}))), hc)) : {Fail{NM.Overflow{}} == SG.checked_pick(~WU.U64, ~SG.u64_of, s, _) : Result<&2, &2, NM.NumError, WU.U64>}
      {==}
    case Con{+x, +t} True{}:
      +n2 = Nat.add(n, v(x))
      +hn = Equal.cong(Nat, Nat, z => Nat.add(z, v(x)), v(of(n)), n, LW.vo(n, hc))
      %Equal.sym(Maybe<&2, WU.U64>, r, Some{of(n)}, hr) : {G.ok(WU.U64, G.sum_go(~WU.U64, ~I.u64_op, ~I.u64_is, Con{x, t}, _)) == SG.checked(~WU.U64, ~SG.u64_of, 64n, Nat.add(n, Nat.add(v(x), NS.lsum(vals(t))))) : Result<&2, &2, NM.NumError, WU.U64>}
      %NA.add_assoc(n, v(x), NS.lsum(vals(t))) : {G.ok(WU.U64, G.sum_go(~WU.U64, ~I.u64_op, ~I.u64_is, t, G.cadd(~WU.U64, ~I.u64_op, ~I.u64_is, of(n), x))) == SG.checked(~WU.U64, ~SG.u64_of, 64n, _) : Result<&2, &2, NM.NumError, WU.U64>}
      sal(t, G.cadd(~WU.U64, ~I.u64_op, ~I.u64_is, of(n), x), n2, C.fits(64n, n2), cadd_rel(of(n), x, n2, hn, C.fits(64n, n2), {==}), {==})

def sum_checked(+xs: List<&2, WU.U64>) -> SG.Sum.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, xs):
  sal(xs, Some{I.u64_op(NM.ZeroOp{})}, 0n, True{}, Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, I.u64_op(NM.ZeroOp{}), of(0n), as_of(I.u64_op(NM.ZeroOp{}), 0n, zero_v())), {==})

# ---- bit_length: halvings on the values ----

def blsim(+f: Nat, +k: Nat, +n: WU.U64, +cz: Bool, +nn: Nat, +hcz: {I.u64_is(NM.IsZero{n}) == cz : Bool}, +hnn: {v(n) == nn : Nat}) -> {G.bit_length_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, k, (n, cz)) == M.bit_length_go(f, nn, k) : Nat}:
  match f cz nn:
    case 0n _ _:
      {==}
    case 1n+g True{} 0n:
      {==}
    case 1n+g True{} 1n+np:
      Empty.absurd({G.bit_length_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, (n, True{})) == M.bit_length_go(1n+g, 1n+np, k) : Nat}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{n}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{n}), True{}, hcz), iz(n, 1n+np, hnn))))
    case 1n+g False{} 0n:
      Empty.absurd({G.bit_length_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, (n, False{})) == M.bit_length_go(1n+g, 0n, k) : Nat}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{n}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{n}), True{}, iz(n, 0n, hnn)), hcz)))
    case 1n+ +g False{} 1n+ +np:
      +h = I.u64_op(NM.Half{n})
      +eh = Equal.trans(Nat, v(h), Nat.div(v(n), 2n), Nat.div(1n+np, 2n), LW.ops_half(n), Equal.cong(Nat, Nat, t => Nat.div(t, 2n), v(n), 1n+np, hnn))
      blsim(g, 1n+k, h, I.u64_is(NM.IsZero{h}), Nat.div(1n+np, 2n), {==}, eh)

def bit_length_k(+k: Nat, +hk: {k == 64n : Nat}, +n: WU.U64) -> {G.bit_length(~WU.U64, ~I.u64_op, ~I.u64_is, n) == M.bit_length(v(n)) : Nat}:
  +hj = L.subst(Nat, z => {Nat.is_le(z, 140n) == True{} : Bool}, 64n, k, Equal.sym(Nat, k, 64n, hk), {==})
  Equal.trans(Nat, G.bit_length(~WU.U64, ~I.u64_op, ~I.u64_is, n), M.bit_length_go(140n, v(n), 0n), M.bit_length(v(n)), blsim(140n, 0n, n, I.u64_is(NM.IsZero{n}), v(n), {==}, {==}), NF.bl_140(k, v(n), hj, LW.val_lt(k, hk, n)))

def bit_length_agrees(+n: WU.U64) -> SG.BitLength.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, n):
  bit_length_k(64n, {==}, n)

# ---- pow_mod: binary exponentiation on the values, below m ----

def pmo_lt(+mp: Nat, +d: Nat, +base: Nat, +acc: Nat, +ha: {Nat.is_lt(acc, 1n+mp) == True{} : Bool}) -> {Nat.is_lt(M.pow_mod_odd(1n+mp, d, base, acc), 1n+mp) == True{} : Bool}:
  match d:
    case 0n:
      ha
    case 1n+z:
      NR.dm_lt(mp, Nat.mul(acc, base))

def lt_m(+x: WU.U64, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +h: {Nat.is_lt(v(x), 1n+mp) == True{} : Bool}) -> {Nat.is_lt(v(x), v(m)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(v(x), z) == True{} : Bool}, 1n+mp, v(m), Equal.sym(Nat, v(m), 1n+mp, hm), h)

def mmb_v(+m: WU.U64, +b: WU.U64, +acc: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +hb: {Nat.is_lt(v(b), 1n+mp) == True{} : Bool}, +ha: {Nat.is_lt(v(acc), 1n+mp) == True{} : Bool}, +d: Nat, +o: Bool, +hd: {Nat.is_lt(d, 2n) == True{} : Bool}, +ho: {o == Nat.is_eq(d, 1n) : Bool}) -> {v(G.mm_bit(~WU.U64, ~I.u64_op, o, m, b, acc)) == M.pow_mod_odd(1n+mp, d, v(b), v(acc)) : Nat}:
  match d o:
    case 0n False{}:
      {==}
    case 0n True{}:
      Empty.absurd({v(G.mm_bit(~WU.U64, ~I.u64_op, True{}, m, b, acc)) == M.pow_mod_odd(1n+mp, 0n, v(b), v(acc)) : Nat}, true_ne_false(ho))
    case 1n True{}:
      Equal.trans(Nat, v(I.u64_op(NM.MulMod{acc, b, m})), Nat.mod(Nat.mul(v(acc), v(b)), v(m)), Nat.mod(Nat.mul(v(acc), v(b)), 1n+mp), LW.ops_mulmod(acc, b, m, lt_m(acc, m, mp, hm, ha), lt_m(b, m, mp, hm, hb)), Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(v(acc), v(b)), t), v(m), 1n+mp, hm))
    case 1n False{}:
      Empty.absurd({v(G.mm_bit(~WU.U64, ~I.u64_op, False{}, m, b, acc)) == M.pow_mod_odd(1n+mp, 1n, v(b), v(acc)) : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, ho)))
    case 2n+q _:
      Empty.absurd({v(G.mm_bit(~WU.U64, ~I.u64_op, o, m, b, acc)) == M.pow_mod_odd(1n+mp, 2n+q, v(b), v(acc)) : Nat}, N.lt_zero_absurd(q, hd))

def pmsim(+f: Nat, +m: WU.U64, +b: WU.U64, +acc: WU.U64, +e: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +hb: {Nat.is_lt(v(b), 1n+mp) == True{} : Bool}, +ha: {Nat.is_lt(v(acc), 1n+mp) == True{} : Bool}, +ez: Bool, +ne: Nat, +hez: {I.u64_is(NM.IsZero{e}) == ez : Bool}, +hne: {v(e) == ne : Nat}) -> {v(G.pow_mod_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, m, b, acc, (e, ez))) == M.pow_mod_go(f, 1n+mp, ne, v(b), v(acc)) : Nat}:
  match f ez ne:
    case 0n _ _:
      {==}
    case 1n+g True{} 0n:
      {==}
    case 1n+g True{} 1n+ep:
      Empty.absurd({v(G.pow_mod_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, m, b, acc, (e, True{}))) == M.pow_mod_go(1n+g, 1n+mp, 1n+ep, v(b), v(acc)) : Nat}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{e}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{e}), True{}, hez), iz(e, 1n+ep, hne))))
    case 1n+g False{} 0n:
      Empty.absurd({v(G.pow_mod_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, m, b, acc, (e, False{}))) == M.pow_mod_go(1n+g, 1n+mp, 0n, v(b), v(acc)) : Nat}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{e}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{e}), True{}, iz(e, 0n, hne)), hez)))
    case 1n+ +g False{} 1n+ +ep:
      +b2 = I.u64_op(NM.MulMod{b, b, m})
      +eb2 = Equal.trans(Nat, v(b2), Nat.mod(Nat.mul(v(b), v(b)), v(m)), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), LW.ops_mulmod(b, b, m, lt_m(b, m, mp, hm, hb), lt_m(b, m, mp, hm, hb)), Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(v(b), v(b)), t), v(m), 1n+mp, hm))
      +hb2 = L.subst(Nat, z => {Nat.is_lt(z, 1n+mp) == True{} : Bool}, Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), v(b2), Equal.sym(Nat, v(b2), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), eb2), NR.dm_lt(mp, Nat.mul(v(b), v(b))))
      +o = I.u64_is(NM.Odd{e})
      +d = Nat.mod(1n+ep, 2n)
      +ho = Equal.trans(Bool, o, Nat.is_eq(Nat.mod(v(e), 2n), 1n), Nat.is_eq(d, 1n), LW.tests_odd(e), Equal.cong(Nat, Bool, t => Nat.is_eq(Nat.mod(t, 2n), 1n), v(e), 1n+ep, hne))
      +acc2 = G.mm_bit(~WU.U64, ~I.u64_op, o, m, b, acc)
      +ea2 = mmb_v(m, b, acc, mp, hm, hb, ha, d, o, NR.dm_lt(1n, 1n+ep), ho)
      +ha2 = L.subst(Nat, z => {Nat.is_lt(z, 1n+mp) == True{} : Bool}, M.pow_mod_odd(1n+mp, d, v(b), v(acc)), v(acc2), Equal.sym(Nat, v(acc2), M.pow_mod_odd(1n+mp, d, v(b), v(acc)), ea2), pmo_lt(mp, d, v(b), v(acc), ha))
      +e2 = I.u64_op(NM.Half{e})
      +ee2 = Equal.trans(Nat, v(e2), Nat.div(v(e), 2n), Nat.div(1n+ep, 2n), LW.ops_half(e), Equal.cong(Nat, Nat, t => Nat.div(t, 2n), v(e), 1n+ep, hne))
      +ih = pmsim(g, m, b2, acc2, e2, mp, hm, hb2, ha2, I.u64_is(NM.IsZero{e2}), Nat.div(1n+ep, 2n), {==}, ee2)
      Equal.trans(Nat, v(G.pow_mod_go(~WU.U64, ~I.u64_op, ~I.u64_is, g, m, b2, acc2, (e2, I.u64_is(NM.IsZero{e2})))), M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), v(b2), v(acc2)), M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), M.pow_mod_odd(1n+mp, d, v(b), v(acc))), ih, Equal.trans(Nat, M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), v(b2), v(acc2)), M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), v(acc2)), M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), M.pow_mod_odd(1n+mp, d, v(b), v(acc))), Equal.cong(Nat, Nat, t => M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), t, v(acc2)), v(b2), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), eb2), Equal.cong(Nat, Nat, t => M.pow_mod_go(g, 1n+mp, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(v(b), v(b)), 1n+mp), t), v(acc2), M.pow_mod_odd(1n+mp, d, v(b), v(acc)), ea2)))

def pm_rem(+x: WU.U64, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}) -> {v(I.u64_op(NM.Rem{x, m})) == Nat.mod(v(x), 1n+mp) : Nat}:
  +hq = Equal.trans(Bool, Nat.is_eq(v(m), 0n), Nat.is_eq(1n+mp, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(m), 1n+mp, hm), {==})
  Equal.trans(Nat, v(I.u64_op(NM.Rem{x, m})), Nat.mod(v(x), v(m)), Nat.mod(v(x), 1n+mp), LW.ops_rem(x, m, hq), Equal.cong(Nat, Nat, t => Nat.mod(v(x), t), v(m), 1n+mp, hm))

def pm_top(+k: Nat, +hk: {k == 64n : Nat}, +b: WU.U64, +e: WU.U64, +m: WU.U64, +c: Bool, +hc: {I.u64_is(NM.IsZero{m}) == c : Bool}, +nm: Nat, +hnm: {v(m) == nm : Nat}) -> {G.pow_mod_ok(~WU.U64, ~I.u64_op, ~I.u64_is, b, e, m, c) == SG.lift(~WU.U64, ~SG.u64_of, M.pow_mod(v(b), v(e), nm)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c nm:
    case True{} 0n:
      {==}
    case False{} 0n:
      Empty.absurd({G.pow_mod_ok(~WU.U64, ~I.u64_op, ~I.u64_is, b, e, m, False{}) == SG.lift(~WU.U64, ~SG.u64_of, M.pow_mod(v(b), v(e), 0n)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{m}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{m}), True{}, iz(m, 0n, hnm)), hc)))
    case True{} 1n+ +mp:
      Empty.absurd({G.pow_mod_ok(~WU.U64, ~I.u64_op, ~I.u64_is, b, e, m, True{}) == SG.lift(~WU.U64, ~SG.u64_of, M.pow_mod(v(b), v(e), 1n+mp)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{m}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{m}), True{}, hc), iz(m, 1n+mp, hnm))))
    case False{} 1n+ +mp:
      +rb = I.u64_op(NM.Rem{b, m})
      +ra = I.u64_op(NM.Rem{I.u64_op(NM.One{}), m})
      +eb = pm_rem(b, m, mp, hnm)
      +ea = Equal.trans(Nat, v(ra), Nat.mod(v(I.u64_op(NM.One{})), 1n+mp), Nat.mod(1n, 1n+mp), pm_rem(I.u64_op(NM.One{}), m, mp, hnm), Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), v(I.u64_op(NM.One{})), 1n, one_v()))
      +hb = L.subst(Nat, z => {Nat.is_lt(z, 1n+mp) == True{} : Bool}, Nat.mod(v(b), 1n+mp), v(rb), Equal.sym(Nat, v(rb), Nat.mod(v(b), 1n+mp), eb), NR.dm_lt(mp, v(b)))
      +ha = L.subst(Nat, z => {Nat.is_lt(z, 1n+mp) == True{} : Bool}, Nat.mod(1n, 1n+mp), v(ra), Equal.sym(Nat, v(ra), Nat.mod(1n, 1n+mp), ea), NR.dm_lt(mp, 1n))
      +hj = L.subst(Nat, z => {Nat.is_le(z, 140n) == True{} : Bool}, 64n, k, Equal.sym(Nat, k, 64n, hk), {==})
      +s = pmsim(140n, m, rb, ra, e, mp, hnm, hb, ha, I.u64_is(NM.IsZero{e}), v(e), {==}, {==})
      +c1 = Equal.trans(Nat, M.pow_mod_go(140n, 1n+mp, v(e), v(rb), v(ra)), M.pow_mod_go(140n, 1n+mp, v(e), Nat.mod(v(b), 1n+mp), v(ra)), M.pow_mod_go(140n, 1n+mp, v(e), Nat.mod(v(b), 1n+mp), Nat.mod(1n, 1n+mp)), Equal.cong(Nat, Nat, t => M.pow_mod_go(140n, 1n+mp, v(e), t, v(ra)), v(rb), Nat.mod(v(b), 1n+mp), eb), Equal.cong(Nat, Nat, t => M.pow_mod_go(140n, 1n+mp, v(e), Nat.mod(v(b), 1n+mp), t), v(ra), Nat.mod(1n, 1n+mp), ea))
      +c2 = NF.pm_140(k, 1n+mp, v(e), Nat.mod(v(b), 1n+mp), Nat.mod(1n, 1n+mp), hj, LW.val_lt(k, hk, e))
      +g = G.pow_mod_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, m, rb, ra, (e, I.u64_is(NM.IsZero{e})))
      +r = M.pow_mod_go(v(e), 1n+mp, v(e), Nat.mod(v(b), 1n+mp), Nat.mod(1n, 1n+mp))
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, g, of(r), as_of(g, r, Equal.trans(Nat, v(g), M.pow_mod_go(140n, 1n+mp, v(e), v(rb), v(ra)), r, s, Equal.trans(Nat, M.pow_mod_go(140n, 1n+mp, v(e), v(rb), v(ra)), M.pow_mod_go(140n, 1n+mp, v(e), Nat.mod(v(b), 1n+mp), Nat.mod(1n, 1n+mp)), r, c1, c2))))

def powmod_agrees(+b: WU.U64, +e: WU.U64, +m: WU.U64) -> SG.PowMod.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, b, e, m):
  pm_top(64n, {==}, b, e, m, I.u64_is(NM.IsZero{m}), {==}, v(m), {==})

# ---- mod_inverse: extended Euclid on the values, coefficients below m ----

def nlt(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {Nat.is_lt(a, b) == Nat.is_lt(na, nb) : Bool}:
  Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_lt(na, b), Nat.is_lt(na, nb), Equal.cong(Nat, Bool, t => Nat.is_lt(t, b), a, na, ha), Equal.cong(Nat, Bool, t => Nat.is_lt(na, t), b, nb, hb))

def ltv(+a: WU.U64, +b: WU.U64, +na: Nat, +nb: Nat, +ha: {v(a) == na : Nat}, +hb: {v(b) == nb : Nat}) -> {I.u64_is(NM.Lt{a, b}) == Nat.is_lt(na, nb) : Bool}:
  Equal.trans(Bool, I.u64_is(NM.Lt{a, b}), Nat.is_lt(v(a), v(b)), Nat.is_lt(na, nb), LW.tests_lt(a, b), nlt(v(a), v(b), na, nb, ha, hb))

def nsub(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {Nat.sub(a, b) == Nat.sub(na, nb) : Nat}:
  Equal.trans(Nat, Nat.sub(a, b), Nat.sub(na, b), Nat.sub(na, nb), Equal.cong(Nat, Nat, t => Nat.sub(t, b), a, na, ha), Equal.cong(Nat, Nat, t => Nat.sub(na, t), b, nb, hb))

def nadd(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {Nat.add(a, b) == Nat.add(na, nb) : Nat}:
  Equal.trans(Nat, Nat.add(a, b), Nat.add(na, b), Nat.add(na, nb), Equal.cong(Nat, Nat, t => Nat.add(t, b), a, na, ha), Equal.cong(Nat, Nat, t => Nat.add(na, t), b, nb, hb))

def mv(+k: Nat, +hk: {k == 64n : Nat}, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}) -> {Nat.is_lt(1n+mp, C.pow2(k)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, C.pow2(k)) == True{} : Bool}, v(m), 1n+mp, hm, LW.val_lt(k, hk, m))

def fits32(+k: Nat, +hk: {k == 64n : Nat}, +n: Nat, +h: {Nat.is_lt(n, C.pow2(k)) == True{} : Bool}) -> {C.fits(64n, n) == True{} : Bool}:
  L.subst(Nat, z => {C.fits(z, n) == True{} : Bool}, k, 64n, hk, Equal.trans(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), True{}, WW.fits_lt(k, n), h))

def lt_mn(+x: WU.U64, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +nx: Nat, +hx: {v(x) == nx : Nat}, +h: {Nat.is_lt(nx, 1n+mp) == True{} : Bool}) -> {Nat.is_lt(v(x), v(m)) == True{} : Bool}:
  lt_m(x, m, mp, hm, L.subst(Nat, z => {Nat.is_lt(z, 1n+mp) == True{} : Bool}, nx, v(x), Equal.sym(Nat, v(x), nx, hx), h))

def subv(+k: Nat, +hk: {k == 64n : Nat}, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +s0: WU.U64, +x: WU.U64, +ns0: Nat, +nx: Nat, +hs0: {v(s0) == ns0 : Nat}, +hx: {v(x) == nx : Nat}, +hb0: {Nat.is_lt(ns0, 1n+mp) == True{} : Bool}, +hbx: {Nat.is_lt(nx, 1n+mp) == True{} : Bool}, +c: Bool, +hc: {I.u64_is(NM.Lt{s0, x}) == c : Bool}) -> {v(G.submod(~WU.U64, ~I.u64_op, m, s0, x, c)) == Nat.mod(Nat.add(ns0, Nat.sub(1n+mp, nx)), 1n+mp) : Nat}:
  match c:
    case True{}:
      +hl = Equal.trans(Bool, Nat.is_lt(ns0, nx), I.u64_is(NM.Lt{s0, x}), True{}, Equal.sym(Bool, I.u64_is(NM.Lt{s0, x}), Nat.is_lt(ns0, nx), ltv(s0, x, ns0, nx, hs0, hx)), hc)
      +y = I.u64_op(NM.Sub{m, x})
      +ey = Equal.trans(Nat, v(y), Nat.sub(v(m), v(x)), Nat.sub(1n+mp, nx), LW.ops_sub(m, x, N.lt_le(v(x), v(m), lt_mn(x, m, mp, hm, nx, hx, hbx))), nsub(v(m), v(x), 1n+mp, nx, hm, hx))
      +sum = Nat.add(ns0, Nat.sub(1n+mp, nx))
      +hsum = NF.sm_lt(1n+mp, ns0, nx, hl, N.lt_le(nx, 1n+mp, hbx))
      +esum = nadd(v(s0), v(y), ns0, Nat.sub(1n+mp, nx), hs0, ey)
      +hfit = fits32(k, hk, Nat.add(v(s0), v(y)), L.subst(Nat, z => {Nat.is_lt(z, C.pow2(k)) == True{} : Bool}, sum, Nat.add(v(s0), v(y)), Equal.sym(Nat, Nat.add(v(s0), v(y)), sum, esum), N.lt_trans(sum, 1n+mp, C.pow2(k), hsum, mv(k, hk, m, mp, hm))))
      +hao = Equal.trans(Bool, I.u64_is(NM.AddOver{s0, y}), Bool.not(C.fits(64n, Nat.add(v(s0), v(y)))), False{}, LW.tests_add_over(s0, y), Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, Nat.add(v(s0), v(y))), True{}, hfit))
      Equal.trans(Nat, v(I.u64_op(NM.Add{s0, y})), Nat.add(v(s0), v(y)), Nat.mod(sum, 1n+mp), LW.ops_add(s0, y, hao), Equal.trans(Nat, Nat.add(v(s0), v(y)), sum, Nat.mod(sum, 1n+mp), esum, Equal.sym(Nat, Nat.mod(sum, 1n+mp), sum, NF.mod_small(mp, sum, hsum))))
    case False{}:
      +hl = Equal.trans(Bool, Nat.is_lt(ns0, nx), I.u64_is(NM.Lt{s0, x}), False{}, Equal.sym(Bool, I.u64_is(NM.Lt{s0, x}), Nat.is_lt(ns0, nx), ltv(s0, x, ns0, nx, hs0, hx)), hc)
      +hlv = Equal.trans(Bool, Nat.is_lt(v(s0), v(x)), I.u64_is(NM.Lt{s0, x}), False{}, Equal.sym(Bool, I.u64_is(NM.Lt{s0, x}), Nat.is_lt(v(s0), v(x)), LW.tests_lt(s0, x)), hc)
      Equal.trans(Nat, v(I.u64_op(NM.Sub{s0, x})), Nat.sub(v(s0), v(x)), Nat.mod(Nat.add(ns0, Nat.sub(1n+mp, nx)), 1n+mp), LW.ops_sub(s0, x, N.not_lt_le(v(s0), v(x), hlv)), Equal.trans(Nat, Nat.sub(v(s0), v(x)), Nat.sub(ns0, nx), Nat.mod(Nat.add(ns0, Nat.sub(1n+mp, nx)), 1n+mp), nsub(v(s0), v(x), ns0, nx, hs0, hx), Equal.sym(Nat, Nat.mod(Nat.add(ns0, Nat.sub(1n+mp, nx)), 1n+mp), Nat.sub(ns0, nx), NF.sm_ge(mp, ns0, nx, N.not_lt_le(ns0, nx, hl), hb0))))

def stepv(+k: Nat, +hk: {k == 64n : Nat}, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +q: WU.U64, +s0: WU.U64, +s1: WU.U64, +nq: Nat, +ns0: Nat, +ns1: Nat, +hq: {v(q) == nq : Nat}, +hs0: {v(s0) == ns0 : Nat}, +hs1: {v(s1) == ns1 : Nat}, +hb0: {Nat.is_lt(ns0, 1n+mp) == True{} : Bool}, +hb1: {Nat.is_lt(ns1, 1n+mp) == True{} : Bool}) -> {v(G.inv_step(~WU.U64, ~I.u64_op, ~I.u64_is, m, q, s0, s1)) == M.inv_step(1n+mp, nq, ns0, ns1) : Nat}:
  +rq = I.u64_op(NM.Rem{q, m})
  +erq = Equal.trans(Nat, v(rq), Nat.mod(v(q), 1n+mp), Nat.mod(nq, 1n+mp), pm_rem(q, m, mp, hm), Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), v(q), nq, hq))
  +x = I.u64_op(NM.MulMod{rq, s1, m})
  e1 = LW.ops_mulmod(rq, s1, m, lt_mn(rq, m, mp, hm, Nat.mod(nq, 1n+mp), erq, NR.dm_lt(mp, nq)), lt_mn(s1, m, mp, hm, ns1, hs1, hb1))
  +e2 = Equal.trans(Nat, Nat.mod(Nat.mul(v(rq), v(s1)), v(m)), Nat.mod(Nat.mul(v(rq), v(s1)), 1n+mp), Nat.mod(Nat.mul(Nat.mod(nq, 1n+mp), ns1), 1n+mp), Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(v(rq), v(s1)), t), v(m), 1n+mp, hm), Equal.trans(Nat, Nat.mod(Nat.mul(v(rq), v(s1)), 1n+mp), Nat.mod(Nat.mul(Nat.mod(nq, 1n+mp), v(s1)), 1n+mp), Nat.mod(Nat.mul(Nat.mod(nq, 1n+mp), ns1), 1n+mp), Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(t, v(s1)), 1n+mp), v(rq), Nat.mod(nq, 1n+mp), erq), Equal.cong(Nat, Nat, t => Nat.mod(Nat.mul(Nat.mod(nq, 1n+mp), t), 1n+mp), v(s1), ns1, hs1)))
  +ex = Equal.trans(Nat, v(x), Nat.mod(Nat.mul(v(rq), v(s1)), v(m)), Nat.mod(Nat.mul(nq, ns1), 1n+mp), e1, Equal.trans(Nat, Nat.mod(Nat.mul(v(rq), v(s1)), v(m)), Nat.mod(Nat.mul(Nat.mod(nq, 1n+mp), ns1), 1n+mp), Nat.mod(Nat.mul(nq, ns1), 1n+mp), e2, NR.mod_mul_l(mp, nq, ns1)))
  subv(k, hk, m, mp, hm, s0, x, ns0, Nat.mod(Nat.mul(nq, ns1), 1n+mp), hs0, ex, hb0, NR.dm_lt(mp, Nat.mul(nq, ns1)), I.u64_is(NM.Lt{s0, x}), {==})

def pv(p: WU.U64 & WU.U64) -> M.Bezout:
  (+g, +s) = p
  M.BZ{v(g), v(s)}

def bzeq(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {M.BZ{a, b} == M.BZ{na, nb} : M.Bezout}:
  Equal.trans(M.Bezout, M.BZ{a, b}, M.BZ{na, b}, M.BZ{na, nb}, Equal.cong(Nat, M.Bezout, t => M.BZ{t, b}, a, na, ha), Equal.cong(Nat, M.Bezout, t => M.BZ{na, t}, b, nb, hb))

def or_true(+x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def invsim(+f: Nat, +k: Nat, +hk: {k == 64n : Nat}, +m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +r0: WU.U64, +s0: WU.U64, +s1: WU.U64, +r1: WU.U64, +nr0: Nat, +ns0: Nat, +ns1: Nat, +hr0: {v(r0) == nr0 : Nat}, +hs0: {v(s0) == ns0 : Nat}, +hs1: {v(s1) == ns1 : Nat}, +hb0: {Nat.is_lt(ns0, 1n+mp) == True{} : Bool}, +cz: Bool, +nr1: Nat, +hcz: {I.u64_is(NM.IsZero{r1}) == cz : Bool}, +hr1: {v(r1) == nr1 : Nat}, +hb1: {Bool.or(Nat.is_eq(nr1, 0n), Nat.is_lt(ns1, 1n+mp)) == True{} : Bool}) -> {pv(G.inv_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, m, r0, s0, s1, (r1, cz))) == M.inv_go(f, 1n+mp, nr0, ns0, nr1, ns1) : M.Bezout}:
  match f cz nr1:
    case 0n _ _:
      bzeq(v(r0), v(s0), nr0, ns0, hr0, hs0)
    case 1n+g True{} 0n:
      bzeq(v(r0), v(s0), nr0, ns0, hr0, hs0)
    case 1n+g True{} 1n+rp:
      Empty.absurd({pv(G.inv_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, m, r0, s0, s1, (r1, True{}))) == M.inv_go(1n+g, 1n+mp, nr0, ns0, 1n+rp, ns1) : M.Bezout}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{r1}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{r1}), True{}, hcz), iz(r1, 1n+rp, hr1))))
    case 1n+g False{} 0n:
      Empty.absurd({pv(G.inv_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, m, r0, s0, s1, (r1, False{}))) == M.inv_go(1n+g, 1n+mp, nr0, ns0, 0n, ns1) : M.Bezout}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{r1}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{r1}), True{}, iz(r1, 0n, hr1)), hcz)))
    case 1n+ +g False{} 1n+ +rp:
      +hnz = Equal.trans(Bool, Nat.is_eq(v(r1), 0n), Nat.is_eq(1n+rp, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(r1), 1n+rp, hr1), {==})
      +q = I.u64_op(NM.Quot{r0, r1})
      +eq = Equal.trans(Nat, v(q), Nat.div(v(r0), v(r1)), Nat.div(nr0, 1n+rp), LW.ops_quot(r0, r1, hnz), Equal.trans(Nat, Nat.div(v(r0), v(r1)), Nat.div(nr0, v(r1)), Nat.div(nr0, 1n+rp), Equal.cong(Nat, Nat, t => Nat.div(t, v(r1)), v(r0), nr0, hr0), Equal.cong(Nat, Nat, t => Nat.div(nr0, t), v(r1), 1n+rp, hr1)))
      +r2 = I.u64_op(NM.Rem{r0, r1})
      +er2 = Equal.trans(Nat, v(r2), Nat.mod(v(r0), v(r1)), Nat.mod(nr0, 1n+rp), LW.ops_rem(r0, r1, hnz), Equal.trans(Nat, Nat.mod(v(r0), v(r1)), Nat.mod(nr0, v(r1)), Nat.mod(nr0, 1n+rp), Equal.cong(Nat, Nat, t => Nat.mod(t, v(r1)), v(r0), nr0, hr0), Equal.cong(Nat, Nat, t => Nat.mod(nr0, t), v(r1), 1n+rp, hr1)))
      +ns2 = M.inv_step(1n+mp, Nat.div(nr0, 1n+rp), ns0, ns1)
      +es2 = stepv(k, hk, m, mp, hm, q, s0, s1, Nat.div(nr0, 1n+rp), ns0, ns1, eq, hs0, hs1, hb0, hb1)
      +hb2 = L.subst(Bool, t => {Bool.or(Nat.is_eq(Nat.mod(nr0, 1n+rp), 0n), t) == True{} : Bool}, True{}, Nat.is_lt(ns2, 1n+mp), Equal.sym(Bool, Nat.is_lt(ns2, 1n+mp), True{}, NR.dm_lt(mp, Nat.add(ns0, Nat.sub(1n+mp, Nat.mod(Nat.mul(Nat.div(nr0, 1n+rp), ns1), 1n+mp))))), or_true(Nat.is_eq(Nat.mod(nr0, 1n+rp), 0n)))
      invsim(g, k, hk, m, mp, hm, r1, s1, G.inv_step(~WU.U64, ~I.u64_op, ~I.u64_is, m, q, s0, s1), r2, 1n+rp, ns1, ns2, hr1, hs1, es2, hb1, I.u64_is(NM.IsZero{r2}), Nat.mod(nr0, 1n+rp), {==}, er2, hb2)

def fin2(+m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, +s: WU.U64, +sn: Nat, +hs: {v(s) == sn : Nat}, +cb: Bool, +gn: Nat, +hcb: {Bool.and(Bool.not(Nat.is_lt(gn, 1n)), Bool.not(Nat.is_lt(1n, gn))) == cb : Bool}) -> {G.inv_one(~WU.U64, ~I.u64_op, m, s, cb) == SG.lift(~WU.U64, ~SG.u64_of, M.inv_fin(1n+mp, M.BZ{gn, sn})) : Result<&2, &2, NM.NumError, WU.U64>}:
  match cb gn:
    case True{} 1n:
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.Rem{s, m}), of(Nat.mod(sn, 1n+mp)), as_of(I.u64_op(NM.Rem{s, m}), Nat.mod(sn, 1n+mp), Equal.trans(Nat, v(I.u64_op(NM.Rem{s, m})), Nat.mod(v(s), 1n+mp), Nat.mod(sn, 1n+mp), pm_rem(s, m, mp, hm), Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+mp), v(s), sn, hs))))
    case False{} 1n:
      Empty.absurd({G.inv_one(~WU.U64, ~I.u64_op, m, s, False{}) == SG.lift(~WU.U64, ~SG.u64_of, M.inv_fin(1n+mp, M.BZ{1n, sn})) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(hcb))
    case True{} 0n:
      Empty.absurd({G.inv_one(~WU.U64, ~I.u64_op, m, s, True{}) == SG.lift(~WU.U64, ~SG.u64_of, M.inv_fin(1n+mp, M.BZ{0n, sn})) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.sym(Bool, False{}, True{}, hcb)))
    case False{} 0n:
      {==}
    case True{} 2n+h:
      Empty.absurd({G.inv_one(~WU.U64, ~I.u64_op, m, s, True{}) == SG.lift(~WU.U64, ~SG.u64_of, M.inv_fin(1n+mp, M.BZ{2n+h, sn})) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.sym(Bool, False{}, True{}, hcb)))
    case False{} 2n+h:
      {==}

def finsim(+m: WU.U64, +mp: Nat, +hm: {v(m) == 1n+mp : Nat}, p: WU.U64 & WU.U64, +bz: M.Bezout, +h: {pv(p) == bz : M.Bezout}) -> {G.inv_fin(~WU.U64, ~I.u64_op, ~I.u64_is, m, p) == SG.lift(~WU.U64, ~SG.u64_of, M.inv_fin(1n+mp, bz)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match p bz:
    case Tuple{+g, +s} M.BZ{+gn, +sn}:
      +hg = Equal.cong(M.Bezout, Nat, z => IV.bg(z), M.BZ{v(g), v(s)}, M.BZ{gn, sn}, h)
      +hs = Equal.cong(M.Bezout, Nat, z => IV.bc(z), M.BZ{v(g), v(s)}, M.BZ{gn, sn}, h)
      +one = I.u64_op(NM.One{})
      +e = Equal.trans(Bool, Bool.and(Bool.not(I.u64_is(NM.Lt{g, one})), Bool.not(I.u64_is(NM.Lt{one, g}))), Bool.and(Bool.not(Nat.is_lt(gn, 1n)), Bool.not(I.u64_is(NM.Lt{one, g}))), Bool.and(Bool.not(Nat.is_lt(gn, 1n)), Bool.not(Nat.is_lt(1n, gn))), Equal.cong(Bool, Bool, t => Bool.and(Bool.not(t), Bool.not(I.u64_is(NM.Lt{one, g}))), I.u64_is(NM.Lt{g, one}), Nat.is_lt(gn, 1n), ltv(g, one, gn, 1n, hg, one_v())), Equal.cong(Bool, Bool, t => Bool.and(Bool.not(Nat.is_lt(gn, 1n)), Bool.not(t)), I.u64_is(NM.Lt{one, g}), Nat.is_lt(1n, gn), ltv(one, g, 1n, gn, one_v(), hg)))
      fin2(m, mp, hm, s, sn, hs, Bool.and(Bool.not(I.u64_is(NM.Lt{g, one})), Bool.not(I.u64_is(NM.Lt{one, g}))), gn, Equal.sym(Bool, Bool.and(Bool.not(I.u64_is(NM.Lt{g, one})), Bool.not(I.u64_is(NM.Lt{one, g}))), Bool.and(Bool.not(Nat.is_lt(gn, 1n)), Bool.not(Nat.is_lt(1n, gn))), e))

def lt1_eq(+x: Nat, +h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {Nat.is_eq(x, 0n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      Empty.absurd({Nat.is_eq(1n+y, 0n) == True{} : Bool}, N.lt_zero_absurd(y, h))

def hb_init(+mp: Nat, +a: Nat) -> {Bool.or(Nat.is_eq(Nat.mod(a, 1n+mp), 0n), Nat.is_lt(1n, 1n+mp)) == True{} : Bool}:
  match mp:
    case 0n:
      L.subst(Bool, t => {Bool.or(t, Nat.is_lt(1n, 1n)) == True{} : Bool}, True{}, Nat.is_eq(Nat.mod(a, 1n), 0n), Equal.sym(Bool, Nat.is_eq(Nat.mod(a, 1n), 0n), True{}, lt1_eq(Nat.mod(a, 1n), NR.dm_lt(0n, a))), {==})
    case 1n+q:
      or_true(Nat.is_eq(Nat.mod(a, 2n+q), 0n))

def inv_top(+k: Nat, +hk: {k == 64n : Nat}, +a: WU.U64, +m: WU.U64, +c: Bool, +hc: {I.u64_is(NM.IsZero{m}) == c : Bool}, +nm: Nat, +hnm: {v(m) == nm : Nat}) -> {G.inv_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, m, c) == SG.lift(~WU.U64, ~SG.u64_of, M.mod_inverse(v(a), nm)) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c nm:
    case True{} 0n:
      {==}
    case False{} 0n:
      Empty.absurd({G.inv_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, m, False{}) == SG.lift(~WU.U64, ~SG.u64_of, M.mod_inverse(v(a), 0n)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{m}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{m}), True{}, iz(m, 0n, hnm)), hc)))
    case True{} 1n+ +mp:
      Empty.absurd({G.inv_ok(~WU.U64, ~I.u64_op, ~I.u64_is, a, m, True{}) == SG.lift(~WU.U64, ~SG.u64_of, M.mod_inverse(v(a), 1n+mp)) : Result<&2, &2, NM.NumError, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, I.u64_is(NM.IsZero{m}), False{}, Equal.sym(Bool, I.u64_is(NM.IsZero{m}), True{}, hc), iz(m, 1n+mp, hnm))))
    case False{} 1n+ +mp:
      +r1 = I.u64_op(NM.Rem{a, m})
      +ra = Nat.mod(v(a), 1n+mp)
      +hk2 = L.subst(Nat, z => {Nat.is_le(1n+Nat.double(z), 140n) == True{} : Bool}, 64n, k, Equal.sym(Nat, k, 64n, hk), {==})
      +s = invsim(140n, k, hk, m, mp, hnm, m, I.u64_op(NM.ZeroOp{}), I.u64_op(NM.One{}), r1, 1n+mp, 0n, 1n, hnm, zero_v(), one_v(), {==}, I.u64_is(NM.IsZero{r1}), ra, {==}, pm_rem(a, m, mp, hnm), hb_init(mp, v(a)))
      +bz = M.inv_go(1n+mp, 1n+mp, 1n+mp, 0n, ra, 1n)
      g = G.inv_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, m, m, I.u64_op(NM.ZeroOp{}), I.u64_op(NM.One{}), (r1, I.u64_is(NM.IsZero{r1})))
      finsim(m, mp, hnm, g, bz, Equal.trans(M.Bezout, pv(g), M.inv_go(140n, 1n+mp, 1n+mp, 0n, ra, 1n), bz, s, NF.inv_140(k, mp, v(a), hk2, mv(k, hk, m, mp, hnm))))

def modinv_agrees(+a: WU.U64, +m: WU.U64) -> SG.ModInverse.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, a, m):
  inv_top(64n, {==}, a, m, I.u64_is(NM.IsZero{m}), {==}, v(m), {==})

# ---- ilog: the multiply-up loop on the values ----

def nle(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {Bool.not(c) == Nat.is_le(b, a) : Bool}:
  match c:
    case True{}:
      Equal.sym(Bool, Nat.is_le(b, a), False{}, N.lt_not_le(a, b, hc))
    case False{}:
      Equal.sym(Bool, Nat.is_le(b, a), True{}, N.not_lt_le(a, b, hc))

def nmul(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {Nat.mul(a, b) == Nat.mul(na, nb) : Nat}:
  Equal.trans(Nat, Nat.mul(a, b), Nat.mul(na, b), Nat.mul(na, nb), Equal.cong(Nat, Nat, t => Nat.mul(t, b), a, na, ha), Equal.cong(Nat, Nat, t => Nat.mul(na, t), b, nb, hb))

# le(x, y) on WU.U64 is is_le on the values
def lev(+x: WU.U64, +y: WU.U64, +nx: Nat, +ny: Nat, +hx: {v(x) == nx : Nat}, +hy: {v(y) == ny : Nat}) -> {G.le(~WU.U64, ~I.u64_is, x, y) == Nat.is_le(nx, ny) : Bool}:
  Equal.trans(Bool, Bool.not(I.u64_is(NM.Lt{y, x})), Bool.not(Nat.is_lt(ny, nx)), Nat.is_le(nx, ny), Equal.cong(Bool, Bool, t => Bool.not(t), I.u64_is(NM.Lt{y, x}), Nat.is_lt(ny, nx), ltv(y, x, ny, nx, hy, hx)), nle(ny, nx, Nat.is_lt(ny, nx), {==}))

def ilsim(+f: Nat, +q: WU.U64, +b: WU.U64, +k: Nat, +p: WU.U64, +nn: Nat, +bq: Nat, +np: Nat, +hq: {v(q) == Nat.div(nn, 2n+bq) : Nat}, +hb: {v(b) == 2n+bq : Nat}, +hp: {v(p) == np : Nat}, +K: Nat, +hK: {K == 64n : Nat}, +hn: {Nat.is_lt(nn, C.pow2(K)) == True{} : Bool}, +up: Bool, +hup: {up == Nat.is_le(np, Nat.div(nn, 2n+bq)) : Bool}) -> {G.ilog_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, q, b, k, p, up) == M.ilog_go(f, nn, 2n+bq, k, np, up) : Nat}:
  match f up:
    case 0n _:
      {==}
    case 1n+g False{}:
      {==}
    case 1n+ +g True{}:
      +hle = Equal.sym(Bool, True{}, Nat.is_le(np, Nat.div(nn, 2n+bq)), hup)
      +hmn = Equal.trans(Bool, Nat.is_le(Nat.mul(np, 2n+bq), nn), Nat.is_le(np, Nat.div(nn, 2n+bq)), True{}, Equal.sym(Bool, Nat.is_le(np, Nat.div(nn, 2n+bq)), Nat.is_le(Nat.mul(np, 2n+bq), nn), NR.le_div(1n+bq, np, nn)), hle)
      +emul = nmul(v(p), v(b), np, 2n+bq, hp, hb)
      +hfit = fits32(K, hK, Nat.mul(v(p), v(b)), L.subst(Nat, z => {Nat.is_lt(z, C.pow2(K)) == True{} : Bool}, Nat.mul(np, 2n+bq), Nat.mul(v(p), v(b)), Equal.sym(Nat, Nat.mul(v(p), v(b)), Nat.mul(np, 2n+bq), emul), N.le_lt_trans(Nat.mul(np, 2n+bq), nn, C.pow2(K), hmn, hn)))
      +hmo = Equal.trans(Bool, I.u64_is(NM.MulOver{p, b}), Bool.not(C.fits(64n, Nat.mul(v(p), v(b)))), False{}, LW.tests_mul_over(p, b), Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, Nat.mul(v(p), v(b))), True{}, hfit))
      +pb = I.u64_op(NM.Mul{p, b})
      +epb = Equal.trans(Nat, v(pb), Nat.mul(v(p), v(b)), Nat.mul(np, 2n+bq), LW.ops_mul(p, b, hmo), emul)
      +u2 = G.le(~WU.U64, ~I.u64_is, pb, q)
      +hu2 = lev(pb, q, Nat.mul(np, 2n+bq), Nat.div(nn, 2n+bq), epb, hq)
      Equal.trans(Nat, G.ilog_go(~WU.U64, ~I.u64_op, ~I.u64_is, g, q, b, 1n+k, pb, u2), M.ilog_go(g, nn, 2n+bq, 1n+k, Nat.mul(np, 2n+bq), u2), M.ilog_go(g, nn, 2n+bq, 1n+k, Nat.mul(np, 2n+bq), Nat.is_le(Nat.mul(np, 2n+bq), Nat.div(nn, 2n+bq))), ilsim(g, q, b, 1n+k, pb, nn, bq, Nat.mul(np, 2n+bq), hq, hb, epb, K, hK, hn, u2, hu2), Equal.cong(Bool, Nat, t => M.ilog_go(g, nn, 2n+bq, 1n+k, Nat.mul(np, 2n+bq), t), u2, Nat.is_le(Nat.mul(np, 2n+bq), Nat.div(nn, 2n+bq)), hu2))

def or_false_r(+x: Bool, +y: Bool, +h: {Bool.or(x, y) == False{} : Bool}) -> {y == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({y == False{} : Bool}, true_ne_false(h))
    case False{}:
      h

def ilog_fin(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +b: WU.U64, +nb: Nat, +hb: {v(b) == nb : Nat}, +hl: {Nat.is_lt(nb, 2n) == False{} : Bool}) -> {G.ilog_ok(~WU.U64, ~I.u64_op, ~I.u64_is, n, b, False{}) == SG.lift_nat(M.ilog_ok(v(n), nb, False{})) : Result<&2, &2, NM.NumError, Nat>}:
  match nb:
    case 0n:
      Empty.absurd({G.ilog_ok(~WU.U64, ~I.u64_op, ~I.u64_is, n, b, False{}) == SG.lift_nat(M.ilog_ok(v(n), 0n, False{})) : Result<&2, &2, NM.NumError, Nat>}, true_ne_false(hl))
    case 1n:
      Empty.absurd({G.ilog_ok(~WU.U64, ~I.u64_op, ~I.u64_is, n, b, False{}) == SG.lift_nat(M.ilog_ok(v(n), 1n, False{})) : Result<&2, &2, NM.NumError, Nat>}, true_ne_false(hl))
    case 2n+ +bq:
      +hnz = Equal.trans(Bool, Nat.is_eq(v(b), 0n), Nat.is_eq(2n+bq, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(b), 2n+bq, hb), {==})
      +q = I.u64_op(NM.Quot{n, b})
      +dq = Nat.div(v(n), 2n+bq)
      +eq = Equal.trans(Nat, v(q), Nat.div(v(n), v(b)), dq, LW.ops_quot(n, b, hnz), Equal.cong(Nat, Nat, t => Nat.div(v(n), t), v(b), 2n+bq, hb))
      +one = I.u64_op(NM.One{})
      +up = G.le(~WU.U64, ~I.u64_is, one, q)
      +hup = lev(one, q, 1n, dq, one_v(), eq)
      +hn = LW.val_lt(K, hK, n)
      +hK2 = L.subst(Nat, z => {Nat.is_le(z, 140n) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), {==})
      +s = ilsim(140n, q, b, 0n, one, v(n), bq, 1n, eq, hb, one_v(), K, hK, hn, up, hup)
      +c1 = Equal.cong(Bool, Nat, t => M.ilog_go(140n, v(n), 2n+bq, 0n, 1n, t), up, Nat.is_le(1n, dq), hup)
      +c2 = NF.il_140(K, v(n), bq, hK2, N.le_lt_trans(dq, v(n), C.pow2(K), AR2.div_le(v(n), 2n+bq), hn))
      +r = M.ilog_go(v(n), v(n), 2n+bq, 0n, 1n, Nat.is_le(1n, dq))
      Equal.cong(Nat, Result<&2, &2, NM.NumError, Nat>, t => Done{t}, G.ilog_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, q, b, 0n, one, up), r, Equal.trans(Nat, G.ilog_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, q, b, 0n, one, up), M.ilog_go(140n, v(n), 2n+bq, 0n, 1n, up), r, s, Equal.trans(Nat, M.ilog_go(140n, v(n), 2n+bq, 0n, 1n, up), M.ilog_go(140n, v(n), 2n+bq, 0n, 1n, Nat.is_le(1n, dq)), r, c1, c2)))

def ilog_top(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +b: WU.U64, +bad: Bool, +hN: {Bool.or(Nat.is_eq(v(n), 0n), Nat.is_lt(v(b), 2n)) == bad : Bool}) -> {G.ilog_ok(~WU.U64, ~I.u64_op, ~I.u64_is, n, b, bad) == SG.lift_nat(M.ilog_ok(v(n), v(b), bad)) : Result<&2, &2, NM.NumError, Nat>}:
  match bad:
    case True{}:
      {==}
    case False{}:
      ilog_fin(K, hK, n, b, v(b), {==}, or_false_r(Nat.is_eq(v(n), 0n), Nat.is_lt(v(b), 2n), hN))

def two_v() -> {v(I.u64_op(NM.Add{I.u64_op(NM.One{}), I.u64_op(NM.One{})})) == 2n : Nat}:
  +one = I.u64_op(NM.One{})
  +e11 = nadd(v(one), v(one), 1n, 1n, one_v(), one_v())
  +hao = Equal.trans(Bool, I.u64_is(NM.AddOver{one, one}), Bool.not(C.fits(64n, Nat.add(v(one), v(one)))), False{}, LW.tests_add_over(one, one), Equal.cong(Nat, Bool, t => Bool.not(C.fits(64n, t)), Nat.add(v(one), v(one)), 2n, e11))
  Equal.trans(Nat, v(I.u64_op(NM.Add{one, one})), Nat.add(v(one), v(one)), 2n, LW.ops_add(one, one, hao), e11)

def ilog_agrees(+n: WU.U64, +b: WU.U64) -> SG.Ilog.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, n, b):
  +two = I.u64_op(NM.Add{I.u64_op(NM.One{}), I.u64_op(NM.One{})})
  +bu = Bool.or(I.u64_is(NM.IsZero{n}), I.u64_is(NM.Lt{b, two}))
  +bn = Bool.or(Nat.is_eq(v(n), 0n), Nat.is_lt(v(b), 2n))
  +eb = Equal.trans(Bool, bu, Bool.or(Nat.is_eq(v(n), 0n), I.u64_is(NM.Lt{b, two})), bn, Equal.cong(Bool, Bool, t => Bool.or(t, I.u64_is(NM.Lt{b, two})), I.u64_is(NM.IsZero{n}), Nat.is_eq(v(n), 0n), LW.tests_is_zero(n)), Equal.cong(Bool, Bool, t => Bool.or(Nat.is_eq(v(n), 0n), t), I.u64_is(NM.Lt{b, two}), Nat.is_lt(v(b), 2n), ltv(b, two, v(b), 2n, {==}, two_v())))
  Equal.trans(Result<&2, &2, NM.NumError, Nat>, G.ilog_ok(~WU.U64, ~I.u64_op, ~I.u64_is, n, b, bu), SG.lift_nat(M.ilog_ok(v(n), v(b), bu)), SG.lift_nat(M.ilog_ok(v(n), v(b), bn)), ilog_top(64n, {==}, n, b, bu, Equal.sym(Bool, bu, bn, eb)), Equal.cong(Bool, Result<&2, &2, NM.NumError, Nat>, t => SG.lift_nat(M.ilog_ok(v(n), v(b), t)), bu, bn, eb))

# ---- factorial: 2 * 3 * ... bottom-up, stopping at the first overflow ----

# the value when the flag says it fits
def FR(ok: Bool, a: WU.U64, x: Nat) -> Type:
  match ok:
    case True{}:
      {v(a) == x : Nat}
    case False{}:
      {x == x : Nat}

def not_not(+c: Bool) -> {Bool.not(Bool.not(c)) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def fr_mul(+a: WU.U64, +x: WU.U64, +n: Nat, +hn: {Nat.mul(v(a), v(x)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> FR(Bool.not(I.u64_is(NM.MulOver{a, x})), I.u64_op(NM.Mul{a, x}), n):
  match c:
    case True{}:
      +hmo = mo_of(a, x, n, hn, True{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.MulOver{a, x}), False{}, hmo) : FR(Bool.not(_), I.u64_op(NM.Mul{a, x}), n)
      Equal.trans(Nat, v(I.u64_op(NM.Mul{a, x})), Nat.mul(v(a), v(x)), n, LW.ops_mul(a, x, hmo), hn)
    case False{}:
      %Equal.sym(Bool, I.u64_is(NM.MulOver{a, x}), True{}, mo_of(a, x, n, hn, False{}, hc)) : FR(Bool.not(_), I.u64_op(NM.Mul{a, x}), n)
      {==}

# the flag after a checked multiply is fits(product)
def ok_mul(+a: WU.U64, +x: WU.U64, +n: Nat, +hn: {Nat.mul(v(a), v(x)) == n : Nat}) -> {C.fits(64n, n) == Bool.not(I.u64_is(NM.MulOver{a, x})) : Bool}:
  Equal.sym(Bool, Bool.not(I.u64_is(NM.MulOver{a, x})), C.fits(64n, n), Equal.trans(Bool, Bool.not(I.u64_is(NM.MulOver{a, x})), Bool.not(Bool.not(C.fits(64n, n))), C.fits(64n, n), Equal.cong(Bool, Bool, t => Bool.not(t), I.u64_is(NM.MulOver{a, x}), Bool.not(C.fits(64n, n)), mo_of(a, x, n, hn, C.fits(64n, n), {==})), not_not(C.fits(64n, n))))

def fk(+K: Nat, +hK: {K == 64n : Nat}, +x: Nat, +h: {C.fits(64n, x) == True{} : Bool}) -> {Nat.is_lt(x, C.pow2(K)) == True{} : Bool}:
  +h2 = L.subst(Nat, z => {C.fits(z, x) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), h)
  Equal.trans(Bool, Nat.is_lt(x, C.pow2(K)), C.fits(K, x), True{}, Equal.sym(Bool, C.fits(K, x), Nat.is_lt(x, C.pow2(K)), WW.fits_lt(K, x)), h2)

def succ_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, N.lt_zero_absurd(a, h))
    case 0n 1n+y:
      N.zero_le(y)
    case 1n+ +x 1n+ +y:
      succ_le(x, y, h)

def plus1(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, NA.add_succ(x, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(x, 0n), x, N.add_zero(x)))

# inc(i) for i < n is i + 1
def inc_v(+K: Nat, +hK: {K == 64n : Nat}, +i: WU.U64, +n: WU.U64, +ni: Nat, +nn: Nat, +hi: {v(i) == ni : Nat}, +hn: {v(n) == nn : Nat}, +hlt: {Nat.is_lt(ni, nn) == True{} : Bool}) -> {v(G.inc(~WU.U64, ~I.u64_op, i)) == 1n+ni : Nat}:
  +one = I.u64_op(NM.One{})
  +hnK = L.subst(Nat, z => {Nat.is_lt(z, C.pow2(K)) == True{} : Bool}, v(n), nn, hn, LW.val_lt(K, hK, n))
  +hfit = fits32(K, hK, 1n+ni, N.le_lt_trans(1n+ni, nn, C.pow2(K), succ_le(ni, nn, hlt), hnK))
  +hn1 = Equal.trans(Nat, Nat.add(v(i), v(one)), Nat.add(ni, 1n), 1n+ni, nadd(v(i), v(one), ni, 1n, hi, one_v()), plus1(ni))
  Equal.trans(Nat, v(I.u64_op(NM.Add{i, one})), Nat.add(v(i), v(one)), 1n+ni, LW.ops_add(i, one, ao_of(i, one, 1n+ni, hn1, True{}, hfit)), hn1)

def factsim(+f: Nat, +i: WU.U64, +n: WU.U64, +a: WU.U64, +ni: Nat, +nn: Nat, +K: Nat, +ok: Bool, +more: Bool, +cn: Bool, +hK: {K == 64n : Nat}, +hi: {v(i) == ni : Nat}, +hn: {v(n) == nn : Nat}, +hmono: {Nat.is_le(S.factorial(ni), S.factorial(nn)) == True{} : Bool}, +hf: {Nat.is_le(1n+K, Nat.add(f, ni)) == True{} : Bool}, +hok: {C.fits(64n, S.factorial(ni)) == ok : Bool}, ha: FR(ok, a, S.factorial(ni)), +hmore: {more == Nat.is_lt(ni, nn) : Bool}, +hcn: {C.fits(64n, S.factorial(nn)) == cn : Bool}) -> {G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, i, n, (a, ok), more) == G.fits(WU.U64, Bool.not(cn), of(S.factorial(nn))) : Maybe<&2, WU.U64>}:
  match f ok more cn:
    case 0n True{} _ _:
      +big = NF.fbig(K, ni, hf)
      Empty.absurd({G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, i, n, (a, True{}), more) == G.fits(WU.U64, Bool.not(cn), of(S.factorial(nn))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(S.factorial(ni), C.pow2(K)), False{}, Equal.sym(Bool, Nat.is_lt(S.factorial(ni), C.pow2(K)), True{}, fk(K, hK, S.factorial(ni), hok)), N.le_not_lt(S.factorial(ni), C.pow2(K), big))))
    case 0n False{} _ True{}:
      Empty.absurd({G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, i, n, (a, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.factorial(nn))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.factorial(nn)), False{}, Equal.sym(Bool, C.fits(64n, S.factorial(nn)), True{}, hcn), unfit_mono(64n, S.factorial(ni), S.factorial(nn), hmono, hok))))
    case 0n False{} _ False{}:
      {==}
    case 1n+g False{} _ True{}:
      Empty.absurd({G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, i, n, (a, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.factorial(nn))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.factorial(nn)), False{}, Equal.sym(Bool, C.fits(64n, S.factorial(nn)), True{}, hcn), unfit_mono(64n, S.factorial(ni), S.factorial(nn), hmono, hok))))
    case 1n+g False{} _ False{}:
      {==}
    case 1n+g True{} False{} True{}:
      +eqF = N.le_antisym(S.factorial(ni), S.factorial(nn), hmono, NF.fmono(nn, ni, N.not_lt_le(ni, nn, Equal.sym(Bool, False{}, Nat.is_lt(ni, nn), hmore))))
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, a, of(S.factorial(nn)), as_of(a, S.factorial(nn), Equal.trans(Nat, v(a), S.factorial(ni), S.factorial(nn), ha, eqF)))
    case 1n+g True{} False{} False{}:
      +eqF = N.le_antisym(S.factorial(ni), S.factorial(nn), hmono, NF.fmono(nn, ni, N.not_lt_le(ni, nn, Equal.sym(Bool, False{}, Nat.is_lt(ni, nn), hmore))))
      Empty.absurd({G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, i, n, (a, True{}), False{}) == G.fits(WU.U64, Bool.not(False{}), of(S.factorial(nn))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.factorial(ni)), False{}, Equal.sym(Bool, C.fits(64n, S.factorial(ni)), True{}, hok), Equal.trans(Bool, C.fits(64n, S.factorial(ni)), C.fits(64n, S.factorial(nn)), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), S.factorial(ni), S.factorial(nn), eqF), hcn))))
    case 1n+ +g True{} True{} _:
      +hlt = Equal.sym(Bool, True{}, Nat.is_lt(ni, nn), hmore)
      +x = G.inc(~WU.U64, ~I.u64_op, i)
      +ex = inc_v(K, hK, i, n, ni, nn, hi, hn, hlt)
      +pn = S.factorial(1n+ni)
      +hpn = Equal.trans(Nat, Nat.mul(v(a), v(x)), Nat.mul(S.factorial(ni), 1n+ni), pn, nmul(v(a), v(x), S.factorial(ni), 1n+ni, ha, ex), NA.mul_comm(S.factorial(ni), 1n+ni))
      +hf2 = L.subst(Nat, z => {Nat.is_le(1n+K, z) == True{} : Bool}, 1n+Nat.add(g, ni), Nat.add(g, 1n+ni), Equal.sym(Nat, Nat.add(g, 1n+ni), 1n+Nat.add(g, ni), NA.add_succ(g, ni)), hf)
      factsim(g, x, n, I.u64_op(NM.Mul{a, x}), 1n+ni, nn, K, Bool.not(I.u64_is(NM.MulOver{a, x})), I.u64_is(NM.Lt{x, n}), cn, hK, ex, hn, NF.fmono(1n+ni, nn, succ_le(ni, nn, hlt)), hf2, ok_mul(a, x, pn, hpn), fr_mul(a, x, pn, hpn, C.fits(64n, pn), {==}), ltv(x, n, 1n+ni, nn, ex, hn), hcn)

def okfits(+x: Nat, +c: Bool) -> {G.ok(WU.U64, G.fits(WU.U64, Bool.not(c), of(x))) == SG.checked_pick(~WU.U64, ~SG.u64_of, x, c) : Result<&2, &2, NM.NumError, WU.U64>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def fact_top(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64) -> SG.Factorial.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, n):
  +one = I.u64_op(NM.One{})
  +F = S.factorial(v(n))
  +hf0 = L.subst(Nat, z => {Nat.is_le(1n+z, 141n) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), {==})
  +s = factsim(140n, one, n, one, 1n, v(n), K, True{}, I.u64_is(NM.Lt{one, n}), C.fits(64n, F), hK, one_v(), {==}, NF.fmono(0n, v(n), N.zero_le(v(n))), hf0, {==}, one_v(), ltv(one, n, 1n, v(n), one_v(), {==}), {==})
  +g = G.fact_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, one, n, (one, True{}), I.u64_is(NM.Lt{one, n}))
  Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), SG.checked_pick(~WU.U64, ~SG.u64_of, F, C.fits(64n, F)), SG.checked(~WU.U64, ~SG.u64_of, 64n, M.factorial(v(n))), Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), G.ok(WU.U64, G.fits(WU.U64, Bool.not(C.fits(64n, F)), of(F))), SG.checked_pick(~WU.U64, ~SG.u64_of, F, C.fits(64n, F)), Equal.cong(Maybe<&2, WU.U64>, Result<&2, &2, NM.NumError, WU.U64>, t => G.ok(WU.U64, t), g, G.fits(WU.U64, Bool.not(C.fits(64n, F)), of(F)), s), okfits(F, C.fits(64n, F))), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), F, M.factorial(v(n)), Equal.sym(Nat, M.factorial(v(n)), F, FA.factorial_ok(v(n)))))

def factorial_checked(+n: WU.U64) -> SG.Factorial.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, n):
  fact_top(64n, {==}, n)

# ---- perm: n (n - 1) ... multiplied top-down, j factors taken, r left ----

def pmon(+nn: Nat, +j: Nat, +r: Nat, +k0: Nat, +hj: {Nat.add(j, r) == k0 : Nat}, +hle: {Nat.is_le(k0, nn) == True{} : Bool}) -> {Nat.is_le(S.desc(nn, j), S.desc(nn, k0)) == True{} : Bool}:
  +h1 = NF.dmono(nn, j, r, L.subst(Nat, z => {Nat.is_le(z, nn) == True{} : Bool}, k0, Nat.add(j, r), Equal.sym(Nat, Nat.add(j, r), k0, hj), hle))
  L.subst(Nat, z => {Nat.is_le(S.desc(nn, j), S.desc(nn, z)) == True{} : Bool}, Nat.add(j, r), k0, hj, h1)

def le_v(+a: WU.U64, +b: WU.U64, +na: Nat, +nb: Nat, +ha: {v(a) == na : Nat}, +hb: {v(b) == nb : Nat}, +h: {Nat.is_le(na, nb) == True{} : Bool}) -> {Nat.is_le(v(a), v(b)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, nb) == True{} : Bool}, na, v(a), Equal.sym(Nat, v(a), na, ha), h)
  L.subst(Nat, z => {Nat.is_le(v(a), z) == True{} : Bool}, nb, v(b), Equal.sym(Nat, v(b), nb, hb), h1)

def permsim(+f: Nat, +k: WU.U64, +m: WU.U64, +a: WU.U64, +nn: Nat, +j: Nat, +r: Nat, +k0: Nat, +K: Nat, +ok: Bool, +more: Bool, +cn: Bool, +hK: {K == 64n : Nat}, +hkr: {v(k) == r : Nat}, +hm: {v(m) == Nat.sub(nn, j) : Nat}, +hj: {Nat.add(j, r) == k0 : Nat}, +hle: {Nat.is_le(k0, nn) == True{} : Bool}, +hf: {Nat.is_le(1n+K, Nat.add(f, j)) == True{} : Bool}, +hok: {C.fits(64n, S.desc(nn, j)) == ok : Bool}, ha: FR(ok, a, S.desc(nn, j)), +hmore: {more == Bool.not(Nat.is_eq(r, 0n)) : Bool}, +hcn: {C.fits(64n, S.desc(nn, k0)) == cn : Bool}) -> {G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, k, m, (a, ok), more) == G.fits(WU.U64, Bool.not(cn), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}:
  match f r ok more cn:
    case 0n _ True{} _ _:
      +hjk = L.subst(Nat, z => {Nat.is_le(j, z) == True{} : Bool}, Nat.add(j, r), k0, hj, N.le_add_right(j, r))
      +big = NF.dbig(K, nn, j, hf, N.le_trans(j, k0, nn, hjk, hle))
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, k, m, (a, True{}), more) == G.fits(WU.U64, Bool.not(cn), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(S.desc(nn, j), C.pow2(K)), False{}, Equal.sym(Bool, Nat.is_lt(S.desc(nn, j), C.pow2(K)), True{}, fk(K, hK, S.desc(nn, j), hok)), N.le_not_lt(S.desc(nn, j), C.pow2(K), big))))
    case 0n _ False{} _ True{}:
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, k, m, (a, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.desc(nn, k0)), False{}, Equal.sym(Bool, C.fits(64n, S.desc(nn, k0)), True{}, hcn), unfit_mono(64n, S.desc(nn, j), S.desc(nn, k0), pmon(nn, j, r, k0, hj, hle), hok))))
    case 0n _ False{} _ False{}:
      {==}
    case 1n+g _ False{} _ True{}:
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, m, (a, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.desc(nn, k0)), False{}, Equal.sym(Bool, C.fits(64n, S.desc(nn, k0)), True{}, hcn), unfit_mono(64n, S.desc(nn, j), S.desc(nn, k0), pmon(nn, j, r, k0, hj, hle), hok))))
    case 1n+g _ False{} _ False{}:
      {==}
    case 1n+g 0n True{} False{} True{}:
      +ejk = Equal.trans(Nat, j, Nat.add(j, 0n), k0, Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)), hj)
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, a, of(S.desc(nn, k0)), as_of(a, S.desc(nn, k0), Equal.trans(Nat, v(a), S.desc(nn, j), S.desc(nn, k0), ha, Equal.cong(Nat, Nat, t => S.desc(nn, t), j, k0, ejk))))
    case 1n+g 0n True{} False{} False{}:
      +ejk = Equal.trans(Nat, j, Nat.add(j, 0n), k0, Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)), hj)
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, m, (a, True{}), False{}) == G.fits(WU.U64, Bool.not(False{}), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.desc(nn, j)), False{}, Equal.sym(Bool, C.fits(64n, S.desc(nn, j)), True{}, hok), Equal.trans(Bool, C.fits(64n, S.desc(nn, j)), C.fits(64n, S.desc(nn, k0)), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, S.desc(nn, t)), j, k0, ejk), hcn))))
    case 1n+g 1n+rp True{} False{} _:
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, m, (a, True{}), False{}) == G.fits(WU.U64, Bool.not(cn), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.sym(Bool, False{}, True{}, hmore)))
    case 1n+g 0n True{} True{} _:
      Empty.absurd({G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, k, m, (a, True{}), True{}) == G.fits(WU.U64, Bool.not(cn), of(S.desc(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(hmore))
    case 1n+ +g 1n+ +rp True{} True{} _:
      +one = I.u64_op(NM.One{})
      +es = NA.add_succ(j, rp)
      +hj1 = N.le_lt_trans(j, Nat.add(j, rp), 1n+Nat.add(j, rp), N.le_add_right(j, rp), N.lt_succ(Nat.add(j, rp)))
      +hj2 = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, 1n+Nat.add(j, rp), k0, Equal.trans(Nat, 1n+Nat.add(j, rp), Nat.add(j, 1n+rp), k0, Equal.sym(Nat, Nat.add(j, 1n+rp), 1n+Nat.add(j, rp), es), hj), hj1)
      +hjn = N.lt_le_trans(j, k0, nn, hj2, hle)
      +X = Nat.sub(nn, 1n+j)
      +esx = FA.sub_lt_succ(nn, j, hjn)
      +hpn = Equal.trans(Nat, Nat.mul(v(a), v(m)), Nat.mul(S.desc(nn, j), Nat.sub(nn, j)), S.desc(nn, 1n+j), nmul(v(a), v(m), S.desc(nn, j), Nat.sub(nn, j), ha, hm), NA.mul_comm(S.desc(nn, j), Nat.sub(nn, j)))
      +dk = G.dec(~WU.U64, ~I.u64_op, k)
      +edk = Equal.trans(Nat, v(dk), Nat.sub(v(k), v(one)), rp, LW.ops_sub(k, one, le_v(one, k, 1n, 1n+rp, one_v(), hkr, N.zero_le(rp))), Equal.trans(Nat, Nat.sub(v(k), v(one)), Nat.sub(1n+rp, 1n), rp, nsub(v(k), v(one), 1n+rp, 1n, hkr, one_v()), N.sub_zero(rp)))
      +emx = Equal.trans(Nat, v(m), Nat.sub(nn, j), 1n+X, hm, esx)
      +dm2 = G.dec(~WU.U64, ~I.u64_op, m)
      +edm = Equal.trans(Nat, v(dm2), Nat.sub(v(m), v(one)), X, LW.ops_sub(m, one, le_v(one, m, 1n, 1n+X, one_v(), emx, N.zero_le(X))), Equal.trans(Nat, Nat.sub(v(m), v(one)), Nat.sub(1n+X, 1n), X, nsub(v(m), v(one), 1n+X, 1n, emx, one_v()), N.sub_zero(X)))
      +hmore2 = Equal.cong(Bool, Bool, t => Bool.not(t), I.u64_is(NM.IsZero{dk}), Nat.is_eq(rp, 0n), iz(dk, rp, edk))
      +hjj = Equal.trans(Nat, 1n+Nat.add(j, rp), Nat.add(j, 1n+rp), k0, Equal.sym(Nat, Nat.add(j, 1n+rp), 1n+Nat.add(j, rp), es), hj)
      +hf2 = L.subst(Nat, z => {Nat.is_le(1n+K, z) == True{} : Bool}, 1n+Nat.add(g, j), Nat.add(g, 1n+j), Equal.sym(Nat, Nat.add(g, 1n+j), 1n+Nat.add(g, j), NA.add_succ(g, j)), hf)
      +pn = S.desc(nn, 1n+j)
      permsim(g, dk, dm2, I.u64_op(NM.Mul{a, m}), nn, 1n+j, rp, k0, K, Bool.not(I.u64_is(NM.MulOver{a, m})), Bool.not(I.u64_is(NM.IsZero{dk})), cn, hK, edk, edm, hjj, hle, hf2, ok_mul(a, m, pn, hpn), fr_mul(a, m, pn, hpn, C.fits(64n, pn), {==}), hmore2, hcn)

def perm_top(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +k: WU.U64, +big: Bool, +hbig: {I.u64_is(NM.Lt{n, k}) == big : Bool}) -> {G.perm_big(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, big) == SG.checked(~WU.U64, ~SG.u64_of, 64n, S.desc(v(n), v(k))) : Result<&2, &2, NM.NumError, WU.U64>}:
  match big:
    case True{}:
      +dz = NF.desc_zero(v(n), v(k), lt_of(n, k, True{}, hbig))
      Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, Done{I.u64_op(NM.ZeroOp{})}, SG.checked(~WU.U64, ~SG.u64_of, 64n, 0n), SG.checked(~WU.U64, ~SG.u64_of, 64n, S.desc(v(n), v(k))), Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.ZeroOp{}), of(0n), as_of(I.u64_op(NM.ZeroOp{}), 0n, zero_v())), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), 0n, S.desc(v(n), v(k)), Equal.sym(Nat, S.desc(v(n), v(k)), 0n, dz)))
    case False{}:
      +one = I.u64_op(NM.One{})
      +D = S.desc(v(n), v(k))
      +hge = N.not_lt_le(v(n), v(k), lt_of(n, k, False{}, hbig))
      +hf0 = L.subst(Nat, z => {Nat.is_le(1n+z, 140n) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), {==})
      +hm0 = Equal.sym(Nat, Nat.sub(v(n), 0n), v(n), N.sub_zero(v(n)))
      +more = Bool.not(I.u64_is(NM.IsZero{k}))
      +hmore = Equal.cong(Bool, Bool, t => Bool.not(t), I.u64_is(NM.IsZero{k}), Nat.is_eq(v(k), 0n), iz(k, v(k), {==}))
      +s = permsim(140n, k, n, one, v(n), 0n, v(k), v(k), K, True{}, more, C.fits(64n, D), hK, {==}, hm0, {==}, hge, hf0, {==}, one_v(), hmore, {==})
      +g = G.perm_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, k, n, (one, True{}), more)
      Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), G.ok(WU.U64, G.fits(WU.U64, Bool.not(C.fits(64n, D)), of(D))), SG.checked(~WU.U64, ~SG.u64_of, 64n, D), Equal.cong(Maybe<&2, WU.U64>, Result<&2, &2, NM.NumError, WU.U64>, t => G.ok(WU.U64, t), g, G.fits(WU.U64, Bool.not(C.fits(64n, D)), of(D)), s), okfits(D, C.fits(64n, D)))

def perm_checked(+n: WU.U64, +k: WU.U64) -> SG.Perm.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, n, k):
  Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.perm_big(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, I.u64_is(NM.Lt{n, k})), SG.checked(~WU.U64, ~SG.u64_of, 64n, S.desc(v(n), v(k))), SG.checked(~WU.U64, ~SG.u64_of, 64n, M.perm(v(n), v(k))), perm_top(64n, {==}, n, k, I.u64_is(NM.Lt{n, k}), {==}), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), S.desc(v(n), v(k)), M.perm(v(n), v(k)), Equal.sym(Nat, M.perm(v(n), v(k)), S.desc(v(n), v(k)), FA.perm_ok(v(n), v(k)))))

# ---- pow: square-and-multiply with fit flags ----

# y when ok, else x: {fv(ok, v(a), x) == x} says v(a) == x when ok
def fv(ok: Bool, +y: Nat, +x: Nat) -> Nat:
  match ok:
    case True{}:
      y
    case False{}:
      x

# md: every value >= 1, or every value <= 1 (the base 0 case)
def mode(md: Bool, +x: Nat) -> Bool:
  match md:
    case True{}:
      Nat.is_le(1n, x)
    case False{}:
      Nat.is_le(x, 1n)

def small_fits(+x: Nat, +h: {Nat.is_le(x, 1n) == True{} : Bool}) -> {C.fits(64n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+y:
      Empty.absurd({C.fits(64n, 2n+y) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

def small_mul(+x: Nat, +y: Nat, +hx: {Nat.is_le(x, 1n) == True{} : Bool}, +hy: {Nat.is_le(y, 1n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(x, y), 1n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n:
      L.subst(Nat, z => {Nat.is_le(z, 1n) == True{} : Bool}, y, Nat.add(y, 0n), Equal.sym(Nat, Nat.add(y, 0n), y, N.add_zero(y)), hy)
    case 2n+z:
      Empty.absurd({Nat.is_le(Nat.mul(2n+z, y), 1n) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hx)))

def pos_of(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+y:
      {==}

# x unfit, 1 <= y: x y unfit
def unfit_mul(+x: Nat, +y: Nat, +hx: {C.fits(64n, x) == False{} : Bool}, +hy: {Nat.is_le(1n, y) == True{} : Bool}) -> {C.fits(64n, Nat.mul(x, y)) == False{} : Bool}:
  unfit_mono(64n, x, Nat.mul(x, y), RT.le_mul_pos(x, y, pos_of(y, hy)), hx)

def unfit_mul_r(+x: Nat, +y: Nat, +hy: {C.fits(64n, y) == False{} : Bool}, +hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {C.fits(64n, Nat.mul(x, y)) == False{} : Bool}:
  L.subst(Nat, z => {C.fits(64n, z) == False{} : Bool}, Nat.mul(y, x), Nat.mul(x, y), NA.mul_comm(y, x), unfit_mul(y, x, hy, hx))

# an unfit value is >= 1, so the mode is the >= 1 one
def unfit_big(+x: Nat, +md: Bool, +hm: {mode(md, x) == True{} : Bool}, +hx: {C.fits(64n, x) == False{} : Bool}) -> {md == True{} : Bool}:
  match md:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, x), False{}, Equal.sym(Bool, C.fits(64n, x), True{}, small_fits(x, hm)), hx)))

def fv_mul(+a: WU.U64, +x: WU.U64, +n: Nat, +hn: {Nat.mul(v(a), v(x)) == n : Nat}, +c: Bool, +hc: {C.fits(64n, n) == c : Bool}) -> {fv(Bool.not(I.u64_is(NM.MulOver{a, x})), v(I.u64_op(NM.Mul{a, x})), n) == n : Nat}:
  match c:
    case True{}:
      +hmo = mo_of(a, x, n, hn, True{}, hc)
      %Equal.sym(Bool, I.u64_is(NM.MulOver{a, x}), False{}, hmo) : {fv(Bool.not(_), v(I.u64_op(NM.Mul{a, x})), n) == n : Nat}
      Equal.trans(Nat, v(I.u64_op(NM.Mul{a, x})), Nat.mul(v(a), v(x)), n, LW.ops_mul(a, x, hmo), hn)
    case False{}:
      %Equal.sym(Bool, I.u64_is(NM.MulOver{a, x}), True{}, mo_of(a, x, n, hn, False{}, hc)) : {fv(Bool.not(_), v(I.u64_op(NM.Mul{a, x})), n) == n : Nat}
      {==}

# -- the squared base --

def sq_fits(+more: Bool, +b: WU.U64, +bok: Bool, +nb: Nat, +md: Bool, +hB: {C.fits(64n, nb) == bok : Bool}, +hb: {fv(bok, v(b), nb) == nb : Nat}, +hm: {mode(md, nb) == True{} : Bool}) -> {C.fits(64n, NF.sqn(more, nb)) == G.sq_ok(~WU.U64, ~I.u64_is, more, b, bok) : Bool}:
  match more bok:
    case False{} _:
      hB
    case True{} True{}:
      ok_mul(b, b, Nat.mul(nb, nb), nmul(v(b), v(b), nb, nb, hb, hb))
    case True{} False{}:
      +md1 = unfit_big(nb, md, hm, hB)
      +h1 = L.subst(Bool, t => {mode(t, nb) == True{} : Bool}, md, True{}, md1, hm)
      unfit_mul(nb, nb, hB, h1)

def sq_fv(+more: Bool, +b: WU.U64, +bok: Bool, +nb: Nat, +hb: {fv(bok, v(b), nb) == nb : Nat}) -> {fv(G.sq_ok(~WU.U64, ~I.u64_is, more, b, bok), v(G.sq_val(~WU.U64, ~I.u64_op, more, b)), NF.sqn(more, nb)) == NF.sqn(more, nb) : Nat}:
  match more bok:
    case False{} _:
      hb
    case True{} True{}:
      fv_mul(b, b, Nat.mul(nb, nb), nmul(v(b), v(b), nb, nb, hb, hb), C.fits(64n, Nat.mul(nb, nb)), {==})
    case True{} False{}:
      {==}

def sq_mode(+more: Bool, +nb: Nat, +md: Bool, +hm: {mode(md, nb) == True{} : Bool}) -> {mode(md, NF.sqn(more, nb)) == True{} : Bool}:
  match more md:
    case False{} _:
      hm
    case True{} True{}:
      N.le_trans(1n, nb, Nat.mul(nb, nb), hm, RT.le_mul_pos(nb, nb, pos_of(nb, hm)))
    case True{} False{}:
      small_mul(nb, nb, hm, hm)

# -- the accumulator --

def ms_a(bit: Bool, +a: WU.U64, +b: WU.U64) -> WU.U64:
  match bit:
    case True{}:
      I.u64_op(NM.Mul{a, b})
    case False{}:
      a

def ms_ok(bit: Bool, +a: WU.U64, +aok: Bool, +b: WU.U64, +bok: Bool) -> Bool:
  match bit:
    case True{}:
      Bool.and(Bool.and(aok, bok), Bool.not(I.u64_is(NM.MulOver{a, b})))
    case False{}:
      aok

def ms_eq(+bit: Bool, +b: WU.U64, +bok: Bool, +a: WU.U64, +aok: Bool) -> {G.mul_st(~WU.U64, ~I.u64_op, ~I.u64_is, bit, b, bok, (a, aok)) == (ms_a(bit, a, b), ms_ok(bit, a, aok, b, bok)) : WU.U64 & Bool}:
  match bit:
    case True{}:
      {==}
    case False{}:
      {==}

def ms_fits(+bit: Bool, +a: WU.U64, +aok: Bool, +b: WU.U64, +bok: Bool, +na: Nat, +nb: Nat, +md: Bool, +hA: {C.fits(64n, na) == aok : Bool}, +ha: {fv(aok, v(a), na) == na : Nat}, +hma: {mode(md, na) == True{} : Bool}, +hB: {C.fits(64n, nb) == bok : Bool}, +hb: {fv(bok, v(b), nb) == nb : Nat}, +hmb: {mode(md, nb) == True{} : Bool}) -> {C.fits(64n, NF.msn(bit, na, nb)) == ms_ok(bit, a, aok, b, bok) : Bool}:
  match bit aok bok:
    case False{} _ _:
      hA
    case True{} True{} True{}:
      ok_mul(a, b, Nat.mul(na, nb), nmul(v(a), v(b), na, nb, ha, hb))
    case True{} False{} _:
      +md1 = unfit_big(na, md, hma, hA)
      unfit_mul(na, nb, hA, L.subst(Bool, t => {mode(t, nb) == True{} : Bool}, md, True{}, md1, hmb))
    case True{} True{} False{}:
      +md1 = unfit_big(nb, md, hmb, hB)
      unfit_mul_r(na, nb, hB, L.subst(Bool, t => {mode(t, na) == True{} : Bool}, md, True{}, md1, hma))

def ms_fv(+bit: Bool, +a: WU.U64, +aok: Bool, +b: WU.U64, +bok: Bool, +na: Nat, +nb: Nat, +ha: {fv(aok, v(a), na) == na : Nat}, +hb: {fv(bok, v(b), nb) == nb : Nat}) -> {fv(ms_ok(bit, a, aok, b, bok), v(ms_a(bit, a, b)), NF.msn(bit, na, nb)) == NF.msn(bit, na, nb) : Nat}:
  match bit aok bok:
    case False{} _ _:
      ha
    case True{} True{} True{}:
      fv_mul(a, b, Nat.mul(na, nb), nmul(v(a), v(b), na, nb, ha, hb), C.fits(64n, Nat.mul(na, nb)), {==})
    case True{} False{} _:
      {==}
    case True{} True{} False{}:
      {==}

def ms_mode(+bit: Bool, +na: Nat, +nb: Nat, +md: Bool, +hma: {mode(md, na) == True{} : Bool}, +hmb: {mode(md, nb) == True{} : Bool}) -> {mode(md, NF.msn(bit, na, nb)) == True{} : Bool}:
  match bit md:
    case False{} _:
      hma
    case True{} True{}:
      N.le_trans(1n, na, Nat.mul(na, nb), hma, RT.le_mul_pos(na, nb, pos_of(nb, hmb)))
    case True{} False{}:
      small_mul(na, nb, hma, hmb)

def pw_fin(+a: WU.U64, +aok: Bool, +na: Nat, +t0: Nat, +ct: Bool, +hA: {C.fits(64n, na) == aok : Bool}, +ha: {fv(aok, v(a), na) == na : Nat}, +et: {na == t0 : Nat}, +hct: {C.fits(64n, t0) == ct : Bool}) -> {G.fits(WU.U64, Bool.not(aok), a) == G.fits(WU.U64, Bool.not(ct), of(t0)) : Maybe<&2, WU.U64>}:
  match aok ct:
    case True{} True{}:
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, a, of(t0), as_of(a, t0, Equal.trans(Nat, v(a), na, t0, ha, et)))
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({G.fits(WU.U64, Bool.not(True{}), a) == G.fits(WU.U64, Bool.not(False{}), of(t0)) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, na), False{}, Equal.sym(Bool, C.fits(64n, na), True{}, hA), Equal.trans(Bool, C.fits(64n, na), C.fits(64n, t0), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), na, t0, et), hct))))
    case False{} True{}:
      Empty.absurd({G.fits(WU.U64, Bool.not(False{}), a) == G.fits(WU.U64, Bool.not(True{}), of(t0)) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, t0), False{}, Equal.sym(Bool, C.fits(64n, t0), True{}, hct), Equal.trans(Bool, C.fits(64n, t0), C.fits(64n, na), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), t0, na, Equal.sym(Nat, na, t0, et)), hA))))

def powsim(+f: Nat, +e: Nat, +b: WU.U64, +bok: Bool, +a: WU.U64, +aok: Bool, +nb: Nat, +na: Nat, +t0: Nat, +md: Bool, +ct: Bool, +he: {Nat.is_le(e, f) == True{} : Bool}, +hB: {C.fits(64n, nb) == bok : Bool}, +hb: {fv(bok, v(b), nb) == nb : Nat}, +hmb: {mode(md, nb) == True{} : Bool}, +hA: {C.fits(64n, na) == aok : Bool}, +ha: {fv(aok, v(a), na) == na : Nat}, +hma: {mode(md, na) == True{} : Bool}, +ht: {Nat.mul(na, Nat.pow(nb, e)) == t0 : Nat}, +hct: {C.fits(64n, t0) == ct : Bool}) -> {G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, e, b, bok, (a, aok)) == G.fits(WU.U64, Bool.not(ct), of(t0)) : Maybe<&2, WU.U64>}:
  match f e:
    case 0n 0n:
      pw_fin(a, aok, na, t0, ct, hA, ha, Equal.trans(Nat, na, Nat.mul(na, 1n), t0, Equal.sym(Nat, Nat.mul(na, 1n), na, NA.mul_one(na)), ht), hct)
    case 0n 1n+j:
      Empty.absurd({G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, 1n+j, b, bok, (a, aok)) == G.fits(WU.U64, Bool.not(ct), of(t0)) : Maybe<&2, WU.U64>}, true_ne_false(Equal.sym(Bool, False{}, True{}, he)))
    case 1n+g 0n:
      pw_fin(a, aok, na, t0, ct, hA, ha, Equal.trans(Nat, na, Nat.mul(na, 1n), t0, Equal.sym(Nat, Nat.mul(na, 1n), na, NA.mul_one(na)), ht), hct)
    case 1n+ +g 1n+ +j:
      +more = Nat.is_lt(1n, 1n+j)
      +bit = Nat.is_eq(Nat.mod(1n+j, 2n), 1n)
      +e2 = Nat.div(1n+j, 2n)
      +ht2 = Equal.trans(Nat, Nat.mul(NF.msn(bit, na, nb), Nat.pow(NF.sqn(more, nb), e2)), Nat.mul(na, Nat.pow(nb, 1n+j)), t0, NF.powstep(j, na, nb), ht)
      +he2 = N.le_trans(e2, j, g, NF.half_le(j), he)
      +ih = powsim(g, e2, G.sq_val(~WU.U64, ~I.u64_op, more, b), G.sq_ok(~WU.U64, ~I.u64_is, more, b, bok), ms_a(bit, a, b), ms_ok(bit, a, aok, b, bok), NF.sqn(more, nb), NF.msn(bit, na, nb), t0, md, ct, he2, sq_fits(more, b, bok, nb, md, hB, hb, hmb), sq_fv(more, b, bok, nb, hb), sq_mode(more, nb, md, hmb), ms_fits(bit, a, aok, b, bok, na, nb, md, hA, ha, hma, hB, hb, hmb), ms_fv(bit, a, aok, b, bok, na, nb, ha, hb), ms_mode(bit, na, nb, md, hma, hmb), ht2, hct)
      L.subst(WU.U64 & Bool, z => {G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, g, e2, G.sq_val(~WU.U64, ~I.u64_op, more, b), G.sq_ok(~WU.U64, ~I.u64_is, more, b, bok), z) == G.fits(WU.U64, Bool.not(ct), of(t0)) : Maybe<&2, WU.U64>}, (ms_a(bit, a, b), ms_ok(bit, a, aok, b, bok)), G.mul_st(~WU.U64, ~I.u64_op, ~I.u64_is, bit, b, bok, (a, aok)), Equal.sym(WU.U64 & Bool, G.mul_st(~WU.U64, ~I.u64_op, ~I.u64_is, bit, b, bok, (a, aok)), (ms_a(bit, a, b), ms_ok(bit, a, aok, b, bok)), ms_eq(bit, b, bok, a, aok)), ih)

def md_init(+x: Nat) -> {mode(Nat.is_le(1n, x), x) == True{} : Bool} & {mode(Nat.is_le(1n, x), 1n) == True{} : Bool}:
  match x:
    case 0n:
      ({==}, {==})
    case 1n+y:
      +ez = Equal.sym(Bool, Nat.is_le(0n, y), True{}, N.zero_le(y))
      (L.subst(Bool, t => {mode(t, 1n+y) == True{} : Bool}, True{}, Nat.is_le(0n, y), ez, N.zero_le(y)), L.subst(Bool, t => {mode(t, 1n) == True{} : Bool}, True{}, Nat.is_le(0n, y), ez, {==}))

def pow_fin(+x: WU.U64, +k: Nat, p: {mode(Nat.is_le(1n, v(x)), v(x)) == True{} : Bool} & {mode(Nat.is_le(1n, v(x)), 1n) == True{} : Bool}) -> SG.Pow.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, x, k):
  (+hmb, +hma) = p
  +one = I.u64_op(NM.One{})
  +t0 = Nat.pow(v(x), k)
  +ht = Equal.trans(Nat, Nat.mul(1n, t0), Nat.add(t0, 0n), t0, {==}, N.add_zero(t0))
  +s = powsim(1n+k, k, x, True{}, one, True{}, v(x), 1n, t0, Nat.is_le(1n, v(x)), C.fits(64n, t0), N.le_succ(k), LW.vb(x), {==}, hmb, {==}, one_v(), hma, ht, {==})
  +g = G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+k, k, x, True{}, (one, True{}))
  Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), G.ok(WU.U64, G.fits(WU.U64, Bool.not(C.fits(64n, t0)), of(t0))), SG.checked(~WU.U64, ~SG.u64_of, 64n, t0), Equal.cong(Maybe<&2, WU.U64>, Result<&2, &2, NM.NumError, WU.U64>, t => G.ok(WU.U64, t), g, G.fits(WU.U64, Bool.not(C.fits(64n, t0)), of(t0)), s), okfits(t0, C.fits(64n, t0)))

def pow_checked(+x: WU.U64, +k: Nat) -> SG.Pow.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, x, k):
  pow_fin(x, k, md_init(v(x)))

# ---- iroot: bisection with lo <= R < lo + w, the width halving ----

def pw_val(+x: WU.U64, +k: Nat, p: {mode(Nat.is_le(1n, v(x)), v(x)) == True{} : Bool} & {mode(Nat.is_le(1n, v(x)), 1n) == True{} : Bool}) -> {G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+k, k, x, True{}, (I.u64_op(NM.One{}), True{})) == G.fits(WU.U64, Bool.not(C.fits(64n, Nat.pow(v(x), k))), of(Nat.pow(v(x), k))) : Maybe<&2, WU.U64>}:
  (+hmb, +hma) = p
  +t0 = Nat.pow(v(x), k)
  +ht = Equal.trans(Nat, Nat.mul(1n, t0), Nat.add(t0, 0n), t0, {==}, N.add_zero(t0))
  powsim(1n+k, k, x, True{}, I.u64_op(NM.One{}), True{}, v(x), 1n, t0, Nat.is_le(1n, v(x)), C.fits(64n, t0), N.le_succ(k), LW.vb(x), {==}, hmb, {==}, one_v(), hma, ht, {==})

def rlf(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +P: Nat, +c: Bool, +hc: {C.fits(64n, P) == c : Bool}) -> {G.root_le_fin(~WU.U64, ~I.u64_op, ~I.u64_is, n, G.fits(WU.U64, Bool.not(c), of(P))) == Nat.is_le(P, v(n)) : Bool}:
  match c:
    case True{}:
      lev(of(P), n, P, v(n), LW.vo(P, hc), {==})
    case False{}:
      +h1 = L.subst(Nat, z => {C.fits(z, P) == False{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), hc)
      +h2 = Equal.trans(Bool, Nat.is_lt(P, C.pow2(K)), C.fits(K, P), False{}, Equal.sym(Bool, C.fits(K, P), Nat.is_lt(P, C.pow2(K)), WW.fits_lt(K, P)), h1)
      +hn = N.lt_le_trans(v(n), C.pow2(K), P, LW.val_lt(K, hK, n), N.not_lt_le(P, C.pow2(K), h2))
      Equal.sym(Bool, Nat.is_le(P, v(n)), False{}, N.lt_not_le(v(n), P, hn))

def rl_v(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +k: Nat, +r: WU.U64) -> {G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, r) == Nat.is_le(Nat.pow(v(r), k), v(n)) : Bool}:
  +P = Nat.pow(v(r), k)
  Equal.trans(Bool, G.root_le_fin(~WU.U64, ~I.u64_op, ~I.u64_is, n, G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+k, k, r, True{}, (I.u64_op(NM.One{}), True{}))), G.root_le_fin(~WU.U64, ~I.u64_op, ~I.u64_is, n, G.fits(WU.U64, Bool.not(C.fits(64n, P)), of(P))), Nat.is_le(P, v(n)), Equal.cong(Maybe<&2, WU.U64>, Bool, t => G.root_le_fin(~WU.U64, ~I.u64_op, ~I.u64_is, n, t), G.pow_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+k, k, r, True{}, (I.u64_op(NM.One{}), True{})), G.fits(WU.U64, Bool.not(C.fits(64n, P)), of(P)), pw_val(r, k, md_init(v(r)))), rlf(K, hK, n, P, C.fits(64n, P), {==}))

def imid_v(+K: Nat, +hK: {K == 64n : Nat}, +lo: WU.U64, +hi: WU.U64, +a: Nat, +w: Nat, +ha: {v(lo) == a : Nat}, +hh: {v(hi) == Nat.add(a, w) : Nat}) -> {v(G.imid(~WU.U64, ~I.u64_op, lo, hi)) == Nat.add(a, Nat.div(w, 2n)) : Nat}:
  +s = I.u64_op(NM.Sub{hi, lo})
  +es = Equal.trans(Nat, v(s), Nat.sub(v(hi), v(lo)), w, LW.ops_sub(hi, lo, le_v(lo, hi, a, Nat.add(a, w), ha, hh, N.le_add_right(a, w))), Equal.trans(Nat, Nat.sub(v(hi), v(lo)), Nat.sub(Nat.add(a, w), a), w, nsub(v(hi), v(lo), Nat.add(a, w), a, hh, ha), N.add_sub_cancel(a, w)))
  +h = I.u64_op(NM.Half{s})
  +eh = Equal.trans(Nat, v(h), Nat.div(v(s), 2n), Nat.div(w, 2n), LW.ops_half(s), Equal.cong(Nat, Nat, t => Nat.div(t, 2n), v(s), w, es))
  +sum = Nat.add(a, Nat.div(w, 2n))
  +esum = nadd(v(lo), v(h), a, Nat.div(w, 2n), ha, eh)
  +hle = N.le_add_left(Nat.div(w, 2n), w, a, AR2.div_le(w, 2n))
  +hhk = L.subst(Nat, z => {Nat.is_lt(z, C.pow2(K)) == True{} : Bool}, v(hi), Nat.add(a, w), hh, LW.val_lt(K, hK, hi))
  +hfit = fits32(K, hK, sum, N.le_lt_trans(sum, Nat.add(a, w), C.pow2(K), hle, hhk))
  Equal.trans(Nat, v(I.u64_op(NM.Add{lo, h})), Nat.add(v(lo), v(h)), sum, LW.ops_add(lo, h, ao_of(lo, h, sum, esum, True{}, hfit)), esum)

def lt_add_r(+a: Nat, +q: Nat, +h: {Nat.is_lt(0n, q) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(a, q)) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, 0n), Nat.add(a, q)), Nat.is_lt(0n, q), True{}, NF.lt_add_cancel(a, 0n, q), h)
  L.subst(Nat, z => {Nat.is_lt(z, Nat.add(a, q)) == True{} : Bool}, Nat.add(a, 0n), a, N.add_zero(a), h1)

# inc(lo) < lo + w as 1 < w
def more_v(+K: Nat, +hK: {K == 64n : Nat}, +lo: WU.U64, +hi: WU.U64, +a: Nat, +w: Nat, +ha: {v(lo) == a : Nat}, +hh: {v(hi) == Nat.add(a, w) : Nat}, +hw: {Nat.is_lt(0n, w) == True{} : Bool}) -> {I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, lo), hi}) == Nat.is_lt(1n, w) : Bool}:
  +ei = inc_v(K, hK, lo, hi, a, Nat.add(a, w), ha, hh, lt_add_r(a, w, hw))
  Equal.trans(Bool, I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, lo), hi}), Nat.is_lt(1n+a, Nat.add(a, w)), Nat.is_lt(1n, w), ltv(G.inc(~WU.U64, ~I.u64_op, lo), hi, 1n+a, Nat.add(a, w), ei, hh), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(a, w)) == Nat.is_lt(1n, w) : Bool}, Nat.add(a, 1n), 1n+a, plus1(a), NF.lt_add_cancel(a, 1n, w)))

def srch(+f: Nat, +n: WU.U64, +k: Nat, +lo: WU.U64, +hi: WU.U64, +m: WU.U64, +more: Bool, +hit: Bool, +j: Nat, +nlo: Nat, +w: Nat, +R: Nat, +K: Nat, +hK: {K == 64n : Nat}, +hlo: {v(lo) == nlo : Nat}, +hhi: {v(hi) == Nat.add(nlo, w) : Nat}, +hm: {v(m) == Nat.add(nlo, Nat.div(w, 2n)) : Nat}, +hR1: {Nat.is_le(Nat.pow(R, k), v(n)) == True{} : Bool}, +hR2: {Nat.is_lt(v(n), Nat.pow(1n+R, k)) == True{} : Bool}, +hl: {Nat.is_le(nlo, R) == True{} : Bool}, +hr: {Nat.is_lt(R, Nat.add(nlo, w)) == True{} : Bool}, +hmore: {more == Nat.is_lt(1n, w) : Bool}, +hhit: {hit == Nat.is_le(Nat.pow(Nat.add(nlo, Nat.div(w, 2n)), k), v(n)) : Bool}, +hw: {Nat.is_le(w, C.pow2(j)) == True{} : Bool}, +hf: {Nat.is_le(1n+j, f) == True{} : Bool}) -> {v(G.search_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, n, k, lo, hi, m, more, hit)) == R : Nat}:
  match f more hit j:
    case 0n _ _ _:
      Empty.absurd({v(G.search_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, n, k, lo, hi, m, more, hit)) == R : Nat}, true_ne_false(Equal.sym(Bool, False{}, True{}, hf)))
    case 1n+g False{} _ _:
      +hw1 = N.not_lt_le(1n, w, Equal.sym(Bool, False{}, Nat.is_lt(1n, w), hmore))
      +h1 = L.subst(Nat, z => {Nat.is_le(Nat.add(nlo, w), z) == True{} : Bool}, Nat.add(nlo, 1n), 1n+nlo, plus1(nlo), N.le_add_left(w, 1n, nlo, hw1))
      +hrl = N.lt_succ_le(R, nlo, N.lt_le_trans(R, Nat.add(nlo, w), 1n+nlo, hr, h1))
      Equal.trans(Nat, v(lo), nlo, R, hlo, N.le_antisym(nlo, R, hl, hrl))
    case 1n+g True{} _ 0n:
      Empty.absurd({v(G.search_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, n, k, lo, hi, m, True{}, hit)) == R : Nat}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(1n, w), False{}, hmore, N.le_not_lt(1n, w, hw))))
    case 1n+ +g True{} True{} 1n+ +jp:
      +q = Nat.div(w, 2n)
      +X = Nat.add(nlo, q)
      +w2 = Nat.sub(w, q)
      +hqw = Equal.trans(Nat, Nat.add(q, w2), w, w, N.sub_add(w, q, AR2.div_le(w, 2n)), {==})
      +ehi = Equal.trans(Nat, Nat.add(X, w2), Nat.add(nlo, Nat.add(q, w2)), Nat.add(nlo, w), N.add_assoc(nlo, q, w2), Equal.cong(Nat, Nat, t => Nat.add(nlo, t), Nat.add(q, w2), w, hqw))
      +hhi2 = Equal.trans(Nat, v(hi), Nat.add(nlo, w), Nat.add(X, w2), hhi, Equal.sym(Nat, Nat.add(X, w2), Nat.add(nlo, w), ehi))
      +hw0 = N.lt_trans(0n, 1n, w, {==}, Equal.sym(Bool, True{}, Nat.is_lt(1n, w), hmore))
      +hdw = L.subst(Nat, z => {Nat.is_lt(w, z) == True{} : Bool}, Nat.add(w, w), Nat.double(w), Equal.sym(Nat, Nat.double(w), Nat.add(w, w), NA.double_self(w)), lt_add_r(w, w, hw0))
      +hpos = RT.sub_pos(q, w, NF.half_below(w, w, hdw))
      +m2 = G.imid(~WU.U64, ~I.u64_op, m, hi)
      +hm2 = imid_v(K, hK, m, hi, X, w2, hm, hhi2)
      +hmore2 = more_v(K, hK, m, hi, X, w2, hm, hhi2, hpos)
      +hhit2 = Equal.trans(Bool, G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, m2), Nat.is_le(Nat.pow(v(m2), k), v(n)), Nat.is_le(Nat.pow(Nat.add(X, Nat.div(w2, 2n)), k), v(n)), rl_v(K, hK, n, k, m2), Equal.cong(Nat, Bool, t => Nat.is_le(Nat.pow(t, k), v(n)), v(m2), Nat.add(X, Nat.div(w2, 2n)), hm2))
      +hl2 = NF.root_below(R, X, k, v(n), Equal.sym(Bool, True{}, Nat.is_le(Nat.pow(X, k), v(n)), hhit), hR2)
      +hr2 = L.subst(Nat, z => {Nat.is_lt(R, z) == True{} : Bool}, Nat.add(nlo, w), Nat.add(X, w2), Equal.sym(Nat, Nat.add(X, w2), Nat.add(nlo, w), ehi), hr)
      +hw3 = NF.w_hi(w, C.pow2(jp), hw)
      srch(g, n, k, m, hi, m2, I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, m), hi}), G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, m2), jp, X, w2, R, K, hK, hm, hhi2, hm2, hR1, hR2, hl2, hr2, Equal.sym(Bool, Nat.is_lt(1n, w2), I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, m), hi}), Equal.sym(Bool, I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, m), hi}), Nat.is_lt(1n, w2), hmore2)), hhit2, hw3, hf)
    case 1n+ +g True{} False{} 1n+ +jp:
      +q = Nat.div(w, 2n)
      +X = Nat.add(nlo, q)
      +h2w = N.lt_succ_le_succ(1n, w, Equal.sym(Bool, True{}, Nat.is_lt(1n, w), hmore))
      +hq1 = Equal.trans(Bool, Nat.is_le(1n, q), Nat.is_le(Nat.mul(1n, 2n), w), True{}, NR.le_div(1n, 1n, w), h2w)
      +hpos = pos_of(q, hq1)
      +m2 = G.imid(~WU.U64, ~I.u64_op, lo, m)
      +hm2 = imid_v(K, hK, lo, m, nlo, q, hlo, hm)
      +hmore2 = more_v(K, hK, lo, m, nlo, q, hlo, hm, hpos)
      +hhit2 = Equal.trans(Bool, G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, m2), Nat.is_le(Nat.pow(v(m2), k), v(n)), Nat.is_le(Nat.pow(Nat.add(nlo, Nat.div(q, 2n)), k), v(n)), rl_v(K, hK, n, k, m2), Equal.cong(Nat, Bool, t => Nat.is_le(Nat.pow(t, k), v(n)), v(m2), Nat.add(nlo, Nat.div(q, 2n)), hm2))
      +hr2 = NF.root_above(R, X, k, v(n), Equal.sym(Bool, False{}, Nat.is_le(Nat.pow(X, k), v(n)), hhit), hR1)
      +hw3 = NF.w_lo(w, C.pow2(jp), hw)
      srch(g, n, k, lo, m, m2, I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, lo), m}), G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, m2), jp, nlo, q, R, K, hK, hlo, hm, hm2, hR1, hR2, hl, hr2, Equal.sym(Bool, Nat.is_lt(1n, q), I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, lo), m}), Equal.sym(Bool, I.u64_is(NM.Lt{G.inc(~WU.U64, ~I.u64_op, lo), m}), Nat.is_lt(1n, q), hmore2)), hhit2, hw3, hf)

def iroot_big(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +kp: Nat) -> {v(G.iroot_k(~WU.U64, ~I.u64_op, ~I.u64_is, n, 2n+kp)) == M.iroot_k(v(n), 2n+kp) : Nat}:
  +bg = G.bit_length(~WU.U64, ~I.u64_op, ~I.u64_is, n)
  +bl = M.bit_length(v(n))
  +ebl = bit_length_k(K, hK, n)
  +hn = LW.val_lt(K, hK, n)
  +hbl = L.subst(Nat, z => {Nat.is_le(bl, z) == True{} : Bool}, K, 64n, hK, NF.bl_le_n(K, v(n), hn))
  +E2 = {1n+Nat.div(bl, 2n+kp) : Nat}
  +E = {1n+Nat.div(bg, 2n+kp) : Nat}
  +eE = Equal.cong(Nat, Nat, t => 1n+Nat.div(t, 2n+kp), bg, bl, ebl)
  +hE2 = NF.e_lt64(kp, bl, hbl)
  +hE = L.subst(Nat, z => {Nat.is_lt(z, 64n) == True{} : Bool}, E2, E, Equal.sym(Nat, E, E2, eE), hE2)
  +hi = I.u64_op(NM.Pow2{E})
  +W = C.pow2(E2)
  ehi0 = LW.ops_pow2(E, hE)
  +ehi = Equal.trans(Nat, v(hi), C.pow2(E), W, ehi0, Equal.cong(Nat, Nat, t => C.pow2(t), E, E2, eE))
  +zero = I.u64_op(NM.ZeroOp{})
  +m = G.imid(~WU.U64, ~I.u64_op, zero, hi)
  +hm = imid_v(K, hK, zero, hi, 0n, W, zero_v(), ehi)
  +hmore = ltv(I.u64_op(NM.One{}), hi, 1n, W, one_v(), ehi)
  +hhit = Equal.trans(Bool, G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, 2n+kp, m), Nat.is_le(Nat.pow(v(m), 2n+kp), v(n)), Nat.is_le(Nat.pow(Nat.div(W, 2n), 2n+kp), v(n)), rl_v(K, hK, n, 2n+kp, m), Equal.cong(Nat, Bool, t => Nat.is_le(Nat.pow(t, 2n+kp), v(n)), v(m), Nat.div(W, 2n), hm))
  +R = M.iroot_k(v(n), 2n+kp)
  +hb = Equal.trans(Bool, Nat.is_le(Nat.pow(P2.pow2t(E2), 2n+kp), v(n)), M.root_le(v(n), 2n+kp, P2.pow2t(E2)), False{}, Equal.sym(Bool, M.root_le(v(n), 2n+kp, P2.pow2t(E2)), Nat.is_le(Nat.pow(P2.pow2t(E2), 2n+kp), v(n)), RT.root_le_ok(v(n), 2n+kp, P2.pow2t(E2))), RT.hi_bound(v(n), 1n+kp))
  +hb2 = L.subst(Nat, z => {Nat.is_le(Nat.pow(z, 2n+kp), v(n)) == False{} : Bool}, P2.pow2t(E2), W, PP.same(E2), hb)
  +hR1 = RT.iroot_le(v(n), 1n+kp)
  +hr = NF.root_above(R, W, 2n+kp, v(n), hb2, hR1)
  +hf = N.le_trans(1n+E2, 64n, 140n, N.lt_succ_le_succ(E2, 64n, hE2), {==})
  srch(140n, n, 2n+kp, zero, hi, m, I.u64_is(NM.Lt{I.u64_op(NM.One{}), hi}), G.root_le(~WU.U64, ~I.u64_op, ~I.u64_is, n, 2n+kp, m), E2, 0n, W, R, K, hK, zero_v(), ehi, hm, hR1, RT.lt_succ_iroot(v(n), 1n+kp), N.zero_le(R), hr, hmore, hhit, N.le_refl(W), hf)

def iroot_agrees(+n: WU.U64, +k: Nat) -> SG.Iroot.agrees(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, n, k):
  match k:
    case 0n:
      {==}
    case 1n:
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, n, of(v(n)), as_of(n, v(n), {==}))
    case 2n+ +kp:
      Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, G.iroot_k(~WU.U64, ~I.u64_op, ~I.u64_is, n, 2n+kp), of(M.iroot_k(v(n), 2n+kp)), as_of(G.iroot_k(~WU.U64, ~I.u64_op, ~I.u64_is, n, 2n+kp), M.iroot_k(v(n), 2n+kp), iroot_big(64n, {==}, n, kp)))

# ---- comb: C(n, i + 1) = (r / g) ((n - i) / ((i + 1) / g)), g = gcd(r, i + 1) ----

def nz_of(+x: WU.U64, +n: Nat, +hx: {v(x) == n : Nat}, +h: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_eq(v(x), 0n) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(v(x), 0n), Nat.is_eq(n, 0n), False{}, Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(x), n, hx), N.is_eq_sym_false(0n, n, N.is_eq_lt(0n, n, h)))

def ndiv(+a: Nat, +b: Nat, +na: Nat, +nb: Nat, +ha: {a == na : Nat}, +hb: {b == nb : Nat}) -> {Nat.div(a, b) == Nat.div(na, nb) : Nat}:
  Equal.trans(Nat, Nat.div(a, b), Nat.div(na, b), Nat.div(na, nb), Equal.cong(Nat, Nat, t => Nat.div(t, b), a, na, ha), Equal.cong(Nat, Nat, t => Nat.div(na, t), b, nb, hb))

def quot_v(+a: WU.U64, +b: WU.U64, +na: Nat, +nb: Nat, +ha: {v(a) == na : Nat}, +hb: {v(b) == nb : Nat}, +hpos: {Nat.is_lt(0n, nb) == True{} : Bool}) -> {v(I.u64_op(NM.Quot{a, b})) == Nat.div(na, nb) : Nat}:
  Equal.trans(Nat, v(I.u64_op(NM.Quot{a, b})), Nat.div(v(a), v(b)), Nat.div(na, nb), LW.ops_quot(a, b, nz_of(b, nb, hb, hpos)), ndiv(v(a), v(b), na, nb, ha, hb))

def combsim(+f: Nat, +n: WU.U64, +i: WU.U64, +k: WU.U64, +r: WU.U64, +nn: Nat, +ni: Nat, +k0: Nat, +K: Nat, +ok: Bool, +more: Bool, +cn: Bool, +hK: {K == 64n : Nat}, +hn: {v(n) == nn : Nat}, +hi: {v(i) == ni : Nat}, +hk: {v(k) == k0 : Nat}, +h2: {Nat.is_le(Nat.double(k0), nn) == True{} : Bool}, +hle: {Nat.is_le(ni, k0) == True{} : Bool}, +hf: {Nat.is_le(1n+K, Nat.add(f, ni)) == True{} : Bool}, +hok: {C.fits(64n, S.choose(nn, ni)) == ok : Bool}, +ha: {fv(ok, v(r), S.choose(nn, ni)) == S.choose(nn, ni) : Nat}, +hmore: {more == Nat.is_lt(ni, k0) : Bool}, +hcn: {C.fits(64n, S.choose(nn, k0)) == cn : Bool}) -> {G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, f, n, i, k, (r, ok), more) == G.fits(WU.U64, Bool.not(cn), of(S.choose(nn, k0))) : Maybe<&2, WU.U64>}:
  match f ok more cn:
    case 0n True{} _ _:
      +h2i = N.le_trans(Nat.double(ni), Nat.double(k0), nn, N.double_le(ni, k0, hle), h2)
      +big = CN.cbig(K, nn, ni, N.le_trans(K, 1n+K, ni, N.le_succ(K), hf), h2i)
      Empty.absurd({G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, n, i, k, (r, True{}), more) == G.fits(WU.U64, Bool.not(cn), of(S.choose(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(S.choose(nn, ni), C.pow2(K)), False{}, Equal.sym(Bool, Nat.is_lt(S.choose(nn, ni), C.pow2(K)), True{}, fk(K, hK, S.choose(nn, ni), hok)), N.le_not_lt(S.choose(nn, ni), C.pow2(K), big))))
    case 0n False{} _ True{}:
      Empty.absurd({G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, 0n, n, i, k, (r, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.choose(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.choose(nn, k0)), False{}, Equal.sym(Bool, C.fits(64n, S.choose(nn, k0)), True{}, hcn), unfit_mono(64n, S.choose(nn, ni), S.choose(nn, k0), CN.cmono(nn, ni, k0, hle, h2), hok))))
    case 0n False{} _ False{}:
      {==}
    case 1n+g False{} _ True{}:
      Empty.absurd({G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, n, i, k, (r, False{}), more) == G.fits(WU.U64, Bool.not(True{}), of(S.choose(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.choose(nn, k0)), False{}, Equal.sym(Bool, C.fits(64n, S.choose(nn, k0)), True{}, hcn), unfit_mono(64n, S.choose(nn, ni), S.choose(nn, k0), CN.cmono(nn, ni, k0, hle, h2), hok))))
    case 1n+g False{} _ False{}:
      {==}
    case 1n+g True{} False{} True{}:
      +eik = N.le_antisym(ni, k0, hle, N.not_lt_le(ni, k0, Equal.sym(Bool, False{}, Nat.is_lt(ni, k0), hmore)))
      Equal.cong(WU.U64, Maybe<&2, WU.U64>, t => Some{t}, r, of(S.choose(nn, k0)), as_of(r, S.choose(nn, k0), Equal.trans(Nat, v(r), S.choose(nn, ni), S.choose(nn, k0), ha, Equal.cong(Nat, Nat, t => S.choose(nn, t), ni, k0, eik))))
    case 1n+g True{} False{} False{}:
      +eik = N.le_antisym(ni, k0, hle, N.not_lt_le(ni, k0, Equal.sym(Bool, False{}, Nat.is_lt(ni, k0), hmore)))
      Empty.absurd({G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, 1n+g, n, i, k, (r, True{}), False{}) == G.fits(WU.U64, Bool.not(False{}), of(S.choose(nn, k0))) : Maybe<&2, WU.U64>}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, S.choose(nn, ni)), False{}, Equal.sym(Bool, C.fits(64n, S.choose(nn, ni)), True{}, hok), Equal.trans(Bool, C.fits(64n, S.choose(nn, ni)), C.fits(64n, S.choose(nn, k0)), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, S.choose(nn, t)), ni, k0, eik), hcn))))
    case 1n+ +g True{} True{} _:
      +hlt = Equal.sym(Bool, True{}, Nat.is_lt(ni, k0), hmore)
      +hin = N.le_trans(ni, k0, nn, N.lt_le(ni, k0, hlt), N.le_trans(k0, Nat.double(k0), nn, N.double_self_le(k0), h2))
      +x = G.inc(~WU.U64, ~I.u64_op, i)
      +ex = inc_v(K, hK, i, k, ni, k0, hi, hk, hlt)
      +t = I.u64_op(NM.Sub{n, i})
      +tn = Nat.sub(nn, ni)
      +et = Equal.trans(Nat, v(t), Nat.sub(v(n), v(i)), tn, LW.ops_sub(n, i, le_v(i, n, ni, nn, hi, hn, hin)), nsub(v(n), v(i), nn, ni, hn, hi))
      +c = S.choose(nn, ni)
      +c1 = S.choose(nn, 1n+ni)
      +ce = FA.choose_succ_right(nn, ni)
      +gu = G.gcd(~WU.U64, ~I.u64_op, ~I.u64_is, r, x)
      +eg = Equal.trans(Nat, v(gu), M.gcd(v(r), v(x)), CN.gg(c, ni), gcd_val(r, x), Equal.trans(Nat, M.gcd(v(r), v(x)), M.gcd(c, v(x)), M.gcd(c, 1n+ni), Equal.cong(Nat, Nat, z => M.gcd(z, v(x)), v(r), c, ha), Equal.cong(Nat, Nat, z => M.gcd(c, z), v(x), 1n+ni, ex)))
      +au = I.u64_op(NM.Quot{r, gu})
      +ea = Equal.trans(Nat, v(au), Nat.div(c, CN.gg(c, ni)), CN.wl(c, ni), quot_v(r, gu, c, CN.gg(c, ni), ha, eg, CN.g_pos(c, ni)), CN.div_c(c, ni))
      +ju = I.u64_op(NM.Quot{x, gu})
      +ej = Equal.trans(Nat, v(ju), Nat.div(1n+ni, CN.gg(c, ni)), CN.wr(c, ni), quot_v(x, gu, 1n+ni, CN.gg(c, ni), ex, eg, CN.g_pos(c, ni)), CN.div_j(c, ni))
      +bu = I.u64_op(NM.Quot{t, ju})
      +eb = Equal.trans(Nat, v(bu), Nat.div(tn, CN.wr(c, ni)), CN.sq(c, ni, tn, c1), quot_v(t, ju, tn, CN.wr(c, ni), et, ej, CN.wr_pos(c, ni)), CN.div_t(c, ni, tn, c1, ce))
      +hpn = Equal.trans(Nat, Nat.mul(v(au), v(bu)), Nat.mul(CN.wl(c, ni), CN.sq(c, ni, tn, c1)), c1, nmul(v(au), v(bu), CN.wl(c, ni), CN.sq(c, ni, tn, c1), ea, eb), CN.prod_eq(c, ni, tn, c1, ce))
      +hf2 = L.subst(Nat, z => {Nat.is_le(1n+K, z) == True{} : Bool}, 1n+Nat.add(g, ni), Nat.add(g, 1n+ni), Equal.sym(Nat, Nat.add(g, 1n+ni), 1n+Nat.add(g, ni), NA.add_succ(g, ni)), hf)
      combsim(g, n, x, k, I.u64_op(NM.Mul{au, bu}), nn, 1n+ni, k0, K, Bool.not(I.u64_is(NM.MulOver{au, bu})), I.u64_is(NM.Lt{x, k}), cn, hK, hn, ex, hk, h2, succ_le(ni, k0, hlt), hf2, ok_mul(au, bu, c1, hpn), fv_mul(au, bu, c1, hpn, C.fits(64n, c1), {==}), ltv(x, k, 1n+ni, k0, ex, hk), hcn)

def min_le_a(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Nat.is_le(z, a) == True{} : Bool}, a, Nat.min(a, b), Equal.sym(Nat, Nat.min(a, b), a, N.min_left(a, b, hc)), N.le_refl(a))
    case False{}:
      L.subst(Nat, z => {Nat.is_le(z, a) == True{} : Bool}, b, Nat.min(a, b), Equal.sym(Nat, Nat.min(a, b), b, N.min_right(a, b, hc)), N.not_lt_le(a, b, hc))

def min_le_b(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, a, Nat.min(a, b), Equal.sym(Nat, Nat.min(a, b), a, N.min_left(a, b, hc)), N.lt_le(a, b, hc))
    case False{}:
      L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, b, Nat.min(a, b), Equal.sym(Nat, Nat.min(a, b), b, N.min_right(a, b, hc)), N.le_refl(b))

def le_add_rr(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(c, b)) == True{} : Bool}, Nat.add(c, a), Nat.add(a, c), N.add_comm(c, a), N.le_add_left(a, b, c, h))
  L.subst(Nat, z => {Nat.is_le(Nat.add(a, c), z) == True{} : Bool}, Nat.add(c, b), Nat.add(b, c), N.add_comm(c, b), h1)

def comb_top(+K: Nat, +hK: {K == 64n : Nat}, +n: WU.U64, +k: WU.U64, +big: Bool, +hbig: {I.u64_is(NM.Lt{n, k}) == big : Bool}) -> {G.comb_big(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, big) == SG.checked(~WU.U64, ~SG.u64_of, 64n, S.choose(v(n), v(k))) : Result<&2, &2, NM.NumError, WU.U64>}:
  match big:
    case True{}:
      +cz = FA.choose_eq_zero(v(n), v(k), lt_of(n, k, True{}, hbig))
      Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, Done{I.u64_op(NM.ZeroOp{})}, SG.checked(~WU.U64, ~SG.u64_of, 64n, 0n), SG.checked(~WU.U64, ~SG.u64_of, 64n, S.choose(v(n), v(k))), Equal.cong(WU.U64, Result<&2, &2, NM.NumError, WU.U64>, t => Done{t}, I.u64_op(NM.ZeroOp{}), of(0n), as_of(I.u64_op(NM.ZeroOp{}), 0n, zero_v())), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), 0n, S.choose(v(n), v(k)), Equal.sym(Nat, S.choose(v(n), v(k)), 0n, cz)))
    case False{}:
      +hkn = N.not_lt_le(v(n), v(k), lt_of(n, k, False{}, hbig))
      +s = I.u64_op(NM.Sub{n, k})
      +sn = Nat.sub(v(n), v(k))
      +es = Equal.trans(Nat, v(s), Nat.sub(v(n), v(k)), sn, LW.ops_sub(n, k, hkn), {==})
      +k0 = Nat.min(v(k), sn)
      +kk = G.min(~WU.U64, ~I.u64_op, ~I.u64_is, k, s)
      +hk0a = min_le_a(v(k), sn, Nat.is_lt(v(k), sn), {==})
      +hk0b = min_le_b(v(k), sn, Nat.is_lt(v(k), sn), {==})
      +hkK = L.subst(Nat, z => {Nat.is_lt(z, C.pow2(K)) == True{} : Bool}, v(k), v(k), {==}, LW.val_lt(K, hK, k))
      +ekk0 = min_c(k, s, I.u64_is(NM.Lt{s, k}), {==})
      +ekk1 = Equal.cong(WU.U64, Nat, t => v(t), kk, of(Nat.min(v(k), v(s))), ekk0)
      +ekk2 = Equal.cong(Nat, Nat, t => Nat.min(v(k), t), v(s), sn, es)
      +hfk = fits32(K, hK, k0, N.le_lt_trans(k0, v(k), C.pow2(K), hk0a, hkK))
      +ekk = Equal.trans(Nat, v(kk), v(of(Nat.min(v(k), v(s)))), k0, ekk1, Equal.trans(Nat, v(of(Nat.min(v(k), v(s)))), v(of(k0)), k0, Equal.cong(Nat, Nat, t => v(of(t)), Nat.min(v(k), v(s)), k0, ekk2), LW.vo(k0, hfk)))
      +hsum = N.le_trans(Nat.add(k0, k0), Nat.add(v(k), k0), v(n), le_add_rr(k0, v(k), k0, hk0a), L.subst(Nat, z => {Nat.is_le(Nat.add(v(k), k0), z) == True{} : Bool}, Nat.add(v(k), sn), v(n), N.sub_add(v(n), v(k), hkn), N.le_add_left(k0, sn, v(k), hk0b)))
      +h2 = L.subst(Nat, z => {Nat.is_le(z, v(n)) == True{} : Bool}, Nat.add(k0, k0), Nat.double(k0), Equal.sym(Nat, Nat.double(k0), Nat.add(k0, k0), NA.double_self(k0)), hsum)
      +one = I.u64_op(NM.One{})
      +zero = I.u64_op(NM.ZeroOp{})
      +c0 = FA.choose_zero_right(v(n))
      +hf0 = L.subst(Nat, z => {Nat.is_le(1n+z, 140n) == True{} : Bool}, 64n, K, Equal.sym(Nat, K, 64n, hK), {==})
      +hok = L.subst(Nat, z => {C.fits(64n, z) == True{} : Bool}, 1n, S.choose(v(n), 0n), Equal.sym(Nat, S.choose(v(n), 0n), 1n, c0), {==})
      +ha = Equal.trans(Nat, v(one), 1n, S.choose(v(n), 0n), one_v(), Equal.sym(Nat, S.choose(v(n), 0n), 1n, c0))
      +D = S.choose(v(n), k0)
      +sm = combsim(140n, n, zero, kk, one, v(n), 0n, k0, K, True{}, I.u64_is(NM.Lt{zero, kk}), C.fits(64n, D), hK, {==}, zero_v(), ekk, h2, N.zero_le(k0), hf0, hok, ha, ltv(zero, kk, 0n, k0, zero_v(), ekk), {==})
      +g = G.comb_go(~WU.U64, ~I.u64_op, ~I.u64_is, 140n, n, zero, kk, (one, True{}), I.u64_is(NM.Lt{zero, kk}))
      +em = FA.comb_min(v(n), v(k), hkn, Nat.is_lt(v(k), sn), {==})
      Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), SG.checked(~WU.U64, ~SG.u64_of, 64n, D), SG.checked(~WU.U64, ~SG.u64_of, 64n, S.choose(v(n), v(k))), Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.ok(WU.U64, g), G.ok(WU.U64, G.fits(WU.U64, Bool.not(C.fits(64n, D)), of(D))), SG.checked(~WU.U64, ~SG.u64_of, 64n, D), Equal.cong(Maybe<&2, WU.U64>, Result<&2, &2, NM.NumError, WU.U64>, t => G.ok(WU.U64, t), g, G.fits(WU.U64, Bool.not(C.fits(64n, D)), of(D)), sm), okfits(D, C.fits(64n, D))), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), D, S.choose(v(n), v(k)), em))

def comb_checked(+n: WU.U64, +k: WU.U64) -> SG.Comb.checked(~WU.U64, ~I.u64_op, ~I.u64_is, ~SG.u64_val, ~SG.u64_of, 64n, n, k):
  Equal.trans(Result<&2, &2, NM.NumError, WU.U64>, G.comb_big(~WU.U64, ~I.u64_op, ~I.u64_is, n, k, I.u64_is(NM.Lt{n, k})), SG.checked(~WU.U64, ~SG.u64_of, 64n, S.choose(v(n), v(k))), SG.checked(~WU.U64, ~SG.u64_of, 64n, M.comb(v(n), v(k))), comb_top(64n, {==}, n, k, I.u64_is(NM.Lt{n, k}), {==}), Equal.cong(Nat, Result<&2, &2, NM.NumError, WU.U64>, t => SG.checked(~WU.U64, ~SG.u64_of, 64n, t), S.choose(v(n), v(k)), M.comb(v(n), v(k)), Equal.sym(Nat, M.comb(v(n), v(k)), S.choose(v(n), v(k)), FA.comb_ok(v(n), v(k)))))
