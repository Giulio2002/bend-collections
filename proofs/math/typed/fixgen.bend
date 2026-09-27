import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/fixed.bend as F
import ../../../spec/math/fixed.bend as SF
import ../../../spec/math/generic.bend as SG
import ../../../src/math/num.bend as NM
import ../../lib/nat.bend as N
import ../../lib/arith.bend as AR
import ../natural/arith.bend as R
import ./width.bend as WW

# The shapes shared by the U32 and U64 proofs of spec/math/fixed.bend, over
# any instance value val: T -> Nat (Rust's u32/u64 families are defined the
# same way at every width: core::num's uint_impl! macro). A checked result
# is Some exactly when the exact result fits; a saturating one is the
# largest value otherwise; a wrapping difference is the exact one plus 2^w
# when a < b (Mathlib Nat.sub_add_cancel, Nat.mod_add_div).

def bnot_eq(+x: Bool, +c: Bool, +h: {x == c : Bool}) -> {Bool.not(x) == Bool.not(c) : Bool}:
  Equal.cong(Bool, Bool, t => Bool.not(t), x, c, h)

# ---- checked ----

def some_of(~T: Data, ~val: T -> Nat, +bad: Bool, +hb: {bad == False{} : Bool}, +r: T, +n: Nat, +hv: {val(r) == n : Nat}) -> {SF.mval(~T, ~val, F.opt(T, bad, r)) == Some{n} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, bad, False{}, hb) : {SF.mval(~T, ~val, F.opt(T, _, r)) == Some{n} : Maybe<&2, Nat>}
  Equal.cong(Nat, Maybe<&2, Nat>, t => Some{t}, val(r), n, hv)

def none_of(~T: Data, ~val: T -> Nat, +bad: Bool, +hb: {bad == True{} : Bool}, +r: T) -> {SF.mval(~T, ~val, F.opt(T, bad, r)) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, bad, True{}, hb) : {SF.mval(~T, ~val, F.opt(T, _, r)) == None{} : Maybe<&2, Nat>}
  {==}

# the result r is low(w, n) and bad says n does not fit: Some n exactly
# when n fits
def chk_fit(~T: Data, ~val: T -> Nat, +w: Nat, +n: Nat, +r: T, +bad: Bool, +hb: {bad == Bool.not(C.fits(w, n)) : Bool}, +hv: {val(r) == C.low(w, n) : Nat}, +ok: Bool, +hok: {C.fits(w, n) == ok : Bool}) -> {SF.mval(~T, ~val, F.opt(T, bad, r)) == SF.keep(ok, n) : Maybe<&2, Nat>}:
  match ok:
    case True{}:
      some_of(~T, ~val, bad, Equal.trans(Bool, bad, Bool.not(C.fits(w, n)), False{}, hb, bnot_eq(C.fits(w, n), True{}, hok)), r, n, Equal.trans(Nat, val(r), C.low(w, n), n, hv, WW.low_fit(w, n, hok)))
    case False{}:
      none_of(~T, ~val, bad, Equal.trans(Bool, bad, Bool.not(C.fits(w, n)), True{}, hb, bnot_eq(C.fits(w, n), False{}, hok)), r)

# ---- saturating ----

# the largest w-bit value: it fits, its successor does not
def top_ok(+w: Nat, +t: Nat, +h1: {C.fits(w, t) == True{} : Bool}, +h2: {C.fits(w, 1n+t) == False{} : Bool}) -> {Bool.and(C.fits(w, t), Bool.not(C.fits(w, 1n+t))) == True{} : Bool}:
  %Equal.sym(Bool, C.fits(w, t), True{}, h1) : {Bool.and(_, Bool.not(C.fits(w, 1n+t))) == True{} : Bool}
  %Equal.sym(Bool, C.fits(w, 1n+t), False{}, h2) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

def sat_fit(~T: Data, ~val: T -> Nat, +w: Nat, +n: Nat, +r: T, +top: T, +bad: Bool, +hb: {bad == Bool.not(C.fits(w, n)) : Bool}, +hv: {val(r) == C.low(w, n) : Nat}, +ht: {Bool.and(C.fits(w, val(top)), Bool.not(C.fits(w, 1n+val(top)))) == True{} : Bool}, +ok: Bool, +hok: {C.fits(w, n) == ok : Bool}) -> {SF.saturated(w, n, val(F.pick(T, bad, top, r)), ok) == True{} : Bool}:
  match ok:
    case True{}:
      +eb = Equal.trans(Bool, bad, Bool.not(C.fits(w, n)), False{}, hb, bnot_eq(C.fits(w, n), True{}, hok))
      %Equal.sym(Bool, bad, False{}, eb) : {SF.saturated(w, n, val(F.pick(T, _, top, r)), True{}) == True{} : Bool}
      %Equal.sym(Nat, val(r), n, Equal.trans(Nat, val(r), C.low(w, n), n, hv, WW.low_fit(w, n, hok))) : {Nat.is_eq(_, n) == True{} : Bool}
      N.is_eq_refl(n)
    case False{}:
      +eb = Equal.trans(Bool, bad, Bool.not(C.fits(w, n)), True{}, hb, bnot_eq(C.fits(w, n), False{}, hok))
      %Equal.sym(Bool, bad, True{}, eb) : {SF.saturated(w, n, val(F.pick(T, _, top, r)), False{}) == True{} : Bool}
      ht

# ---- Nat facts ----

def add_cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  +e1 = Equal.trans(Nat, Nat.add(c, a), Nat.add(a, c), Nat.add(b, c), N.add_comm(c, a), e)
  +e2 = Equal.trans(Nat, Nat.add(c, a), Nat.add(b, c), Nat.add(c, b), e1, N.add_comm(b, c))
  +e3 = Equal.cong(Nat, Nat, t => Nat.sub(t, c), Nat.add(c, a), Nat.add(c, b), e2)
  Equal.trans(Nat, a, Nat.sub(Nat.add(c, a), c), b, Equal.sym(Nat, Nat.sub(Nat.add(c, a), c), a, N.add_sub_cancel(c, a)), Equal.trans(Nat, Nat.sub(Nat.add(c, a), c), Nat.sub(Nat.add(c, b), c), b, e3, N.add_sub_cancel(c, b)))

def fits_sub(+k: Nat, +x: Nat, +y: Nat, +hx: {C.fits(k, x) == True{} : Bool}) -> {C.fits(k, Nat.sub(x, y)) == True{} : Bool}:
  WW.fits_of_lt(k, Nat.sub(x, y), N.le_lt_trans(Nat.sub(x, y), x, C.pow2(k), AR.sub_le2(x, y), WW.lt_of_fits(k, x, hx)))

# (z + s) + y == (y + z) + s
def rot3(+z: Nat, +s: Nat, +y: Nat) -> {Nat.add(Nat.add(z, s), y) == Nat.add(Nat.add(y, z), s) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(z, s), y), Nat.add(y, Nat.add(z, s)), Nat.add(Nat.add(y, z), s), N.add_comm(Nat.add(z, s), y), Equal.sym(Nat, Nat.add(Nat.add(y, z), s), Nat.add(y, Nat.add(z, s)), N.add_assoc(y, z, s)))

# d == x - y + 2^k modulo 2^k: its low part plus y is x, plus 2^k when x < y
def wsub(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +y: Nat, +d: Nat, +e: {Nat.add(d, y) == Nat.add(x, C.shift(k, one)) : Nat}, +hx: {C.fits(k, x) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(x, y) == c : Bool}) -> {Nat.add(C.low(k, d), y) == Nat.add(x, C.shift(k, SF.bn(c))) : Nat}:
  match c:
    case True{}:
      +S = C.shift(k, one)
      +g1 = N.lt_add_r2(x, y, S, hc)
      +g2 = Equal.trans(Bool, Nat.is_lt(Nat.add(d, y), Nat.add(y, S)), Nat.is_lt(Nat.add(x, S), Nat.add(y, S)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(y, S)), Nat.add(d, y), Nat.add(x, S), e), g1)
      +g3 = Equal.trans(Bool, Nat.is_lt(Nat.add(d, y), Nat.add(S, y)), Nat.is_lt(Nat.add(d, y), Nat.add(y, S)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(d, y), t), Nat.add(S, y), Nat.add(y, S), N.add_comm(S, y)), g2)
      +g4 = Equal.trans(Bool, Nat.is_lt(d, S), Nat.is_lt(Nat.add(d, y), Nat.add(S, y)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(d, y), Nat.add(S, y)), Nat.is_lt(d, S), WW.lt_cancel_r(d, S, y)), g3)
      +hf = WW.fits_one(k, one, h1, d, g4)
      %h1 : {Nat.add(C.low(k, d), y) == Nat.add(x, C.shift(k, _)) : Nat}
      %Equal.sym(Nat, C.low(k, d), d, WW.low_fit(k, d, hf)) : {Nat.add(_, y) == Nat.add(x, C.shift(k, one)) : Nat}
      e
    case False{}:
      +S = C.shift(k, one)
      +z = Nat.sub(x, y)
      +hle = N.not_lt_le(x, y, hc)
      +exz = N.sub_add(x, y, hle)
      +e1 = Equal.trans(Nat, Nat.add(Nat.add(z, S), y), Nat.add(Nat.add(y, z), S), Nat.add(x, S), rot3(z, S, y), Equal.cong(Nat, Nat, t => Nat.add(t, S), Nat.add(y, z), x, exz))
      +ed = add_cancel_r(d, Nat.add(z, S), y, Equal.trans(Nat, Nat.add(d, y), Nat.add(x, S), Nat.add(Nat.add(z, S), y), e, Equal.sym(Nat, Nat.add(Nat.add(z, S), y), Nat.add(x, S), e1)))
      +el = Equal.trans(Nat, C.low(k, d), C.low(k, Nat.add(z, S)), z, Equal.cong(Nat, Nat, t => C.low(k, t), d, Nat.add(z, S), ed), WW.low_u(k, z, one, fits_sub(k, x, y, hx)))
      %Equal.sym(Nat, C.low(k, d), z, el) : {Nat.add(_, y) == Nat.add(x, C.shift(k, 0n)) : Nat}
      %Equal.sym(Nat, C.shift(k, 0n), 0n, WW.shift_zero(k)) : {Nat.add(z, y) == Nat.add(x, _) : Nat}
      Equal.trans(Nat, Nat.add(z, y), x, Nat.add(x, 0n), Equal.trans(Nat, Nat.add(z, y), Nat.add(y, z), x, N.add_comm(z, y), exz), Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)))

# low(k, n) is n mod 2^k
def low_mod(+k: Nat, +n: Nat, +pp: Nat, +hp: {C.pow2(k) == 1n+pp : Nat}) -> {C.low(k, n) == Nat.mod(n, 1n+pp) : Nat}:
  +l = C.low(k, n)
  +q = C.high(k, n)
  +hl = Equal.trans(Bool, Nat.is_lt(l, 1n+pp), Nat.is_lt(l, C.pow2(k)), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(l, t), 1n+pp, C.pow2(k), Equal.sym(Nat, C.pow2(k), 1n+pp, hp)), WW.low_lt(k, n))
  +es = Equal.trans(Nat, C.shift(k, q), Nat.mul(q, C.shift(k, 1n)), Nat.mul(q, 1n+pp), WW.shift_mul(k, q), Equal.cong(Nat, Nat, t => Nat.mul(q, t), C.shift(k, 1n), 1n+pp, Equal.trans(Nat, C.shift(k, 1n), C.pow2(k), 1n+pp, WW.shift_one(k), hp)))
  +en = Equal.trans(Nat, n, Nat.add(l, C.shift(k, q)), Nat.add(Nat.mul(q, 1n+pp), l), WW.low_high(k, n), Equal.trans(Nat, Nat.add(l, C.shift(k, q)), Nat.add(l, Nat.mul(q, 1n+pp)), Nat.add(Nat.mul(q, 1n+pp), l), Equal.cong(Nat, Nat, t => Nat.add(l, t), C.shift(k, q), Nat.mul(q, 1n+pp), es), N.add_comm(l, Nat.mul(q, 1n+pp))))
  +em = Equal.trans(Nat, Nat.mod(n, 1n+pp), Nat.mod(Nat.add(Nat.mul(q, 1n+pp), l), 1n+pp), l, Equal.cong(Nat, Nat, t => Nat.mod(t, 1n+pp), n, Nat.add(Nat.mul(q, 1n+pp), l), en), R.mod_of(q, pp, l, hl))
  Equal.sym(Nat, Nat.mod(n, 1n+pp), l, em)

# a value below 2^k is its own low part mod 2^k
def mod_small(+k: Nat, +n: Nat, +pp: Nat, +hp: {C.pow2(k) == 1n+pp : Nat}, +h: {Nat.is_lt(n, 1n+pp) == True{} : Bool}) -> {Nat.mod(n, 1n+pp) == n : Nat}:
  R.mod_of(0n, pp, n, h)

# the low part absorbs an inner low part: (x mod 2^k + y) mod 2^k
def low_add_low(+k: Nat, +x: Nat, +y: Nat) -> {C.low(k, Nat.add(C.low(k, x), y)) == C.low(k, Nat.add(x, y)) : Nat}:
  +lx = C.low(k, x)
  +sh = C.shift(k, C.high(k, x))
  +e1 = Equal.cong(Nat, Nat, t => Nat.add(t, y), x, Nat.add(lx, sh), WW.low_high(k, x))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(lx, sh), y), Nat.add(lx, Nat.add(sh, y)), Nat.add(Nat.add(lx, y), sh), N.add_assoc(lx, sh, y), Equal.trans(Nat, Nat.add(lx, Nat.add(sh, y)), Nat.add(lx, Nat.add(y, sh)), Nat.add(Nat.add(lx, y), sh), Equal.cong(Nat, Nat, t => Nat.add(lx, t), Nat.add(sh, y), Nat.add(y, sh), N.add_comm(sh, y)), Equal.sym(Nat, Nat.add(Nat.add(lx, y), sh), Nat.add(lx, Nat.add(y, sh)), N.add_assoc(lx, y, sh))))
  +e3 = Equal.cong(Nat, Nat, t => C.low(k, t), Nat.add(x, y), Nat.add(Nat.add(lx, y), sh), Equal.trans(Nat, Nat.add(x, y), Nat.add(Nat.add(lx, sh), y), Nat.add(Nat.add(lx, y), sh), e1, e2))
  Equal.sym(Nat, C.low(k, Nat.add(x, y)), C.low(k, Nat.add(lx, y)), Equal.trans(Nat, C.low(k, Nat.add(x, y)), C.low(k, Nat.add(Nat.add(lx, y), sh)), C.low(k, Nat.add(lx, y)), e3, WW.low_add_shift(k, Nat.add(lx, y), C.high(k, x))))

# ((x + t) + 1) + y == x + S when y + t == M and 1 + M == S
def plus_one(+x: Nat, +t: Nat, +y: Nat, +M: Nat, +S: Nat, +h: {Nat.add(y, t) == M : Nat}, +hS: {1n+M == S : Nat}) -> {Nat.add(Nat.add(Nat.add(x, t), 1n), y) == Nat.add(x, S) : Nat}:
  +A = Nat.add(x, t)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(A, 1n), y), Nat.add(A, Nat.add(1n, y)), Nat.add(A, Nat.add(y, 1n)), N.add_assoc(A, 1n, y), Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(1n, y), Nat.add(y, 1n), N.add_comm(1n, y)))
  +e2 = Equal.sym(Nat, Nat.add(Nat.add(A, y), 1n), Nat.add(A, Nat.add(y, 1n)), N.add_assoc(A, y, 1n))
  +e3 = Equal.trans(Nat, Nat.add(A, y), Nat.add(x, Nat.add(t, y)), Nat.add(x, M), N.add_assoc(x, t, y), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(t, y), M, Equal.trans(Nat, Nat.add(t, y), Nat.add(y, t), M, N.add_comm(t, y), h)))
  +e4 = Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(A, y), Nat.add(x, M), e3)
  +e5 = Equal.cong(Nat, Nat, z => Nat.add(x, z), 1n+M, S, hS)
  Equal.trans(Nat, Nat.add(Nat.add(A, 1n), y), Nat.add(A, Nat.add(y, 1n)), Nat.add(x, S), e1, Equal.trans(Nat, Nat.add(A, Nat.add(y, 1n)), Nat.add(Nat.add(A, y), 1n), Nat.add(x, S), e2, Equal.trans(Nat, Nat.add(Nat.add(A, y), 1n), Nat.add(Nat.add(x, M), 1n), Nat.add(x, S), e4, Equal.trans(Nat, Nat.add(Nat.add(x, M), 1n), Nat.add(x, 1n+M), Nat.add(x, S), Equal.trans(Nat, Nat.add(Nat.add(x, M), 1n), Nat.add(x, Nat.add(M, 1n)), Nat.add(x, 1n+M), N.add_assoc(x, M, 1n), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(M, 1n), 1n+M, N.add_comm(M, 1n))), e5))))

def lt1(+n: Nat, +h: {Nat.is_lt(n, 1n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, N.lt_zero_absurd(p, h))

# and it failed exactly when n does not fit
def bad_res(~T: Data, ~of: Nat -> T, +w: Nat, +n: Nat, +r: Result<&2, &2, NM.NumError, T>, +hr: {r == SG.checked(~T, ~of, w, n) : Result<&2, &2, NM.NumError, T>}, +ok: Bool, +hok: {C.fits(w, n) == ok : Bool}) -> {F.res_bad(T, r) == Bool.not(ok) : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Result<&2, &2, NM.NumError, T>, r, SG.checked(~T, ~of, w, n), hr) : {F.res_bad(T, _) == False{} : Bool}
      %Equal.sym(Bool, C.fits(w, n), True{}, hok) : {F.res_bad(T, SG.checked_pick(~T, ~of, n, _)) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Result<&2, &2, NM.NumError, T>, r, SG.checked(~T, ~of, w, n), hr) : {F.res_bad(T, _) == True{} : Bool}
      %Equal.sym(Bool, C.fits(w, n), False{}, hok) : {F.res_bad(T, SG.checked_pick(~T, ~of, n, _)) == True{} : Bool}
      {==}
