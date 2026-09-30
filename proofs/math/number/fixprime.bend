import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/fixed.bend as SF
import ../../../spec/math/number.bend as SN
import ../../../src/math/fixed.bend as F
import ../../../src/math/number.bend as NB
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ./prime.bend as PR
import ../typed/width.bend as WW
import ../typed/w64add.bend as WA
import ../typed/w64mul.bend as W64M
import ../typed/u32laws.bend as LW
import ../u64/u64.bend as P64
import ../../lib/u32alg.bend as UA
import ../../lib/u32.bend as U3

# is_prime and next_prime at U32 (spec/math/fixed.bend): is_prime is the
# proved trial division of proofs/math/number/prime.bend on the value;
# next_prime tries n + 1, n + 2, ... as U32s. A candidate is tracked by its
# position t == value + 2^32 [wrapped] (the successor of 2^32 - 1 wraps to
# 0 at position 2^32), so the loop's None means no prime in [n + 1, 2^32)
# and its Some p the least prime there (Mathlib Nat.find / Nat.exists_infinite_primes
# stated on the bounded range). 2^32 stays C.shift(32, one): never unfolded.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def is_prime(+a: U32) -> SF.IsPrime.value(a):
  PR.is_prime_value(v(a))

# ---- the successor's position ----

def zc_t(+one: Nat, +h1: {one == 1n : Nat}, +r: Nat, +x: Nat, +e: {Nat.add(r, C.shift(32n, one)) == Nat.add(x, 1n) : Nat}, +hx: {C.fits(32n, x) == True{} : Bool}) -> {SF.bn(Nat.is_eq(r, 0n)) == one : Nat}:
  match r:
    case 0n:
      Equal.sym(Nat, one, 1n, h1)
    case 1n+ +rp:
      +S = C.shift(32n, one)
      +e1 = Equal.trans(Nat, 1n+Nat.add(rp, S), Nat.add(x, 1n), 1n+x, e, N.add_comm(x, 1n))
      +e2 = N.succ_inj(Nat.add(rp, S), x, e1)
      +hl = Equal.trans(Bool, Nat.is_lt(Nat.add(rp, S), S), Nat.is_lt(x, S), True{}, Equal.cong(Nat, Bool, t => Nat.is_lt(t, S), Nat.add(rp, S), x, e2), WW.lt_one(32n, one, h1, x, hx))
      +hg = Equal.trans(Bool, Nat.is_le(S, Nat.add(rp, S)), Nat.is_le(S, Nat.add(S, rp)), True{}, Equal.cong(Nat, Bool, t => Nat.is_le(S, t), Nat.add(rp, S), Nat.add(S, rp), N.add_comm(rp, S)), N.le_add_right(S, rp))
      Empty.absurd({SF.bn(Nat.is_eq(1n+rp, 0n)) == one : Nat}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(S, Nat.add(rp, S)), False{}, Equal.sym(Bool, Nat.is_le(S, Nat.add(rp, S)), True{}, hg), N.lt_not_le(Nat.add(rp, S), S, hl))))

def zc(+one: Nat, +h1: {one == 1n : Nat}, +r: Nat, +x: Nat, +c: Bool, +e: {Nat.add(r, C.shift(32n, WD.bo(c, one))) == Nat.add(x, 1n) : Nat}, +hx: {C.fits(32n, x) == True{} : Bool}) -> {SF.bn(Nat.is_eq(r, 0n)) == WD.bo(c, one) : Nat}:
  match c:
    case True{}:
      zc_t(one, h1, r, x, e, hx)
    case False{}:
      +er = Equal.trans(Nat, r, Nat.add(r, 0n), 1n+x, Equal.sym(Nat, Nat.add(r, 0n), r, N.add_zero(r)), Equal.trans(Nat, Nat.add(r, 0n), Nat.add(x, 1n), 1n+x, e, N.add_comm(x, 1n)))
      %Equal.sym(Nat, r, 1n+x, er) : {SF.bn(Nat.is_eq(_, 0n)) == 0n : Nat}
      {==}

# the position of m + 1 is 1 + the value of m
def bn_bo(+b: Bool, +c: Bool, +one: Nat, +h1: {one == 1n : Nat}, +e: {SF.bn(b) == WD.bo(c, one) : Nat}) -> {WD.bo(b, one) == WD.bo(c, one) : Nat}:
  match b c:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({one == 0n : Nat}, N.succ_zero(0n, e))
    case False{} True{}:
      Empty.absurd({0n == one : Nat}, N.zero_succ(0n, Equal.trans(Nat, 0n, one, 1n, e, h1)))

def succ_t(+one: Nat, +h1: {one == 1n : Nat}, +m: U32) -> {Nat.add(v(U32.add(m, 1)), C.shift(32n, WD.bo(U32.is_zero(U32.add(m, 1)), one))) == 1n+v(m) : Nat}:
  +m1 = U32.add(m, 1)
  +c = P64.carry32(m, 1)
  +e0 = WA.acons_o(one, h1, m, 1)
  +z = zc(one, h1, v(m1), v(m), c, e0, LW.vb(m))
  +ez = bn_bo(U32.is_zero(m1), c, one, h1, Equal.trans(Nat, SF.bn(U32.is_zero(m1)), SF.bn(Nat.is_eq(v(m1), 0n)), WD.bo(c, one), Equal.cong(Bool, Nat, t => SF.bn(t), U32.is_zero(m1), Nat.is_eq(v(m1), 0n), LW.zero_nat(m1)), z))
  Equal.trans(Nat, Nat.add(v(m1), C.shift(32n, WD.bo(U32.is_zero(m1), one))), Nat.add(v(m1), C.shift(32n, WD.bo(c, one))), 1n+v(m), Equal.cong(Nat, Nat, t => Nat.add(v(m1), C.shift(32n, t)), WD.bo(U32.is_zero(m1), one), WD.bo(c, one), ez), Equal.trans(Nat, Nat.add(v(m1), C.shift(32n, WD.bo(c, one))), Nat.add(v(m), 1n), 1n+v(m), e0, N.add_comm(v(m), 1n)))

# an unwrapped candidate sits at its value
def at_val(+m: U32, +t: Nat, +ht: {Nat.add(v(m), C.shift(32n, 0n)) == t : Nat}) -> {v(m) == t : Nat}:
  Equal.trans(Nat, v(m), Nat.add(v(m), 0n), t, Equal.sym(Nat, Nat.add(v(m), 0n), v(m), N.add_zero(v(m))), ht)

def prime_of(+m: U32, +pr: Bool, +hpr: {NB.is_prime(v(m)) == pr : Bool}) -> {SN.prime(v(m)) == pr : Bool}:
  Equal.trans(Bool, SN.prime(v(m)), NB.is_prime(v(m)), pr, Equal.sym(Bool, NB.is_prime(v(m)), SN.prime(v(m)), PR.is_prime_value(v(m))), hpr)

# ---- found: a prime, none before it ----

def here(+n: Nat, +hp: {SN.prime(n) == True{} : Bool}) -> {Bool.and(Bool.and(Nat.is_le(n, n), SN.prime(n)), SF.no_prime(Nat.sub(n, n), n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(n, n), 0n, N.sub_self(n)) : {Bool.and(Bool.and(Nat.is_le(n, n), SN.prime(n)), SF.no_prime(_, n)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(n, n), True{}, N.le_refl(n)) : {Bool.and(Bool.and(_, SN.prime(n)), True{}) == True{} : Bool}
  %Equal.sym(Bool, SN.prime(n), True{}, hp) : {Bool.and(Bool.and(True{}, _), True{}) == True{} : Bool}
  {==}

def step_found(+t: Nat, +q: Nat, +pt: {SN.prime(t) == False{} : Bool}, +ih: {Bool.and(Bool.and(Nat.is_le(1n+t, q), SN.prime(q)), SF.no_prime(Nat.sub(q, 1n+t), 1n+t)) == True{} : Bool}) -> {Bool.and(Bool.and(Nat.is_le(t, q), SN.prime(q)), SF.no_prime(Nat.sub(q, t), t)) == True{} : Bool}:
  +a12 = L.and_left(Bool.and(Nat.is_le(1n+t, q), SN.prime(q)), SF.no_prime(Nat.sub(q, 1n+t), 1n+t), ih)
  +a1 = L.and_left(Nat.is_le(1n+t, q), SN.prime(q), a12)
  +a2 = L.and_right(Nat.is_le(1n+t, q), SN.prime(q), a12)
  +a3 = L.and_right(Bool.and(Nat.is_le(1n+t, q), SN.prime(q)), SF.no_prime(Nat.sub(q, 1n+t), 1n+t), ih)
  +le = N.le_trans(t, 1n+t, q, N.le_succ(t), a1)
  +es = PR.sub_split(q, t, N.succ_le_lt(t, q, a1))
  %Equal.sym(Nat, Nat.sub(q, t), 1n+Nat.sub(q, 1n+t), es) : {Bool.and(Bool.and(Nat.is_le(t, q), SN.prime(q)), SF.no_prime(_, t)) == True{} : Bool}
  %Equal.sym(Bool, SN.prime(t), False{}, pt) : {Bool.and(Bool.and(Nat.is_le(t, q), SN.prime(q)), Bool.and(Bool.not(_), SF.no_prime(Nat.sub(q, 1n+t), 1n+t))) == True{} : Bool}
  L.and_intro(Bool.and(Nat.is_le(t, q), SN.prime(q)), Bool.and(True{}, SF.no_prime(Nat.sub(q, 1n+t), 1n+t)), L.and_intro(Nat.is_le(t, q), SN.prime(q), le, a2), a3)

def found_go(fuel: Nat, +one: Nat, +h1: {one == 1n : Nat}, +m: U32, +wr: Bool, +hwr: {U32.is_zero(m) == wr : Bool}, +pr: Bool, +hpr: {NB.is_prime(v(m)) == pr : Bool}, +t: Nat, +ht: {Nat.add(v(m), C.shift(32n, WD.bo(wr, one))) == t : Nat}, +p: U32, +h: {F.u32_np(fuel, m, wr, pr) == Some{p} : Maybe<&2, U32>}) -> {Bool.and(Bool.and(Nat.is_le(t, v(p)), SN.prime(v(p))), SF.no_prime(Nat.sub(v(p), t), t)) == True{} : Bool}:
  match fuel wr pr:
    case 0n _ _:
      Empty.absurd({Bool.and(Bool.and(Nat.is_le(t, v(p)), SN.prime(v(p))), SF.no_prime(Nat.sub(v(p), t), t)) == True{} : Bool}, L.none_some(U32, p, h))
    case 1n+f True{} _:
      Empty.absurd({Bool.and(Bool.and(Nat.is_le(t, v(p)), SN.prime(v(p))), SF.no_prime(Nat.sub(v(p), t), t)) == True{} : Bool}, L.none_some(U32, p, h))
    case 1n+f False{} True{}:
      +ep = L.some_inj(U32, m, p, h)
      +et = at_val(m, t, ht)
      +hm = L.subst(Nat, q => {Bool.and(Bool.and(Nat.is_le(q, v(m)), SN.prime(v(m))), SF.no_prime(Nat.sub(v(m), q), q)) == True{} : Bool}, v(m), t, et, here(v(m), prime_of(m, True{}, hpr)))
      L.subst(U32, z => {Bool.and(Bool.and(Nat.is_le(t, v(z)), SN.prime(v(z))), SF.no_prime(Nat.sub(v(z), t), t)) == True{} : Bool}, m, p, ep, hm)
    case 1n+ +f False{} False{}:
      +m1 = U32.add(m, 1)
      +et = at_val(m, t, ht)
      +ht1 = Equal.trans(Nat, Nat.add(v(m1), C.shift(32n, WD.bo(U32.is_zero(m1), one))), 1n+v(m), 1n+t, succ_t(one, h1, m), Equal.cong(Nat, Nat, z => 1n+z, v(m), t, et))
      +ih = found_go(f, one, h1, m1, U32.is_zero(m1), {==}, NB.is_prime(v(m1)), {==}, 1n+t, ht1, p, h)
      +pt = Equal.trans(Bool, SN.prime(t), SN.prime(v(m)), False{}, Equal.cong(Nat, Bool, z => SN.prime(z), t, v(m), Equal.sym(Nat, v(m), t, et)), prime_of(m, False{}, hpr))
      step_found(t, v(p), pt, ih)

# is_lt(a, b) is is_le(a + 1, b)
def le_c(+a: Nat, +b: Nat, +d: Bool, +hd: {Nat.is_le(1n+a, b) == d : Bool}, +hc: {Nat.is_lt(a, b) == False{} : Bool}) -> {False{} == d : Bool}:
  match d:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, N.succ_le_lt(a, b, hd)), hc)))

def lt_iff_c(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {c == Nat.is_le(1n+a, b) : Bool}:
  match c:
    case True{}:
      Equal.sym(Bool, Nat.is_le(1n+a, b), True{}, N.lt_succ_le_succ(a, b, hc))
    case False{}:
      le_c(a, b, Nat.is_le(1n+a, b), {==}, hc)

def lt_iff(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  lt_iff_c(a, b, Nat.is_lt(a, b), {==})

def found_one(+one: Nat, +h1: {one == 1n : Nat}, +n: U32, +p: U32, +h: {F.u32_next_prime(n) == Some{p} : Maybe<&2, U32>}) -> {Bool.and(Bool.and(Nat.is_le(1n+v(n), v(p)), SN.prime(v(p))), SF.no_prime(Nat.sub(v(p), 1n+v(n)), 1n+v(n))) == True{} : Bool}:
  +m1 = U32.add(n, 1)
  found_go(Nat.add(v(U32.not(n)), 1n), one, h1, m1, U32.is_zero(m1), {==}, NB.is_prime(v(m1)), {==}, 1n+v(n), succ_t(one, h1, n), p, h)

def found(+n: U32, +p: U32, +h: {F.u32_next_prime(n) == Some{p} : Maybe<&2, U32>}) -> SF.NextPrime.found(n, p, h):
  +g = found_one(1n, {==}, n, p, h)
  %Equal.sym(Bool, Nat.is_lt(v(n), v(p)), Nat.is_le(1n+v(n), v(p)), lt_iff(v(n), v(p))) : {Bool.and(Bool.and(_, SN.prime(v(p))), SF.no_prime(Nat.sub(v(p), 1n+v(n)), 1n+v(n))) == True{} : Bool}
  g

# ---- none: no prime left below 2^32 ----

# UA.not_value with the unit kept open (n is 32 at the use)
def not_value_one(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +b: Word(n)) -> {Nat.add(1n, Nat.add(UA.uw(n, Word.not(n, b)), UA.uw(n, b))) == UA.sc(n, one) : Nat}:
  Equal.trans(Nat, Nat.add(1n, Nat.add(UA.uw(n, Word.not(n, b)), UA.uw(n, b))), UA.sc(n, 1n), UA.sc(n, one), UA.not_value(n, b), Equal.cong(Nat, Nat, z => UA.sc(n, z), 1n, one, Equal.sym(Nat, one, 1n, h1)))

def fuel_ok(+one: Nat, +h1: {one == 1n : Nat}, +n: U32) -> {Nat.is_le(C.shift(32n, one), Nat.add(1n+v(n), 1n+v(U32.not(n)))) == True{} : Bool}:
  match n:
    case U32{+w}:
      +A = UA.uw(32n, Word.not(32n, w))
      +B = UA.uw(32n, w)
      +S = C.shift(32n, one)
      +e1 = Equal.trans(Nat, S, WD.sc(32n, one), UA.sc(32n, one), W64M.shift_sc(32n, one), {==})
      +eS = Equal.trans(Nat, S, UA.sc(32n, one), Nat.add(1n, Nat.add(A, B)), e1, Equal.sym(Nat, Nat.add(1n, Nat.add(A, B)), UA.sc(32n, one), not_value_one(32n, one, h1, w)))
      +eR = Equal.trans(Nat, Nat.add(1n+B, 1n+A), 1n+Nat.add(B, 1n+A), 2n+Nat.add(A, B), {==}, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(B, 1n+A), 1n+Nat.add(A, B), Equal.trans(Nat, Nat.add(B, 1n+A), 1n+Nat.add(B, A), 1n+Nat.add(A, B), N.add_succ(B, A), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(B, A), Nat.add(A, B), N.add_comm(B, A)))))
      %Equal.sym(Nat, U32.to_nat(U32{w}), B, U3.to_nat_word(w)) : {Nat.is_le(S, Nat.add(1n+_, 1n+U32.to_nat(U32{Word.not(32n, w)}))) == True{} : Bool}
      %Equal.sym(Nat, U32.to_nat(U32{Word.not(32n, w)}), A, U3.to_nat_word(Word.not(32n, w))) : {Nat.is_le(S, Nat.add(1n+B, 1n+_)) == True{} : Bool}
      %Equal.sym(Nat, S, Nat.add(1n, Nat.add(A, B)), eS) : {Nat.is_le(_, Nat.add(1n+B, 1n+A)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(1n+B, 1n+A), 2n+Nat.add(A, B), eR) : {Nat.is_le(Nat.add(1n, Nat.add(A, B)), _) == True{} : Bool}
      N.le_succ(1n+Nat.add(A, B))

# 2^32 stays C.shift(32, one) for a symbolic one: with one == 1n the checker
# would expand the closed 2^32 in unary
def fuel_ok2(+one: Nat, +h1: {one == 1n : Nat}, +n: U32) -> {Nat.is_le(C.shift(32n, one), Nat.add(1n+v(n), Nat.add(v(U32.not(n)), 1n))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(C.shift(32n, one), Nat.add(1n+v(n), z)) == True{} : Bool}, 1n+v(U32.not(n)), Nat.add(v(U32.not(n)), 1n), Equal.sym(Nat, Nat.add(v(U32.not(n)), 1n), 1n+v(U32.not(n)), WA.plus1(v(U32.not(n)))), fuel_ok(one, h1, n))

def beyond(+one: Nat, +h1: {one == 1n : Nat}, +t: Nat, +q: Nat, +hS: {Nat.is_le(C.shift(32n, one), t) == True{} : Bool}, +hq: {Nat.is_le(t, q) == True{} : Bool}, +hqf: {C.fits(32n, q) == True{} : Bool}) -> Empty:
  L.true_false(Equal.trans(Bool, True{}, Nat.is_le(C.shift(32n, one), q), False{}, Equal.sym(Bool, Nat.is_le(C.shift(32n, one), q), True{}, N.le_trans(C.shift(32n, one), t, q, hS, hq)), N.lt_not_le(q, C.shift(32n, one), WW.lt_one(32n, one, h1, q, hqf))))

def none_go(fuel: Nat, +one: Nat, +h1: {one == 1n : Nat}, +m: U32, +wr: Bool, +hwr: {U32.is_zero(m) == wr : Bool}, +pr: Bool, +hpr: {NB.is_prime(v(m)) == pr : Bool}, +t: Nat, +ht: {Nat.add(v(m), C.shift(32n, WD.bo(wr, one))) == t : Nat}, +hf: {Nat.is_le(C.shift(32n, one), Nat.add(t, fuel)) == True{} : Bool}, +h: {F.u32_np(fuel, m, wr, pr) == None{} : Maybe<&2, U32>}, +q: Nat, +hq: {Nat.is_le(t, q) == True{} : Bool}, +hqf: {C.fits(32n, q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(t, q) == c : Bool}) -> {SN.prime(q) == False{} : Bool}:
  match fuel wr pr c:
    case 0n _ _ _:
      +hS = Equal.trans(Bool, Nat.is_le(C.shift(32n, one), t), Nat.is_le(C.shift(32n, one), Nat.add(t, 0n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(C.shift(32n, one), z), t, Nat.add(t, 0n), Equal.sym(Nat, Nat.add(t, 0n), t, N.add_zero(t))), hf)
      Empty.absurd({SN.prime(q) == False{} : Bool}, beyond(one, h1, t, q, hS, hq, hqf))
    case 1n+f True{} _ _:
      +S = C.shift(32n, one)
      +e1 = ht
      +hS = Equal.trans(Bool, Nat.is_le(S, t), Nat.is_le(S, Nat.add(S, v(m))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(S, z), t, Nat.add(S, v(m)), Equal.trans(Nat, t, Nat.add(v(m), S), Nat.add(S, v(m)), Equal.sym(Nat, Nat.add(v(m), S), t, e1), N.add_comm(v(m), S))), N.le_add_right(S, v(m)))
      Empty.absurd({SN.prime(q) == False{} : Bool}, beyond(one, h1, t, q, hS, hq, hqf))
    case 1n+f False{} True{} _:
      Empty.absurd({SN.prime(q) == False{} : Bool}, L.none_some(U32, m, Equal.sym(Maybe<&2, U32>, Some{m}, None{}, h)))
    case 1n+f False{} False{} True{}:
      +et = at_val(m, t, ht)
      +eq = N.eq_from_is_eq(t, q, hc)
      Equal.trans(Bool, SN.prime(q), SN.prime(v(m)), False{}, Equal.cong(Nat, Bool, z => SN.prime(z), q, v(m), Equal.sym(Nat, v(m), q, Equal.trans(Nat, v(m), t, q, et, eq))), prime_of(m, False{}, hpr))
    case 1n+ +f False{} False{} False{}:
      +et = at_val(m, t, ht)
      +m1 = U32.add(m, 1)
      +ht1 = Equal.trans(Nat, Nat.add(v(m1), C.shift(32n, WD.bo(U32.is_zero(m1), one))), 1n+v(m), 1n+t, succ_t(one, h1, m), Equal.cong(Nat, Nat, z => 1n+z, v(m), t, et))
      +hf1 = Equal.trans(Bool, Nat.is_le(C.shift(32n, one), Nat.add(1n+t, f)), Nat.is_le(C.shift(32n, one), Nat.add(t, 1n+f)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(C.shift(32n, one), z), Nat.add(1n+t, f), Nat.add(t, 1n+f), Equal.sym(Nat, Nat.add(t, 1n+f), 1n+Nat.add(t, f), N.add_succ(t, f))), hf)
      +hq1 = N.lt_succ_le_succ(t, q, N.lt_or_eq(t, q, hq, hc))
      none_go(f, one, h1, m1, U32.is_zero(m1), {==}, NB.is_prime(v(m1)), {==}, 1n+t, ht1, hf1, h, q, hq1, hqf, Nat.is_eq(1n+t, q), {==})

def none_one(+one: Nat, +h1: {one == 1n : Nat}, +n: U32, +h: {F.u32_next_prime(n) == None{} : Maybe<&2, U32>}, +m: Nat, +hm: {Nat.is_lt(v(n), m) == True{} : Bool}, +hf: {C.fits(32n, m) == True{} : Bool}) -> {SN.prime(m) == False{} : Bool}:
  +m1 = U32.add(n, 1)
  none_go(Nat.add(v(U32.not(n)), 1n), one, h1, m1, U32.is_zero(m1), {==}, NB.is_prime(v(m1)), {==}, 1n+v(n), succ_t(one, h1, n), fuel_ok2(one, h1, n), h, m, N.lt_succ_le_succ(v(n), m, hm), hf, Nat.is_eq(1n+v(n), m), {==})

def none(+n: U32, +h: {F.u32_next_prime(n) == None{} : Maybe<&2, U32>}, +m: Nat, +hm: {Nat.is_lt(v(n), m) == True{} : Bool}, +hf: {C.fits(32n, m) == True{} : Bool}) -> SF.NextPrime.none(n, h, m, hm, hf):
  none_one(1n, {==}, n, h, m, hm, hf)
