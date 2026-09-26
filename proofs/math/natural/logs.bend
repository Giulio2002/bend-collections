import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R
import ./roots.bend as RT

# ilog(n, b) is the exact integer logarithm: b^r <= n < b^(r + 1) for
# n >= 1, b >= 2, and Domain otherwise (Lean 4 Mathlib Mathlib/Data/Nat/Log:
# Nat.pow_log_le_self, Nat.lt_pow_succ_log_self; the reference's ilog,
# section 10).

# a <= b gives a + c <= b + c
def le_add_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), A.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), A.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  N.le_add_left(a, b, c, h)

# a < a + c for c > 0
def lt_add_pos(+a: Nat, +c: Nat, +h: {Nat.is_lt(0n, c) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(a, c)) == True{} : Bool}:
  %Equal.sym(Nat, a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, A.add_zero(a))) : {Nat.is_lt(_, Nat.add(a, c)) == True{} : Bool}
  N.lt_add_left(0n, c, a, h)

# k < b^k for b >= 2
def pow_gt(+bq: Nat, +k: Nat) -> {Nat.is_lt(k, Nat.pow(2n+bq, k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      +p = Nat.pow(2n+bq, kp)
      +q = Nat.add(p, Nat.mul(bq, p))
      +hp = N.lt_succ_le_succ(kp, p, pow_gt(bq, kp))
      +hq = N.lt_le_trans(0n, p, q, RT.pow_pos(1n+bq, kp), N.le_add_right(p, Nat.mul(bq, p)))
      N.lt_le_trans(1n+kp, Nat.add(1n+kp, q), Nat.add(p, q), lt_add_pos(1n+kp, q, hq), le_add_r(1n+kp, p, q, hp))

# the loop stops at k: b^k == p <= n < p b
def ilog_stop(+n: Nat, +bq: Nat, +k: Nat, +p: Nat, +hp: {p == Nat.pow(2n+bq, k) : Nat}, +hpn: {Nat.is_le(p, n) == True{} : Bool}, +hu: {False{} == Nat.is_le(Nat.mul(p, 2n+bq), n) : Bool}) -> {Nat.is_le(Nat.pow(2n+bq, k), n) == True{} : Bool} & {Nat.is_lt(n, Nat.pow(2n+bq, 1n+k)) == True{} : Bool}:
  +b = {2n+bq : Nat}
  +lt = N.not_le_lt(Nat.mul(p, b), n, Equal.sym(Bool, False{}, Nat.is_le(Nat.mul(p, b), n), hu))
  (Equal.trans(Bool, Nat.is_le(Nat.pow(b, k), n), Nat.is_le(p, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, n), Nat.pow(b, k), p, Equal.sym(Nat, p, Nat.pow(b, k), hp)), hpn),
   Equal.trans(Bool, Nat.is_lt(n, Nat.mul(b, Nat.pow(b, k))), Nat.is_lt(n, Nat.mul(p, b)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), Nat.mul(b, Nat.pow(b, k)), Nat.mul(p, b), Equal.trans(Nat, Nat.mul(b, Nat.pow(b, k)), Nat.mul(b, p), Nat.mul(p, b), Equal.cong(Nat, Nat, z => Nat.mul(b, z), Nat.pow(b, k), p, Equal.sym(Nat, p, Nat.pow(b, k), hp)), A.mul_comm(b, p))), lt))

# with no fuel left k == n, and p b <= n is impossible: n == k < p <= p b
def ilog_absurd(+n: Nat, +bq: Nat, +k: Nat, +p: Nat, +hp: {p == Nat.pow(2n+bq, k) : Nat}, +hu: {True{} == Nat.is_le(Nat.mul(p, 2n+bq), n) : Bool}, +hf: {k == n : Nat}) -> Empty:
  +b = {2n+bq : Nat}
  +kp = Equal.trans(Bool, Nat.is_lt(k, p), Nat.is_lt(k, Nat.pow(b, k)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(k, z), p, Nat.pow(b, k), hp), pow_gt(bq, k))
  +kb = N.lt_le_trans(k, p, Nat.mul(p, b), kp, RT.le_mul_pos(p, b, {==}))
  +kn = N.lt_le_trans(k, Nat.mul(p, b), n, kb, Equal.sym(Bool, True{}, Nat.is_le(Nat.mul(p, b), n), hu))
  N.lt_ne(k, n, kn, hf)

# the loop: p == b^k <= n, up is p b <= n, fuel + k == n
def ilog_ok(fuel: Nat, +n: Nat, +bq: Nat, +k: Nat, +p: Nat, +up: Bool, +hp: {p == Nat.pow(2n+bq, k) : Nat}, +hpn: {Nat.is_le(p, n) == True{} : Bool}, +hup: {up == Nat.is_le(p, Nat.div(n, 2n+bq)) : Bool}, +hf: {Nat.add(fuel, k) == n : Nat}) -> {Nat.is_le(Nat.pow(2n+bq, M.ilog_go(fuel, n, 2n+bq, k, p, up)), n) == True{} : Bool} & {Nat.is_lt(n, Nat.pow(2n+bq, 1n+M.ilog_go(fuel, n, 2n+bq, k, p, up))) == True{} : Bool}:
  match fuel up:
    case 0n False{}:
      ilog_stop(n, bq, k, p, hp, hpn, Equal.trans(Bool, False{}, Nat.is_le(p, Nat.div(n, 2n+bq)), Nat.is_le(Nat.mul(p, 2n+bq), n), hup, R.le_div(1n+bq, p, n)))
    case 1n+f False{}:
      ilog_stop(n, bq, k, p, hp, hpn, Equal.trans(Bool, False{}, Nat.is_le(p, Nat.div(n, 2n+bq)), Nat.is_le(Nat.mul(p, 2n+bq), n), hup, R.le_div(1n+bq, p, n)))
    case 0n True{}:
      Empty.absurd({Nat.is_le(Nat.pow(2n+bq, M.ilog_go(0n, n, 2n+bq, k, p, True{})), n) == True{} : Bool} & {Nat.is_lt(n, Nat.pow(2n+bq, 1n+M.ilog_go(0n, n, 2n+bq, k, p, True{}))) == True{} : Bool}, ilog_absurd(n, bq, k, p, hp, Equal.trans(Bool, True{}, Nat.is_le(p, Nat.div(n, 2n+bq)), Nat.is_le(Nat.mul(p, 2n+bq), n), hup, R.le_div(1n+bq, p, n)), hf))
    case 1n+ +f True{}:
      +b = {2n+bq : Nat}
      +hu = Equal.trans(Bool, True{}, Nat.is_le(p, Nat.div(n, b)), Nat.is_le(Nat.mul(p, b), n), hup, R.le_div(1n+bq, p, n))
      +pb = Nat.mul(p, b)
      ilog_ok(f, n, bq, 1n+k, pb, Nat.is_le(pb, Nat.div(n, b)), Equal.trans(Nat, pb, Nat.mul(b, p), Nat.pow(b, 1n+k), A.mul_comm(p, b), Equal.cong(Nat, Nat, z => Nat.mul(b, z), p, Nat.pow(b, k), hp)), Equal.sym(Bool, True{}, Nat.is_le(pb, n), hu), {==}, Equal.trans(Nat, Nat.add(f, 1n+k), 1n+Nat.add(f, k), n, A.add_succ(f, k), hf))

def lt_two(+bq: Nat) -> {Nat.is_lt(2n+bq, 2n) == False{} : Bool}:
  match bq:
    case 0n:
      {==}
    case 1n+q:
      {==}

# the value ilog(n, b) returns for n >= 1, b >= 2
def ilog_value(+np: Nat, +bq: Nat) -> Nat:
  M.ilog_go(1n+np, 1n+np, 2n+bq, 0n, 1n, Nat.is_le(1n, Nat.div(1n+np, 2n+bq)))

def ilog_done(+np: Nat, +bq: Nat) -> {M.ilog(1n+np, 2n+bq) == Done{ilog_value(np, bq)} : Result<&2, &2, M.MathError, Nat>}:
  %Equal.sym(Bool, Nat.is_lt(2n+bq, 2n), False{}, lt_two(bq)) : {M.ilog_ok(1n+np, 2n+bq, Bool.or(False{}, _)) == Done{ilog_value(np, bq)} : Result<&2, &2, M.MathError, Nat>}
  {==}

def ilog_bounds(+np: Nat, +bq: Nat) -> {Nat.is_le(Nat.pow(2n+bq, ilog_value(np, bq)), 1n+np) == True{} : Bool} & {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+ilog_value(np, bq))) == True{} : Bool}:
  ilog_ok(1n+np, 1n+np, bq, 0n, 1n, Nat.is_le(1n, Nat.div(1n+np, 2n+bq)), {==}, N.lt_succ_le_succ(0n, 1n+np, {==}), {==}, A.add_zero(1n+np))

# b^ilog(n, b) <= n   (Mathlib Nat.pow_log_le_self)
def fst_b(-P: Type, -Q: Type, p: P & Q) -> P:
  (a, b) = p
  a

def snd_b(-P: Type, -Q: Type, p: P & Q) -> Q:
  (a, b) = p
  b

def pow_ilog_le(+np: Nat, +bq: Nat) -> {Nat.is_le(Nat.pow(2n+bq, ilog_value(np, bq)), 1n+np) == True{} : Bool}:
  fst_b({Nat.is_le(Nat.pow(2n+bq, ilog_value(np, bq)), 1n+np) == True{} : Bool}, {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+ilog_value(np, bq))) == True{} : Bool}, ilog_bounds(np, bq))

# n < b^(ilog(n, b) + 1)   (Mathlib Nat.lt_pow_succ_log_self)
def lt_pow_succ_ilog(+np: Nat, +bq: Nat) -> {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+ilog_value(np, bq))) == True{} : Bool}:
  snd_b({Nat.is_le(Nat.pow(2n+bq, ilog_value(np, bq)), 1n+np) == True{} : Bool}, {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+ilog_value(np, bq))) == True{} : Bool}, ilog_bounds(np, bq))

def ilog_zero(+b: Nat) -> {M.ilog(0n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  {==}

def or_true(+n: Nat, +b: Nat) -> {M.ilog_ok(n, b, Bool.or(Nat.is_eq(n, 0n), True{})) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      {==}

def ilog_small_base(+n: Nat, +b: Nat, +hb: {Nat.is_lt(b, 2n) == True{} : Bool}) -> {M.ilog(n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}:
  %Equal.sym(Bool, Nat.is_lt(b, 2n), True{}, hb) : {M.ilog_ok(n, b, Bool.or(Nat.is_eq(n, 0n), _)) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}
  or_true(n, b)
