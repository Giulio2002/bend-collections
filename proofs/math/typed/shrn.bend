import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/w64.bend as X
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/u32half.bend as UH
import ../../lib/u32alg.bend as A
import ../u64/u64div.bend as PD
import ./u32.bend as U32P
import ./width.bend as WW

# A shift right by k on a word is division by 2^k: U32.shrn (a single
# machine shift) has the value high(k, x), the same as U32.div(x, 2^k) (two
# machine divisions), so the two are the same word (Mathlib
# Nat.shiftRight_eq_div_pow). The w64 limb code uses shrn; its proofs rewrite
# it back to the division by the 2^k table.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# halving, as the word library and the spec write it
def hlf_half(+n: Nat) -> {UH.hlf(n) == C.half(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+q:
      Equal.cong(Nat, Nat, z => 1n+z, UH.hlf(q), C.half(q), hlf_half(q))

# high(p, half(n)) == half(high(p, n)): both halve p + 1 times
def high_half(+p: Nat, +n: Nat) -> {C.high(p, C.half(n)) == C.half(C.high(p, n)) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      high_half(q, C.half(n))

# the value of a shift right: high(k, x), for every k
def shrn_high(+x: U32, +k: Nat) -> {v(U32.shrn(x, k)) == C.high(k, v(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +e1 = Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), UH.hlf(v(U32.shrn(x, p))), C.half(v(U32.shrn(x, p))), UH.shr_value(U32.shrn(x, p)), hlf_half(v(U32.shrn(x, p))))
      +e2 = Equal.cong(Nat, Nat, z => C.half(z), v(U32.shrn(x, p)), C.high(p, v(x)), shrn_high(x, p))
      Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), C.half(C.high(p, v(x))), C.high(1n+p, v(x)), Equal.trans(Nat, v(U32.shr(U32.shrn(x, p))), C.half(v(U32.shrn(x, p))), C.half(C.high(p, v(x))), e1, e2), Equal.sym(Nat, C.high(1n+p, v(x)), C.half(C.high(p, v(x))), high_half(p, v(x))))

# the 2^k table is the word with bit k set
def p2w(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {X.pow2(k) == U32{WD.pw(32n, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n+j:
      Empty.absurd({X.pow2(32n+j) == U32{WD.pw(32n, 32n+j)} : U32}, N.lt_zero_absurd(j, hk))
def p2v(+k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {v(X.pow2(k)) == C.pow2(k) : Nat}:
  Equal.trans(Nat, v(X.pow2(k)), WD.sc(k, 1n), C.pow2(k), PD.pow32(k, hk, 1n, {==}, X.pow2(k), p2w(k, hk)), Equal.sym(Nat, C.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)))

def pow2_eq(+k: Nat) -> {C.pow2(k) == 1n+Nat.sub(C.pow2(k), 1n) : Nat}:
  Equal.sym(Nat, 1n+Nat.sub(C.pow2(k), 1n), C.pow2(k), N.sub_add(C.pow2(k), 1n, N.pow2_pos(k)))

def is_zero_c(+a: U32, +c: Bool, +hc: {U32.is_zero(a) == c : Bool}, +n: Nat, +hn: {v(a) == n : Nat}) -> {c == Nat.is_eq(v(a), 0n) : Bool}:
  match c:
    case True{}:
      %Equal.sym(U32, a, 0, A.eq_of(a, 0, hc)) : {True{} == Nat.is_eq(v(_), 0n) : Bool}
      {==}
    case False{}:
      match n:
        case 0n:
          +hz = L.subst(U32, z => {U32.is_zero(z) == True{} : Bool}, 0, a, Equal.sym(U32, a, 0, U.injective(a, 0, hn)), {==})
          Empty.absurd({False{} == Nat.is_eq(v(a), 0n) : Bool}, U32P.true_ne_false(Equal.trans(Bool, True{}, U32.is_zero(a), False{}, Equal.sym(Bool, U32.is_zero(a), True{}, hz), hc)))
        case 1n+ +p:
          %Equal.sym(Nat, v(a), 1n+p, hn) : {False{} == Nat.is_eq(_, 0n) : Bool}
          {==}

def zero_nat(+a: U32) -> {U32.is_zero(a) == Nat.is_eq(v(a), 0n) : Bool}:
  is_zero_c(a, U32.is_zero(a), {==}, v(a), {==})

# x / 2^k on a word is high(k, x)
def div_p2(+x: U32, +k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {v(U32.div(x, X.pow2(k))) == C.high(k, v(x)) : Nat}:
  +pp = Nat.sub(C.pow2(k), 1n)
  +ev = Equal.trans(Nat, v(X.pow2(k)), C.pow2(k), 1n+pp, p2v(k, hk), pow2_eq(k))
  +nz = Equal.trans(Bool, U32.is_zero(X.pow2(k)), Nat.is_eq(v(X.pow2(k)), 0n), False{}, zero_nat(X.pow2(k)), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), v(X.pow2(k)), 1n+pp, ev))
  Equal.trans(Nat, v(U32.div(x, X.pow2(k))), Nat.div(v(x), v(X.pow2(k))), C.high(k, v(x)), UD.div_nat(x, X.pow2(k), nz), Equal.trans(Nat, Nat.div(v(x), v(X.pow2(k))), Nat.div(v(x), 1n+pp), C.high(k, v(x)), Equal.cong(Nat, Nat, t => Nat.div(v(x), t), v(X.pow2(k)), 1n+pp, ev), Equal.sym(Nat, C.high(k, v(x)), Nat.div(v(x), 1n+pp), WW.high_div(k, v(x), pp, pow2_eq(k)))))

# U32.shrn(x, k) is U32.div(x, 2^k) for k < 32
def shrn_div(+x: U32, +k: Nat, +hk: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {U32.shrn(x, k) == U32.div(x, X.pow2(k)) : U32}:
  U.injective(U32.shrn(x, k), U32.div(x, X.pow2(k)), Equal.trans(Nat, v(U32.shrn(x, k)), C.high(k, v(x)), v(U32.div(x, X.pow2(k))), shrn_high(x, k), Equal.sym(Nat, v(U32.div(x, X.pow2(k))), C.high(k, v(x)), div_p2(x, k, hk))))

# the 16-bit split of the limb code
def shr16(+x: U32) -> {U32.shrn(x, 16n) == U32.div(x, 65536) : U32}:
  shrn_div(x, 16n, {==})
