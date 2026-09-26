import Base
import ../../../spec/math/generic.bend as SG
import ../../../spec/lib/common.bend as SC
import ../../../src/math/generic.bend as G
import ../../../src/math/instances.bend as I
import ../../../src/math/num.bend as NM
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/lemmas/spec/numeric.bend as S
import ../../lib/words32.bend as W32
import ../../lib/word.bend as WD

# The cheap clauses of spec/math/generic.bend proved at U32 for every input:
# Abs.identity, Min.agrees, Max.agrees, Sign.agrees and Clamp.agrees (the selections go
# through U32.is_lt, which is Nat's order on the values). The other U32
# clauses and every U64, F32 and F64 clause are stated and tested
# (docs/MATH_CONTRACTS.md).

# ---- Nat.min and Nat.max from the order ----

def min_of_ge(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, a) == False{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n bb:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.min(1n+ap, 0n) == 1n+ap : Nat}, N.zero_succ(0n, Equal.sym(Nat, 1n, 0n, Equal.cong(Bool, Nat, c => S.bit_value(c), True{}, False{}, h))))
    case 1n+ap 1n+bp:
      N.succ_cong(Nat.min(ap, bp), ap, min_of_ge(ap, bp, h))

def min_of_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n bb:
      Empty.absurd({Nat.min(0n, bb) == bb : Nat}, N.lt_zero_absurd(bb, h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      N.succ_cong(Nat.min(ap, bp), bp, min_of_lt(ap, bp, h))

def max_of_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n bb:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.max(1n+ap, 0n) == 0n : Nat}, N.lt_zero_absurd(1n+ap, h))
    case 1n+ap 1n+bp:
      N.succ_cong(Nat.max(ap, bp), bp, max_of_lt(ap, bp, h))

def max_of_ge(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.max(0n, 1n+bp) == 0n : Nat}, N.zero_succ(0n, Equal.sym(Nat, 1n, 0n, Equal.cong(Bool, Nat, c => S.bit_value(c), True{}, False{}, h))))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      N.succ_cong(Nat.max(ap, bp), ap, max_of_ge(ap, bp, h))

# ---- U32 round trip ----

# (one and k stay symbolic, so 2^32 is never expanded)
def val_lt(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {k == 32n : Nat}, +a: U32) -> {Nat.is_lt(U32.to_nat(a), SC.pow2(k)) == True{} : Bool}:
  %Equal.sym(Nat, SC.pow2(k), WD.sc(k, one), W32.pow_one(one, h1, k)) : {Nat.is_lt(U32.to_nat(a), _) == True{} : Bool}
  %Equal.sym(Nat, k, 32n, hk) : {Nat.is_lt(U32.to_nat(a), WD.sc(_, one)) == True{} : Bool}
  UD.vb(one, h1, a)

def le_k(+k: Nat, +hk: {k == 32n : Nat}) -> {Nat.is_le(k, 32n) == True{} : Bool}:
  %Equal.sym(Nat, k, 32n, hk) : {Nat.is_le(_, 32n) == True{} : Bool}
  {==}

# a U32 is the U32 of its value
def round_trip_k(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {k == 32n : Nat}, +a: U32) -> {U32.from_nat(U32.to_nat(a)) == a : U32}:
  U.injective(U32.from_nat(U32.to_nat(a)), a, U.to_nat_from_nat(U32.to_nat(a), k, le_k(k, hk), val_lt(one, h1, k, hk, a)))

def round_trip(+a: U32) -> {U32.from_nat(U32.to_nat(a)) == a : U32}:
  round_trip_k(1n, {==}, 32n, {==}, a)

# ---- the clauses ----

def abs_identity(+x: U32) -> SG.Abs.identity(~U32, ~I.u32_op, ~I.u32_is, x):
  {==}

def min_c(+a: U32, +b: U32, +c: Bool, +hc: {Nat.is_lt(U32.to_nat(b), U32.to_nat(a)) == c : Bool}) -> {G.pick(U32, c, b, a) == U32.from_nat(Nat.min(U32.to_nat(a), U32.to_nat(b))) : U32}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(b), min_of_lt(U32.to_nat(a), U32.to_nat(b), hc)) : {b == U32.from_nat(_) : U32}
      Equal.sym(U32, U32.from_nat(U32.to_nat(b)), b, round_trip(b))
    case False{}:
      %Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a), min_of_ge(U32.to_nat(a), U32.to_nat(b), hc)) : {a == U32.from_nat(_) : U32}
      Equal.sym(U32, U32.from_nat(U32.to_nat(a)), a, round_trip(a))

def min_agrees(+a: U32, +b: U32) -> SG.Min.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, a, b):
  %Equal.sym(Bool, U32.is_lt(b, a), Nat.is_lt(U32.to_nat(b), U32.to_nat(a)), U.is_lt_nat(b, a)) : {G.pick(U32, _, b, a) == U32.from_nat(Nat.min(U32.to_nat(a), U32.to_nat(b))) : U32}
  min_c(a, b, Nat.is_lt(U32.to_nat(b), U32.to_nat(a)), {==})

def max_c(+a: U32, +b: U32, +c: Bool, +hc: {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == c : Bool}) -> {G.pick(U32, c, b, a) == U32.from_nat(Nat.max(U32.to_nat(a), U32.to_nat(b))) : U32}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.max(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(b), max_of_lt(U32.to_nat(a), U32.to_nat(b), hc)) : {b == U32.from_nat(_) : U32}
      Equal.sym(U32, U32.from_nat(U32.to_nat(b)), b, round_trip(b))
    case False{}:
      %Equal.sym(Nat, Nat.max(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a), max_of_ge(U32.to_nat(a), U32.to_nat(b), hc)) : {a == U32.from_nat(_) : U32}
      Equal.sym(U32, U32.from_nat(U32.to_nat(a)), a, round_trip(a))

def max_agrees(+a: U32, +b: U32) -> SG.Max.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, a, b):
  %Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), U.is_lt_nat(a, b)) : {G.pick(U32, _, b, a) == U32.from_nat(Nat.max(U32.to_nat(a), U32.to_nat(b))) : U32}
  max_c(a, b, Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), {==})

# ---- sign: 1 above zero, else the value itself (0) ----

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  N.zero_succ(0n, Equal.sym(Nat, 1n, 0n, Equal.cong(Bool, Nat, c => S.bit_value(c), True{}, False{}, h)))

def lt_zero_false(+n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# 0 < n gives not n < 1
def pos_ge_one(+n: Nat, +h: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(n, 1n) == False{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 1n) == False{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+p:
      lt_zero_false(p)

# not 0 < n gives n < 1
def zero_lt_one(+n: Nat, +h: {Nat.is_lt(0n, n) == False{} : Bool}) -> {Nat.is_lt(n, 1n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, true_ne_false(h))

def sign_c(+x: U32, +c: Bool, +hc: {Nat.is_lt(0n, U32.to_nat(x)) == c : Bool}) -> {G.sign_above(~U32, ~I.u32_op, ~I.u32_is, x, c) == U32.from_nat(Nat.min(U32.to_nat(x), 1n)) : U32}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.min(U32.to_nat(x), 1n), 1n, N.min_right(U32.to_nat(x), 1n, pos_ge_one(U32.to_nat(x), hc))) : {1 == U32.from_nat(_) : U32}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_lt(x, 0), Nat.is_lt(U32.to_nat(x), 0n), U.is_lt_nat(x, 0)) : {G.sign_below(~U32, ~I.u32_op, ~I.u32_is, x, _) == U32.from_nat(Nat.min(U32.to_nat(x), 1n)) : U32}
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(x), 0n), False{}, lt_zero_false(U32.to_nat(x))) : {G.sign_below(~U32, ~I.u32_op, ~I.u32_is, x, _) == U32.from_nat(Nat.min(U32.to_nat(x), 1n)) : U32}
      %Equal.sym(Nat, Nat.min(U32.to_nat(x), 1n), U32.to_nat(x), N.min_left(U32.to_nat(x), 1n, zero_lt_one(U32.to_nat(x), hc))) : {x == U32.from_nat(_) : U32}
      Equal.sym(U32, U32.from_nat(U32.to_nat(x)), x, round_trip(x))

def sign_agrees(+x: U32) -> SG.Sign.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, x):
  %Equal.sym(Bool, U32.is_lt(0, x), Nat.is_lt(0n, U32.to_nat(x)), U.is_lt_nat(0, x)) : {G.sign_above(~U32, ~I.u32_op, ~I.u32_is, x, _) == U32.from_nat(Nat.min(U32.to_nat(x), 1n)) : U32}
  sign_c(x, Nat.is_lt(0n, U32.to_nat(x)), {==})

# ---- clamp: Domain when hi < lo, else min(max(x, lo), hi) ----

def max_val_c(+x: U32, +lo: U32, +c: Bool, +hc: {Nat.is_lt(U32.to_nat(x), U32.to_nat(lo)) == c : Bool}) -> {U32.to_nat(G.pick(U32, c, lo, x)) == Nat.max(U32.to_nat(x), U32.to_nat(lo)) : Nat}:
  match c:
    case True{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(x), U32.to_nat(lo)), U32.to_nat(lo), max_of_lt(U32.to_nat(x), U32.to_nat(lo), hc))
    case False{}:
      Equal.sym(Nat, Nat.max(U32.to_nat(x), U32.to_nat(lo)), U32.to_nat(x), max_of_ge(U32.to_nat(x), U32.to_nat(lo), hc))

# the value of max(x, lo) is the larger value
def max_val(+x: U32, +lo: U32) -> {U32.to_nat(G.max(~U32, ~I.u32_op, ~I.u32_is, x, lo)) == Nat.max(U32.to_nat(x), U32.to_nat(lo)) : Nat}:
  %Equal.sym(Bool, U32.is_lt(x, lo), Nat.is_lt(U32.to_nat(x), U32.to_nat(lo)), U.is_lt_nat(x, lo)) : {U32.to_nat(G.pick(U32, _, lo, x)) == Nat.max(U32.to_nat(x), U32.to_nat(lo)) : Nat}
  max_val_c(x, lo, Nat.is_lt(U32.to_nat(x), U32.to_nat(lo)), {==})

def clamp_c(+x: U32, +lo: U32, +hi: U32, +c: Bool) -> {G.clamp_ok(~U32, ~I.u32_op, ~I.u32_is, x, lo, hi, c) == SG.lift(~U32, ~SG.u32_of, M.clamp_ok(U32.to_nat(x), U32.to_nat(lo), U32.to_nat(hi), c)) : Result<&2, &2, NM.NumError, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(U32, G.min(~U32, ~I.u32_op, ~I.u32_is, G.max(~U32, ~I.u32_op, ~I.u32_is, x, lo), hi), U32.from_nat(Nat.min(U32.to_nat(G.max(~U32, ~I.u32_op, ~I.u32_is, x, lo)), U32.to_nat(hi))), min_agrees(G.max(~U32, ~I.u32_op, ~I.u32_is, x, lo), hi)) : {Done{_} == Done{U32.from_nat(Nat.min(Nat.max(U32.to_nat(x), U32.to_nat(lo)), U32.to_nat(hi)))} : Result<&2, &2, NM.NumError, U32>}
      %Equal.sym(Nat, U32.to_nat(G.max(~U32, ~I.u32_op, ~I.u32_is, x, lo)), Nat.max(U32.to_nat(x), U32.to_nat(lo)), max_val(x, lo)) : {Done{U32.from_nat(Nat.min(_, U32.to_nat(hi)))} == Done{U32.from_nat(Nat.min(Nat.max(U32.to_nat(x), U32.to_nat(lo)), U32.to_nat(hi)))} : Result<&2, &2, NM.NumError, U32>}
      {==}

def clamp_agrees(+x: U32, +lo: U32, +hi: U32) -> SG.Clamp.agrees(~U32, ~I.u32_op, ~I.u32_is, ~SG.u32_val, ~SG.u32_of, x, lo, hi):
  %Equal.sym(Bool, U32.is_lt(hi, lo), Nat.is_lt(U32.to_nat(hi), U32.to_nat(lo)), U.is_lt_nat(hi, lo)) : {G.clamp_ok(~U32, ~I.u32_op, ~I.u32_is, x, lo, hi, _) == SG.lift(~U32, ~SG.u32_of, M.clamp(U32.to_nat(x), U32.to_nat(lo), U32.to_nat(hi))) : Result<&2, &2, NM.NumError, U32>}
  clamp_c(x, lo, hi, Nat.is_lt(U32.to_nat(hi), U32.to_nat(lo)))
