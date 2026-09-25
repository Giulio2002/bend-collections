import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../../spec/lib/common.bend as SC
import ../../lib/lemmas/spec/numeric.bend as S
import ./idx.bend as IX

# The index arithmetic the heap performs is done in U32 (a unary Nat in a sift
# loop would make the loop cost the index instead of its logarithm). These are
# the bridges: every U32 operation the implementation uses equals the Nat
# operation the proofs reason about, as long as the index is representable.
#
# The implementation uses `U32.inc`, `U32.shl`, `U32.shr` and `U32.sub`
# instead of `U32.add`, because those four have a Nat meaning that can be
# stated with a bound `i < 2^k` for a VARIABLE k <= 32. A bound written as
# `i < 2^32` would make the checker expand a unary Nat of four billion
# successors.

def nat_round(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(i)) == i : Nat}:
  U.to_nat_from_nat(i, k, hk, h)

# ---- +1 is definitional ----

def inc_bridge(+j: Nat) -> {U32.inc(U32.from_nat(j)) == U32.from_nat(1n+j) : U32}:
  {==}

# ---- doubling ----

def shl_nat(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hd: {Nat.is_lt(Nat.double(i), SC.pow2(k)) == True{} : Bool}) -> {U32.to_nat(U32.shl(U32.from_nat(i))) == Nat.double(i) : Nat}:
  +ri = nat_round(i, k, hk, hi)
  %ri : {U32.to_nat(U32.shl(U32.from_nat(i))) == Nat.double(_) : Nat}
  U.shl_value(U32.from_nat(i), k, hk, L.subst(Nat, z => {Nat.is_lt(Nat.double(z), SC.pow2(k)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ri), hd))

def shl_bridge(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hd: {Nat.is_lt(Nat.double(i), SC.pow2(k)) == True{} : Bool}) -> {U32.shl(U32.from_nat(i)) == U32.from_nat(Nat.double(i)) : U32}:
  U.injective(U32.shl(U32.from_nat(i)), U32.from_nat(Nat.double(i)),
    Equal.trans(Nat, U32.to_nat(U32.shl(U32.from_nat(i))), Nat.double(i), U32.to_nat(U32.from_nat(Nat.double(i))),
      shl_nat(i, k, hk, hi, hd),
      Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.double(i))), Nat.double(i), nat_round(Nat.double(i), k, hk, hd))))

# ---- comparisons ----

def lt_bridge(+i: Nat, +j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}) -> {U32.is_lt(U32.from_nat(i), U32.from_nat(j)) == Nat.is_lt(i, j) : Bool}:
  %nat_round(i, k, hk, hi) : {U32.is_lt(U32.from_nat(i), U32.from_nat(j)) == Nat.is_lt(_, j) : Bool}
  %nat_round(j, k, hk, hj) : {U32.is_lt(U32.from_nat(i), U32.from_nat(j)) == Nat.is_lt(U32.to_nat(U32.from_nat(i)), _) : Bool}
  U.is_lt_nat(U32.from_nat(i), U32.from_nat(j))

def eq_bridge(+i: Nat, +j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}) -> {U32.is_eq(U32.from_nat(i), U32.from_nat(j)) == Nat.is_eq(i, j) : Bool}:
  %nat_round(i, k, hk, hi) : {U32.is_eq(U32.from_nat(i), U32.from_nat(j)) == Nat.is_eq(_, j) : Bool}
  %nat_round(j, k, hk, hj) : {U32.is_eq(U32.from_nat(i), U32.from_nat(j)) == Nat.is_eq(U32.to_nat(U32.from_nat(i)), _) : Bool}
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(U32.from_nat(i), U32.from_nat(j)), Nat.cmp(U32.to_nat(U32.from_nat(i)), U32.to_nat(U32.from_nat(j))), U.u32_cmp(U32.from_nat(i), U32.from_nat(j)))

# ---- subtracting one ----

def sub_le(+j: Nat) -> {Nat.is_le(Nat.sub(j, 1n), j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, N.sub_zero(k)) : {Nat.is_le(_, 1n+k) == True{} : Bool}
      N.le_succ(k)

def sub_one_nat(+j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}, +hpos: {Nat.is_le(1n, j) == True{} : Bool}) -> {U32.to_nat(U32.sub(U32.from_nat(j), 1)) == Nat.sub(j, 1n) : Nat}:
  %nat_round(j, k, hk, hj) : {U32.to_nat(U32.sub(U32.from_nat(j), 1)) == Nat.sub(_, 1n) : Nat}
  U.sub_nat(U32.from_nat(j), 1, L.subst(Nat, z => {Nat.is_le(U32.to_nat(1), z) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, nat_round(j, k, hk, hj)), hpos))

def sub_one(+j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}, +hpos: {Nat.is_le(1n, j) == True{} : Bool}) -> {U32.sub(U32.from_nat(j), 1) == U32.from_nat(Nat.sub(j, 1n)) : U32}:
  U.injective(U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.sub(j, 1n)),
    Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(j), 1)), Nat.sub(j, 1n), U32.to_nat(U32.from_nat(Nat.sub(j, 1n))),
      sub_one_nat(j, k, hk, hj, hpos),
      Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.sub(j, 1n))), Nat.sub(j, 1n), nat_round(Nat.sub(j, 1n), k, hk, N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(k), sub_le(j), hj)))))

# ---- halving ----

def half_bit(+b: Bool, +m: Nat) -> {IX.half(Nat.add(S.bit_value(b), Nat.double(m))) == m : Nat}:
  match b:
    case False{}:
      IX.half_double(m)
    case True{}:
      IX.half_succ_double(m)

def shr_nat(+y: U32) -> {U32.to_nat(U32.shr(y)) == IX.half(U32.to_nat(y)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(y), Nat.add(S.bit_value(U.low_bit(y)), Nat.double(U32.to_nat(U32.shr(y)))), U.shr_split(y)) : {U32.to_nat(U32.shr(y)) == IX.half(_) : Nat}
  Equal.sym(Nat, IX.half(Nat.add(S.bit_value(U.low_bit(y)), Nat.double(U32.to_nat(U32.shr(y))))), U32.to_nat(U32.shr(y)), half_bit(U.low_bit(y), U32.to_nat(U32.shr(y))))

def half_le_go(j: Nat, odd: Bool) -> {Nat.is_le(IX.half_go(j, odd), j) == True{} : Bool}:
  match j odd:
    case 0n _:
      {==}
    case 1n+ +p False{}:
      N.le_trans(IX.half_go(p, True{}), p, 1n+p, half_le_go(p, True{}), N.le_succ(p))
    case 1n+p True{}:
      half_le_go(p, False{})

def half_le(+j: Nat) -> {Nat.is_le(IX.half(j), j) == True{} : Bool}:
  half_le_go(j, False{})

def shr_bridge(+j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}) -> {U32.shr(U32.from_nat(j)) == U32.from_nat(IX.half(j)) : U32}:
  U.injective(U32.shr(U32.from_nat(j)), U32.from_nat(IX.half(j)),
    Equal.trans(Nat, U32.to_nat(U32.shr(U32.from_nat(j))), IX.half(j), U32.to_nat(U32.from_nat(IX.half(j))),
      Equal.trans(Nat, U32.to_nat(U32.shr(U32.from_nat(j))), IX.half(U32.to_nat(U32.from_nat(j))), IX.half(j),
        shr_nat(U32.from_nat(j)),
        Equal.cong(Nat, Nat, z => IX.half(z), U32.to_nat(U32.from_nat(j)), j, nat_round(j, k, hk, hj))),
      Equal.sym(Nat, U32.to_nat(U32.from_nat(IX.half(j))), IX.half(j), nat_round(IX.half(j), k, hk, N.le_lt_trans(IX.half(j), j, SC.pow2(k), half_le(j), hj)))))

# ---- the parent index, as the implementation computes it ----

def par_bridge(+j: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(k)) == True{} : Bool}, +hpos: {Nat.is_le(1n, j) == True{} : Bool}) -> {U32.shr(U32.sub(U32.from_nat(j), 1)) == U32.from_nat(IX.par(j)) : U32}:
  %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.sub(j, 1n)), sub_one(j, k, hk, hj, hpos)) : {U32.shr(_) == U32.from_nat(IX.par(j)) : U32}
  shr_bridge(Nat.sub(j, 1n), k, hk, N.le_lt_trans(Nat.sub(j, 1n), j, SC.pow2(k), sub_le(j), hj))
