import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random.bend as SRM
import ../../../spec/math/random/rand.bend as SR
import ../../lib/logic.bend as L
import ../typed/w64add.bend as WA
import ./uint64n.bend as UN
import ./below.bend as BL

# Uint64n.lt: uint64n(n) is the specification's bounded draw
# (Uint64n.value), which is below n.

def fst_val(-S: Data, r: W.U64 & S) -> {BL.pfst(S, SRM.val_pair(S, r)) == SW.value(R.fst(W.U64, S, r)) : Nat}:
  match r:
    case Tuple{x, s}:
      {==}

def nz_pos(+v: Nat, +h: {Nat.is_eq(v, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, v) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_false(h))
    case 1n+p:
      {==}

def uint64n_lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> SRM.Uint64n.lt(~S, ~next, s, n, hn):
  +vn = SW.value(n)
  +hv = Equal.trans(Bool, Nat.is_eq(vn, 0n), X.is_zero(n), False{}, Equal.sym(Bool, X.is_zero(n), Nat.is_eq(vn, 0n), WA.is_zero_value(n)), hn)
  +e = Equal.trans(Nat, SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SRM.val_pair(S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)),
    Equal.sym(Nat, BL.pfst(S, SRM.val_pair(S, R.uint64n(~S, ~next, s, n))), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), fst_val(S, R.uint64n(~S, ~next, s, n))),
    Equal.cong(Nat & S, Nat, p => BL.pfst(S, p), SRM.val_pair(S, R.uint64n(~S, ~next, s, n)), SR.below(~S, ~next, 127n, vn, s), UN.uint64n_value(~S, ~next, s, n)))
  Equal.trans(Bool, Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), vn), Nat.is_lt(BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)), vn), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, vn), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)), e),
    BL.below_lt(~S, ~next, 127n, vn, s, nz_pos(vn, hv)))

