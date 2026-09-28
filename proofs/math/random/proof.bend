import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../src/math/random/chacha8/block.bend as B
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random.bend as SRM
import ../../../spec/math/random/rand.bend as SR
import ../../lib/logic.bend as L
import ../typed/w64add.bend as WA
import ./chacha8/stream.bend as CS
import ./chacha8/seed.bend as SEED
import ./lemire.bend as LE
import ./uint64n.bend as UN
import ./below.bend as BL
import ./shuffle.bend as SH

# Entry point: `bend proofs/math/random/proof.bend` checks every clause of
# spec/math/random.bend, under the clause's name, for every input (and every
# source, relation and element type where the clause is a template). No
# holes, no axioms.

def ChaCha8.stream(+n: Nat, +k: B.Key) -> SRM.ChaCha8.stream(n, k):
  CS.stream(n, k)

def ChaCha8.seeded(+n: Nat, +seed: List<&2, U32>) -> SRM.ChaCha8.seeded(n, seed):
  SEED.seeded(n, seed)

def Uint64n.value(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64) -> SRM.Uint64n.value(~S, ~next, s, n):
  UN.uint64n_value(~S, ~next, s, n)

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

def Uint64n.lt(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> SRM.Uint64n.lt(~S, ~next, s, n, hn):
  +vn = SW.value(n)
  +hv = Equal.trans(Bool, Nat.is_eq(vn, 0n), X.is_zero(n), False{}, Equal.sym(Bool, X.is_zero(n), Nat.is_eq(vn, 0n), WA.is_zero_value(n)), hn)
  +e = Equal.trans(Nat, SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SRM.val_pair(S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)),
    Equal.sym(Nat, BL.pfst(S, SRM.val_pair(S, R.uint64n(~S, ~next, s, n))), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), fst_val(S, R.uint64n(~S, ~next, s, n))),
    Equal.cong(Nat & S, Nat, p => BL.pfst(S, p), SRM.val_pair(S, R.uint64n(~S, ~next, s, n)), SR.below(~S, ~next, 127n, vn, s), UN.uint64n_value(~S, ~next, s, n)))
  Equal.trans(Bool, Nat.is_lt(SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), vn), Nat.is_lt(BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)), vn), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, vn), SW.value(R.fst(W.U64, S, R.uint64n(~S, ~next, s, n))), BL.pfst(S, SR.below(~S, ~next, 127n, vn, s)), e),
    BL.below_lt(~S, ~next, 127n, vn, s, nz_pos(vn, hv)))

def Lemire.unbiased(+w: Nat, +n: Nat, +k: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(w, n) == True{} : Bool}, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> SRM.Lemire.unbiased(w, n, k, hn, hw, hk):
  LE.unbiased(w, n, k, hn, hw, hk)

def Shuffle.permutation(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> SRM.Shuffle.permutation(~A, ~V, ~rel, ~S, ~next, s, xs, v):
  SH.shuffle_perm(~A, ~V, ~rel, ~S, ~next, s, xs, v)

def Perm.permutation(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +i: Nat) -> SRM.Perm.permutation(~S, ~next, s, n, i):
  SH.perm_perm(~S, ~next, s, n, i)
