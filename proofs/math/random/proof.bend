import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../../../src/math/random/chacha8/block.bend as B
import ../../../spec/math/random.bend as SRM
import ./chacha8/stream.bend as CS
import ./chacha8/seed.bend as SEED
import ./lemire.bend as LE
import ./shuffle.bend as SH

# Entry point: `bend proofs/math/random/proof.bend` checks the ChaCha8 source,
# Lemire's counting theorem and the shuffle/perm permutation clauses of
# spec/math/random.bend, under the clause's name, for every input (and every
# source, relation and element type where the clause is a template). No holes,
# no axioms. The other clauses are checked by
# proofs/math/random/proof_draws.bend, proofs/math/random/proof_pcg.bend,
# proofs/math/random/proof_float.bend, so each root only re-checks the lemma
# files it needs.

def ChaCha8.stream(+n: Nat, +k: B.Key) -> SRM.ChaCha8.stream(n, k):
  CS.stream(n, k)

def ChaCha8.seeded(+n: Nat, +seed: List<&2, U32>) -> SRM.ChaCha8.seeded(n, seed):
  SEED.seeded(n, seed)

def Lemire.unbiased(+w: Nat, +n: Nat, +k: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hw: {C.fits(w, n) == True{} : Bool}, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> SRM.Lemire.unbiased(w, n, k, hn, hw, hk):
  LE.unbiased(w, n, k, hn, hw, hk)

def Shuffle.permutation(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> SRM.Shuffle.permutation(~A, ~V, ~rel, ~S, ~next, s, xs, v):
  SH.shuffle_perm(~A, ~V, ~rel, ~S, ~next, s, xs, v)

def Perm.permutation(~S: Data, ~next: S -> W.U64 & S, +s: S, +n: Nat, +i: Nat) -> SRM.Perm.permutation(~S, ~next, s, n, i):
  SH.perm_perm(~S, ~next, s, n, i)
