import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../../../spec/math/w64.bend as SW
import ../../../spec/math/random.bend as SRM
import ./float.bend as FL
import ../../../spec/math/f64.bend as SF

# Entry point: `bend proofs/math/random/proof_float.bend` checks the Float64
# clauses of spec/math/random.bend, under the clause's name, for every input
# (and every source, relation and element type where the clause is a
# template). No holes, no axioms. The other clauses are checked by
# proofs/math/random/proof.bend, proofs/math/random/proof_draws.bend,
# proofs/math/random/proof_pcg.bend, so each root only re-checks the lemma
# files it needs.

def Float64.value(+x: W.U64, +n: Nat, +hn: {C.low(53n, SW.value(x)) == n : Nat}, +xv: Nat, +hx: {Nat.sub(SF.zb(), 53n) == xv : Nat}) -> SRM.Float64.value(x, n, hn, xv, hx):
  FL.value(x, n, hn, xv, hx)

def Float64.lt_one(+x: W.U64) -> SRM.Float64.lt_one(x):
  FL.lt_one(x)
