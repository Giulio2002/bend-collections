import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/u64.bend as W
import ../../src/math/random.bend as R
import ../../src/math/random/pcg.bend as P

# BENCH_COUNT uint64 draws of math/random's PCG (Go's rand.NewPCG(1, 2));
# checksum: suite_randlib.bend (every draw's 8 LE bytes, last draw first),
# after the timed region.

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- S.env_nat("BENCH_COUNT")
    g : P.PCG = R.pcg(W.U64{1, 0}, W.U64{2, 0})
    start : Nat <- IO.now()
    st : List<&2, W.U64> & P.PCG = L.draws(~P.PCG, ~R.pcg_next, n, ([], g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_u64s(L.u64s_of(P.PCG, st), 0))
