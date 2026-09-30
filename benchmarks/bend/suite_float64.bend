import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/f64.bend as F
import ../../src/math/random.bend as R
import ../../src/math/random/chacha8.bend as C8

# BENCH_COUNT float64 draws (Go's r.Float64: 53 random bits / 2^53) on the
# ChaCha8 source of suite_chacha8_u64. Checksum: the 8 LE bytes of each
# result's binary64 bit pattern, last first, after the timed region.

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- S.env_nat("BENCH_COUNT")
    g : C8.ChaCha8 = L.chacha8()
    start : Nat <- IO.now()
    st : List<&2, F.F64> & C8.ChaCha8 = L.fdraws(~C8.ChaCha8, ~R.chacha8_next, n, ([], g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_f64s(L.f64s_of(C8.ChaCha8, st), 0))
