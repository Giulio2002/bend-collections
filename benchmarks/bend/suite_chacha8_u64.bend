import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/u64.bend as W
import ../../src/math/random.bend as R
import ../../src/math/random/chacha8.bend as C8

# BENCH_COUNT uint64 draws of math/random's ChaCha8 (Go's rand.NewChaCha8),
# seed bytes (7 * i + 1) mod 256; checksum: suite_randlib.bend (every draw's
# 8 LE bytes, last draw first), after the timed region.

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- S.env_nat("BENCH_COUNT")
    g : C8.ChaCha8 = L.chacha8()
    start : Nat <- IO.now()
    st : List<&2, W.U64> & C8.ChaCha8 = L.draws(~C8.ChaCha8, ~R.chacha8_next, n, ([], g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_u64s(L.u64s_of(C8.ChaCha8, st), 0))
