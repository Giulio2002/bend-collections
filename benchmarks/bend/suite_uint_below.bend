import Base
import ./suite.bend as S
import ./suite_randlib.bend as L
import ../../src/math/u64.bend as W
import ../../src/math/random.bend as R
import ../../src/math/random/chacha8.bend as C8

# BENCH_COUNT draws of uint_below(n) (Go's r.Uint64N, Lemire) on the ChaCha8
# source of suite_chacha8_u64. BENCH_PARAM 0: n = 1000000007; 1: n = 2^63 + 1
# (almost half the draws rejected). Checksum: suite_randlib.bend (8 LE bytes
# per result, last first), after the timed region.

def bound(+p: Nat) -> W.U64:
  match p:
    case 0n:
      W.U64{1000000007, 0}
    case 1n+q:
      W.U64{1, 2147483648}

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- S.env_nat("BENCH_COUNT")
    +p : Nat <- S.env_nat("BENCH_PARAM")
    +b : W.U64 = bound(p)
    g : C8.ChaCha8 = L.chacha8()
    start : Nat <- IO.now()
    st : List<&2, W.U64> & C8.ChaCha8 = L.belows(~C8.ChaCha8, ~R.chacha8_next, n, b, ([], g))
    stop : Nat <- IO.now()
    L.report_sum(start, stop, L.fold_u64s(L.u64s_of(C8.ChaCha8, st), 0))
