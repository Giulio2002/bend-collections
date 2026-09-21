import Base
import ../../bend/common.bend as B
import ./v_cur.bend as DQ
import ../../../types/deque.bend as E

# Native benchmark driver for src/deque.bend (U32 elements).
# argv = [op, size, count, reps, seed]; see benchmarks/bend/common.bend and
# benchmarks/native/deque.c, which performs the identical work.

type St is Type:
  S{rng: U32, chk: U32, dq: DQ.Deque<U32>}

def init(+seed: U32) -> St:
  S{seed, 0, DQ.new(~U32)}

def item_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def fin_item(r: U32, c: U32, p: DQ.Deque<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (d, x) = p
  S{r, B.mix(c, item_code(x)), d}

def fin_nat(r: U32, c: U32, p: DQ.Deque<U32> & Nat) -> St:
  (d, n) = p
  S{r, B.mix(c, U32.from_nat(n)), d}

def fin_list(r: U32, c: U32, p: DQ.Deque<U32> & List<&2, U32>) -> St:
  (d, xs) = p
  S{r, B.mix(c, U32.from_nat(List.length(&2, U32, xs))), d}

def pf_with(+r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, 1), DQ.push_front(~U32, d, r)}

def do_pf(st: St) -> St:
  S{r, c, d} = st
  pf_with(B.lcg(r), c, d)

def pb_with(+r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, 1), DQ.push_back(~U32, d, r)}

def do_pb(st: St) -> St:
  S{r, c, d} = st
  pb_with(B.lcg(r), c, d)

def do_popf(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, DQ.pop_front(~U32, d))

def do_popb(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, DQ.pop_back(~U32, d))

def do_peekf(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, DQ.peek_front(~U32, d))

def do_peekb(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, DQ.peek_back(~U32, d))

def do_len(st: St) -> St:
  S{r, c, d} = st
  fin_nat(B.lcg(r), c, DQ.length(~U32, d))

def do_to_list(st: St) -> St:
  S{r, c, d} = st
  fin_list(B.lcg(r), c, DQ.to_list(~U32, d))

def new_len(p: DQ.Deque<U32> & Nat) -> U32:
  (d, n) = p
  U32.from_nat(n)

def new_with(r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, new_len(DQ.length(~U32, DQ.new(~U32)))), d}

def do_new(st: St) -> St:
  S{r, c, d} = st
  new_with(B.lcg(r), c, d)

def null_with(+r: U32, c: U32, d: DQ.Deque<U32>) -> St:
  S{r, B.mix(c, r), d}

def do_null(st: St) -> St:
  S{r, c, d} = st
  null_with(B.lcg(r), c, d)

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_pf(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pf(p, do_pf(st))

def loop_pb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pb(p, do_pb(st))

def loop_popf(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_popf(p, do_popf(st))

def loop_popb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_popb(p, do_popb(st))

# ---- restoring pairs ----
#
# A pop cannot be measured on its own: a round can only pop what it built, so
# the measured batch is at most `size` operations while the round also pays
# for building those `size` elements, and the difference A - B never rises
# above the clock noise of the build (benchmarks/run.py documents the rule).
# The pop is therefore measured inside a pair that puts the element back, so
# the structure keeps its size and the batch can be made as long as needed.
# The reported nanoseconds are the PAIR's, charged to the pop: this
# over-charges the Bend side by one push, it never flatters it, and the C
# reference runs the identical pair.

def do_pair_popf(st: St) -> St:
  do_popf(do_pf(st))

def do_pair_popb(st: St) -> St:
  do_popb(do_pb(st))

def loop_pair_popf(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair_popf(p, do_pair_popf(st))

def loop_pair_popb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair_popb(p, do_pair_popb(st))

def loop_peekf(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_peekf(p, do_peekf(st))

def loop_peekb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_peekb(p, do_peekb(st))

def loop_len(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_len(p, do_len(st))

def loop_to_list(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_to_list(p, do_to_list(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, st: St) -> St:
  match op:
    case 9:
      loop_pair_popf(k, st)
    case 1:
      loop_pb(k, st)
    case _:
      loop_null(k, st)

# The drain folds the whole final content, so no measured operation can be
# skipped without changing the checksum.
def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

# The drain is deliberately independent of how many elements the measured
# operation added or removed, so region A and region B pay the same
# observation cost and the difference is the measured operation alone. Every
# measured operation folds its own result into the checksum inside the loop,
# and `settle` below forces the built structure before the loop starts.
def fold_len(c: U32, p: DQ.Deque<U32> & Nat) -> U32:
  (d, n) = p
  B.mix(c, U32.from_nat(n))

def drain(st: St) -> U32:
  S{+r, c, d} = st
  fold_len(B.mix(c, r), DQ.length(~U32, d))

def settle_fold(r: U32, c: U32, p: DQ.Deque<U32> & List<&2, U32>) -> St:
  (d, xs) = p
  S{r, fold_vals(xs, c), d}

def settle(st: St) -> St:
  S{r, c, d} = st
  settle_fold(r, c, DQ.to_list(~U32, d))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, settle(loop_pb(size, init(seed))))))

def reps_go(reps: Nat, +op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, kn, seed, B.mix(acc, round(op, size, k, kn, U32.add(seed, U32.from_nat(p)))))

def regions(+args: List<&2, String>, +k: Nat, +kn: Nat) -> U32:
  reps_go(U32.to_nat(B.arg(B.field(args, 3n))), B.arg(B.field(args, 0n)),
          U32.to_nat(B.arg(B.field(args, 1n))), k, kn,
          B.arg(B.field(args, 4n)), 0)

def kof(+args: List<&2, String>) -> Nat:
  U32.to_nat(B.arg(B.field(args, 2n)))

# A = 2k measured operations, B = k measured operations, C = none at all (the
# build-and-destroy control). A - B is exactly k x reps measured operations:
# the build, the settle and the destruction cancel, and -- unlike a two-region
# "operations against no operations" difference -- BOTH regions end in a state
# the operation has been applied to, so a size-changing operation can no
# longer move deallocation work out of the difference. C is reported next to
# every row: it is what one region costs with no measured operation at all,
# so a difference that is small beside its own build is visible as such.
def run_a(+args: List<&2, String>) -> U32:
  regions(args, Nat.add(kof(args), kof(args)), 0n)

def run_b(+args: List<&2, String>) -> U32:
  regions(args, kof(args), 0n)

def run_c(+args: List<&2, String>) -> U32:
  regions(args, 0n, 0n)

# Checksums go to stderr (printing them is what forces each region), the three
# elapsed millisecond counts to stdout. argv[5] picks the ORDER in which the
# three regions run: a machine that drifts (frequency scaling, thermal) makes
# whatever runs last look slower, which is a systematic bias of exactly the
# shape the A - B difference measures. The runner alternates the order over
# the samples and reports the median, so a monotone drift cancels.
def go_abc(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(args)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(args)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(args)))
    t5 : Nat <- IO.now()
    IO.print(B.times(d1, d2, Nat.sub(t5, t4)))

def go_cba(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(args)))
    t1 : Nat <- IO.now()
    d3 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(args)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(args)))
    t5 : Nat <- IO.now()
    IO.print(B.times(Nat.sub(t5, t4), d2, d3))

def pick(+o: U32, +args: List<&2, String>) -> IO(Unit):
  match o:
    case 0:
      go_abc(args)
    case _:
      go_cba(args)

def go(+args: List<&2, String>) -> IO(Unit):
  pick(B.arg(B.field(args, 5n)), args)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    go(B.shared(raw))
