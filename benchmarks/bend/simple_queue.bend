import Base
import ./common.bend as B
import ../../src/containers/simple_queue.bend as QU
import ../../src/containers/queue.bend as K
import ../../src/containers/types/queue.bend as E

# Native benchmark driver for src/queue.bend (U32 elements).
# argv = [op, size, count, reps, seed]; see benchmarks/bend/common.bend and
# benchmarks/native/queue.c, which performs the identical work.

type St is Type:
  S{rng: U32, chk: U32, q: K.Queue<U32>}

def init(+seed: U32) -> St:
  S{seed, 0, QU.new(~U32)}

def item_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def fin_item(r: U32, c: U32, p: K.Queue<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (d, x) = p
  S{r, B.mix(c, item_code(x)), d}

def fin_nat(r: U32, c: U32, p: K.Queue<U32> & Nat) -> St:
  (d, n) = p
  S{r, B.mix(c, U32.from_nat(n)), d}

# The list's length, counted with a tail loop (Base's List.length is not a
# tail recursion, which keeps a def from compiling to a flat native loop).
def len_acc(xs: List<&2, U32>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{x, t}:
      len_acc(t, 1n+n)

def fin_list(r: U32, c: U32, p: K.Queue<U32> & List<&2, U32>) -> St:
  (d, xs) = p
  S{r, B.mix(c, U32.from_nat(len_acc(xs, 0n))), d}

def pb_with(+r: U32, c: U32, d: K.Queue<U32>) -> St:
  S{r, B.mix(c, 1), QU.put(~U32, d, r)}

def do_pb(st: St) -> St:
  S{r, c, d} = st
  pb_with(B.lcg(r), c, d)

def do_popf(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, QU.get(~U32, d))

def do_peek(st: St) -> St:
  S{r, c, d} = st
  fin_item(B.lcg(r), c, QU.peek(~U32, d))

def do_len(st: St) -> St:
  S{r, c, d} = st
  fin_nat(B.lcg(r), c, QU.qsize(~U32, d))

def do_to_list(st: St) -> St:
  S{r, c, d} = st
  fin_list(B.lcg(r), c, QU.to_list(~U32, d))

def new_len(p: K.Queue<U32> & Nat) -> U32:
  (d, n) = p
  U32.from_nat(n)

def new_with(r: U32, c: U32, d: K.Queue<U32>) -> St:
  S{r, B.mix(c, new_len(QU.qsize(~U32, QU.new(~U32)))), d}

def do_new(st: St) -> St:
  S{r, c, d} = st
  new_with(B.lcg(r), c, d)

def null_with(+r: U32, c: U32, d: K.Queue<U32>) -> St:
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

# Each library operation has ONE call site in this driver (see
# benchmarks/bend/deque.bend: clang inlines a step into its loop only while
# the step has a single caller). enqueue, dequeue and the restoring pair all
# run this one step; two per-loop flags select its enqueue and its dequeue.
def enq_if(+push: Bool, st: St) -> St:
  match push:
    case True{}:
      do_pb(st)
    case False{}:
      st

def deq_if(+pop: Bool, st: St) -> St:
  match pop:
    case True{}:
      do_popf(st)
    case False{}:
      st

def loop_q(k: Nat, +push: Bool, +pop: Bool, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_q(p, push, pop, deq_if(pop, enq_if(push, st)))

def loop_peek(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_peek(p, do_peek(st))

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

# ---- restoring pair ----
#
# A destructive operation cannot be measured on its own: a round can only
# remove what it built, so the measured batch is at most `size` operations
# while the round also pays for building those `size` elements, and the
# difference A - B never rises above the clock noise of the build
# (benchmarks/run.py documents the rule). The operation is therefore measured
# inside a pair that puts the element back, so the structure keeps its size
# and the batch can be made as long as needed. The reported nanoseconds are
# the PAIR's, charged to the destructive operation: this over-charges the
# Bend side by one insertion, it never flatters it, and the C reference runs
# the identical pair.

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, st: St) -> St:
  match op:
    case 0:
      loop_q(k, True{}, False{}, st)
    case 1:
      loop_q(k, False{}, True{}, st)
    case 2:
      loop_peek(k, st)
    case 3:
      loop_len(k, st)
    case 4:
      loop_new(k, st)
    case 5:
      loop_to_list(k, st)
    case 6:
      loop_q(k, True{}, True{}, st)
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
def fold_len(c: U32, p: K.Queue<U32> & Nat) -> U32:
  (d, n) = p
  B.mix(c, U32.from_nat(n))

def drain(st: St) -> U32:
  S{+r, c, d} = st
  fold_len(B.mix(c, r), QU.qsize(~U32, d))

def settle_fold(r: U32, c: U32, p: K.Queue<U32> & List<&2, U32>) -> St:
  (d, xs) = p
  S{r, fold_vals(xs, c), d}

def settle(st: St) -> St:
  S{r, c, d} = st
  settle_fold(r, c, QU.to_list(~U32, d))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, settle(loop_q(size, True{}, False{}, init(seed))))))

def reps_go(reps: Nat, +op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, kn, seed, B.mix(acc, round(op, size, k, kn, U32.add(seed, U32.from_nat(p)))))

def regions(+g: B.Args, +k: Nat, +kn: Nat) -> U32:
  reps_go(U32.to_nat(B.a_reps(g)), B.a_op(g), U32.to_nat(B.a_size(g)), k, kn, B.a_seed(g), 0)

def kof(+g: B.Args) -> Nat:
  U32.to_nat(B.a_count(g))

def run_a(+g: B.Args) -> U32:
  regions(g, Nat.add(kof(g), kof(g)), 0n)

def run_b(+g: B.Args) -> U32:
  regions(g, kof(g), 0n)

def run_c(+g: B.Args) -> U32:
  regions(g, 0n, 0n)

# Checksums go to stderr (printing them is what forces each region), the three
# elapsed millisecond counts to stdout. argv[5] picks the ORDER in which the
# three regions run: a machine that drifts (frequency scaling, thermal) makes
# whatever runs last look slower, which is a systematic bias of exactly the
# shape the A - B difference measures. The runner alternates the order over
# the samples and reports the median, so a monotone drift cancels.
def go_abc(+g: B.Args) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(g)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(g)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(g)))
    t5 : Nat <- IO.now()
    IO.print(B.times(d1, d2, Nat.sub(t5, t4)))

def go_cba(+g: B.Args) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(run_c(g)))
    t1 : Nat <- IO.now()
    d3 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(run_b(g)))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(run_a(g)))
    t5 : Nat <- IO.now()
    IO.print(B.times(Nat.sub(t5, t4), d2, d3))

def pick(+o: U32, +g: B.Args) -> IO(Unit):
  match o:
    case 0:
      go_abc(g)
    case _:
      go_cba(g)

def go(+g: B.Args) -> IO(Unit):
  pick(B.a_order(g), g)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    go(B.parse(raw))
