import Base
import ../../bend/common.bend as B
import ../../../src/deque.bend as DQ
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

# The list's length, counted with a tail loop (Base's List.length is not a
# tail recursion, which keeps a def from compiling to a flat native loop).
def len_acc(xs: List<&2, U32>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{x, t}:
      len_acc(t, 1n+n)

def fin_list(r: U32, c: U32, p: DQ.Deque<U32> & List<&2, U32>) -> St:
  (d, xs) = p
  S{r, B.mix(c, U32.from_nat(len_acc(xs, 0n))), d}

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

# Each library operation has ONE call site in this driver: every Bend def
# compiles to one C function, and clang inlines a function into its caller
# only while it has a single caller. A push step shared by the push loop and
# the push/pop pair loop was called out of line in both (measured 2.3 -> 4.8
# ns per push). So every loop at one end runs the same step, and two
# per-loop flags select its push and its pop: push only (push_*), pop only
# (pop_* on an empty deque) or the restoring pair (pop_* on a nonempty one).
def push_front_if(+push: Bool, st: St) -> St:
  match push:
    case True{}:
      do_pf(st)
    case False{}:
      st

def push_back_if(+push: Bool, st: St) -> St:
  match push:
    case True{}:
      do_pb(st)
    case False{}:
      st

def pop_front_if(+pop: Bool, st: St) -> St:
  match pop:
    case True{}:
      do_popf(st)
    case False{}:
      st

def pop_back_if(+pop: Bool, st: St) -> St:
  match pop:
    case True{}:
      do_popb(st)
    case False{}:
      st

def loop_front(k: Nat, +push: Bool, +pop: Bool, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_front(p, push, pop, pop_front_if(pop, push_front_if(push, st)))

def loop_back(k: Nat, +push: Bool, +pop: Bool, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_back(p, push, pop, pop_back_if(pop, push_back_if(push, st)))

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
    case 0:
      loop_front(k, True{}, False{}, st)
    case 1:
      loop_back(k, True{}, False{}, st)
    case 2:
      loop_front(k, False{}, True{}, st)
    case 3:
      loop_back(k, False{}, True{}, st)
    case 4:
      loop_peekf(k, st)
    case 5:
      loop_peekb(k, st)
    case 6:
      loop_len(k, st)
    case 7:
      loop_to_list(k, st)
    case 8:
      loop_new(k, st)
    case 9:
      loop_front(k, True{}, True{}, st)
    case 10:
      loop_back(k, True{}, True{}, st)
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
  drain(loop_null(kn, measured(op, k, settle(loop_back(size, True{}, False{}, init(seed))))))

def reps_go(reps: Nat, +op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, kn, seed, B.mix(acc, round(op, size, k, kn, U32.add(seed, U32.from_nat(p)))))

type Args is Data:
  AG{op: U32, size: Nat, k: Nat, reps: Nat, seed: U32, order: U32}

def regions(+g: Args, +k: Nat, +kn: Nat) -> U32:
  match g:
    case AG{+op, +size, +kk, +reps, +seed, +order}:
      reps_go(reps, op, size, k, kn, seed, 0)

def kof(+g: Args) -> Nat:
  match g:
    case AG{+op, +size, +kk, +reps, +seed, +order}:
      kk

def run_a(+g: Args) -> U32:
  regions(g, Nat.add(kof(g), kof(g)), 0n)

def run_b(+g: Args) -> U32:
  regions(g, kof(g), 0n)

def run_c(+g: Args) -> U32:
  regions(g, 0n, 0n)

def go_abc(+g: Args) -> IO(Unit):
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

def go_cba(+g: Args) -> IO(Unit):
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

def pick_go(+o: U32, +g: Args) -> IO(Unit):
  match o:
    case 0:
      go_abc(g)
    case _:
      go_cba(g)

def pick(+g: Args) -> IO(Unit):
  match g:
    case AG{+op, +size, +kk, +reps, +seed, +order}:
      pick_go(order, g)

def parse6(a0: String, a1: String, a2: String, a3: String, a4: String, a5: String) -> Args:
  AG{B.arg(a0), U32.to_nat(B.arg(a1)), U32.to_nat(B.arg(a2)), U32.to_nat(B.arg(a3)), B.arg(a4), B.arg(a5)}

def parse(xs: List<&1, String>) -> Args:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, r}}}}}}:
      parse6(a0, a1, a2, a3, a4, a5)
    case _:
      AG{99, 0n, 0n, 0n, 0, 0}

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    pick(parse(raw))
