import Base
import ./common.bend as B
import ../../src/dynamic_array.bend as DA
import ../../types/dynamic_array.bend as E

# Native benchmark driver for src/dynamic_array.bend (U32 elements, through
# the executable DA.*_at API).
#
# argv = [op, size, count, reps, seed]
#   region A = reps x (build `size` elements, then `count` operations `op`)
#   region B = reps x (build `size` elements, then ZERO operations)
# Both regions run the SAME code path and differ only in the trip count, so
# A - B is exactly `count` executions of the measured operation. benchmarks/native/dynamic_array.c
# performs the identical work.

type St is Type:
  S{rng: U32, chk: U32, arr: DA.DynArray<U32>}

def limit() -> Nat:
  24n

def init(+seed: U32) -> St:
  S{seed, 0, DA.with_limit_at(~U32, limit())}

def unit_code(x: Result<&2, &2, E.Error, Unit>) -> U32:
  match x:
    case Fail{e}:
      7
    case Done{u}:
      1

def item_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def nat_code(n: Nat) -> U32:
  U32.from_nat(n)

def fin_unit(r: U32, c: U32, p: DA.DynArray<U32> & Result<&2, &2, E.Error, Unit>) -> St:
  (a, x) = p
  S{r, B.mix(c, unit_code(x)), a}

# One finisher per operation (not a shared helper): clang inlines a def into
# its caller only while it has a single caller (see benchmarks/bend/deque.bend).
# Per-operation copies of the bounded draw (B.nat_below) for the same reason.
def below_get(v: U32, m: Nat) -> Nat:
  U32.to_nat(U32.mod(v, U32.from_nat(m)))

def below_set(v: U32, m: Nat) -> Nat:
  U32.to_nat(U32.mod(v, U32.from_nat(m)))

def below_res(v: U32, m: Nat) -> Nat:
  U32.to_nat(U32.mod(v, U32.from_nat(m)))

def fin_unit_set(r: U32, c: U32, p: DA.DynArray<U32> & Result<&2, &2, E.Error, Unit>) -> St:
  (a, x) = p
  S{r, B.mix(c, unit_code(x)), a}

def fin_unit_res(r: U32, c: U32, p: DA.DynArray<U32> & Result<&2, &2, E.Error, Unit>) -> St:
  (a, x) = p
  S{r, B.mix(c, unit_code(x)), a}

def fin_item_get(r: U32, c: U32, p: DA.DynArray<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (a, x) = p
  S{r, B.mix(c, item_code(x)), a}

# The list's length, counted with a tail loop (Base's List.length is not a
# tail recursion, which keeps a def from compiling to a flat native loop).
def len_acc(xs: List<&2, U32>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{x, t}:
      len_acc(t, 1n+n)

def fin_item(r: U32, c: U32, p: DA.DynArray<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (a, x) = p
  S{r, B.mix(c, item_code(x)), a}

def fin_nat(r: U32, c: U32, p: DA.DynArray<U32> & Nat) -> St:
  (a, n) = p
  S{r, B.mix(c, nat_code(n)), a}

def fin_list(r: U32, c: U32, p: DA.DynArray<U32> & List<&2, U32>) -> St:
  (a, xs) = p
  S{r, B.mix(c, nat_code(len_acc(xs, 0n))), a}

# ---- one step of each operation ----

def push_with(+r: U32, c: U32, a: DA.DynArray<U32>) -> St:
  fin_unit(r, c, DA.push_at(~U32, a, r))

def do_push(st: St) -> St:
  S{r, c, a} = st
  push_with(B.lcg(r), c, a)

def do_pop(st: St) -> St:
  S{r, c, a} = st
  fin_item(B.lcg(r), c, DA.pop_at(~U32, a))

def get_with(+r: U32, c: U32, a: DA.DynArray<U32>, +n: Nat) -> St:
  fin_item_get(r, c, DA.get_at(~U32, a, below_get(r, 1n+n)))

def do_get(st: St, +n: Nat) -> St:
  S{r, c, a} = st
  get_with(B.lcg(r), c, a, n)

def set_with(+r: U32, c: U32, a: DA.DynArray<U32>, +n: Nat) -> St:
  fin_unit_set(r, c, DA.set_at(~U32, a, below_set(r, 1n+n), r))

def do_set(st: St, +n: Nat) -> St:
  S{r, c, a} = st
  set_with(B.lcg(r), c, a, n)

def do_len(st: St) -> St:
  S{r, c, a} = st
  fin_nat(B.lcg(r), c, DA.length(U32, a))

def do_cap(st: St) -> St:
  S{r, c, a} = st
  fin_nat(B.lcg(r), c, DA.capacity(U32, a))

def do_to_list(st: St) -> St:
  S{r, c, a} = st
  fin_list(B.lcg(r), c, DA.to_list_at(~U32, a))

def clear_with(r: U32, c: U32, a: DA.DynArray<U32>) -> St:
  S{r, B.mix(c, 3), DA.clear_at(~U32, a)}

def do_clear(st: St) -> St:
  S{r, c, a} = st
  clear_with(B.lcg(r), c, a)

def reserve_with(+r: U32, c: U32, a: DA.DynArray<U32>, +n: Nat) -> St:
  fin_unit_res(r, c, DA.reserve_at(~U32, a, below_res(r, 1n+n)))

def do_reserve(st: St, +n: Nat) -> St:
  S{r, c, a} = st
  reserve_with(B.lcg(r), c, a, n)

def new_len(p: DA.DynArray<U32> & Nat) -> U32:
  (b, n) = p
  U32.from_nat(n)

def new_with(r: U32, c: U32, a: DA.DynArray<U32>) -> St:
  S{r, B.mix(c, new_len(DA.length(U32, DA.new_at(~U32)))), a}

def do_new(st: St) -> St:
  S{r, c, a} = st
  new_with(B.lcg(r), c, a)

# value-stream only (region B)
def null_with(+r: U32, c: U32, a: DA.DynArray<U32>) -> St:
  S{r, B.mix(c, r), a}

def do_null(st: St) -> St:
  S{r, c, a} = st
  null_with(B.lcg(r), c, a)

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_push(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_push(p, do_push(st))

def loop_pop(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pop(p, do_pop(st))

def loop_get(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_get(p, n, do_get(st, n))

def loop_set(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set(p, n, do_set(st, n))

def loop_len(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_len(p, do_len(st))

def loop_cap(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_cap(p, do_cap(st))

def loop_to_list(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_to_list(p, do_to_list(st))

def loop_clear(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_clear(p, do_clear(st))

def loop_reserve(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_reserve(p, n, do_reserve(st, n))

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

def do_pair_pop(st: St) -> St:
  do_pop(do_push(st))

def loop_pair_pop(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair_pop(p, do_pair_pop(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

# ---- dispatch ----

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_push(k, st)
    case 1:
      loop_pop(k, st)
    case 2:
      loop_get(k, n, st)
    case 3:
      loop_set(k, n, st)
    case 4:
      loop_len(k, st)
    case 5:
      loop_cap(k, st)
    case 6:
      loop_to_list(k, st)
    case 7:
      loop_clear(k, st)
    case 8:
      loop_reserve(k, n, st)
    case 9:
      loop_pair_pop(k, st)
    case _:
      loop_new(k, st)

# The drain is deliberately independent of how many elements the measured
# operation added or removed: it reads the length and then a fixed 64 slots
# chosen from the same value stream, so region A and region B pay the same
# observation cost and the difference is the measured operation alone.
def drain_loop(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, n, do_get(st, n))

def keep_chk(c: U32, p: DA.DynArray<U32> & Nat) -> U32:
  (a, n) = p
  c

def drain_end(st: St) -> U32:
  S{r, c, a} = st
  keep_chk(c, DA.length(U32, a))

def drain2(r: U32, c: U32, a: DA.DynArray<U32>, +n: Nat) -> U32:
  drain_end(drain_loop(64n, n, S{r, B.mix(c, U32.from_nat(n)), a}))

def drain_split(r: U32, c: U32, p: DA.DynArray<U32> & Nat) -> U32:
  (a, n) = p
  drain2(r, c, a, n)

def drain(st: St) -> U32:
  S{+r, c, a} = st
  drain_split(r, B.mix(c, r), DA.length(U32, a))

# Materialise the built structure before the measured loop starts, so a
# measured operation cannot be charged with work the build left pending (and
# so both regions pay exactly the same building cost).
def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

def settle_fold(r: U32, c: U32, p: DA.DynArray<U32> & List<&2, U32>) -> St:
  (a, xs) = p
  S{r, fold_vals(xs, c), a}

def settle(st: St) -> St:
  S{r, c, a} = st
  settle_fold(r, c, DA.to_list_at(~U32, a))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, size, settle(loop_push(size, init(seed))))))

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
