import Base
import ./common.bend as B
import ../../src/containers/binary_heap.bend as H
import ../../src/containers/types/binary_heap.bend as E

# Native benchmark driver for src/binary_heap.bend at the checked U32 instance.
# argv = [op, size, count, reps, seed]; benchmarks/native/binary_heap.c performs the
# identical work. Op selectors: 0 push, 1 pop, 2 peek, 3 length, 4 from_list,
# 5 to_sorted_list, 6 new, anything else = value-stream only.

type St is Type:
  S{rng: U32, chk: U32, h: H.Heap<U32>}

def init(+seed: U32) -> St:
  S{seed, 0, H.new(~U32)}

def item_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def fin_item(r: U32, c: U32, p: H.Heap<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (h, x) = p
  S{r, B.mix(c, item_code(x)), h}

def fin_nat(r: U32, c: U32, p: H.Heap<U32> & Nat) -> St:
  (h, n) = p
  S{r, B.mix(c, U32.from_nat(n)), h}

def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

def fin_list(r: U32, c: U32, p: H.Heap<U32> & List<&2, U32>) -> St:
  (h, xs) = p
  S{r, fold_vals(xs, c), h}

def push_with(+r: U32, c: U32, h: H.Heap<U32>) -> St:
  S{r, B.mix(c, 1), H.push(~U32, ~U32.cmp, h, r)}

def do_push(st: St) -> St:
  S{r, c, h} = st
  push_with(B.lcg(r), c, h)

def do_pop(st: St) -> St:
  S{r, c, h} = st
  fin_item(B.lcg(r), c, H.pop(~U32, ~U32.cmp, h))

def do_peek(st: St) -> St:
  S{r, c, h} = st
  fin_item(B.lcg(r), c, H.peek(~U32, h))

def do_len(st: St) -> St:
  S{r, c, h} = st
  fin_nat(B.lcg(r), c, H.length(~U32, h))

def do_sorted(st: St) -> St:
  S{r, c, h} = st
  fin_list(B.lcg(r), c, H.to_sorted_list(~U32, ~U32.cmp, h))

# from_list of a short run drawn from the same stream
def draw(k: Nat, +r: U32, acc: List<&2, U32>) -> U32 & List<&2, U32>:
  match k:
    case 0n:
      (r, acc)
    case 1n+p:
      draw(p, B.lcg(r), Con{B.lcg(r), acc})

def from_with(c: U32, p: U32 & List<&2, U32>) -> St:
  (r, xs) = p
  S{r, B.mix(c, 5), H.from_list(~U32, ~U32.cmp, xs)}

def drop_heap(h: H.Heap<U32>, st: St) -> St:
  H.BH{size, n, depth, cap, arr} = h
  st

def do_from(st: St) -> St:
  S{r, c, h} = st
  drop_heap(h, from_with(c, draw(8n, r, Nil{})))

def new_len(p: H.Heap<U32> & Nat) -> U32:
  (h, n) = p
  U32.from_nat(n)

def new_with(r: U32, c: U32, h: H.Heap<U32>) -> St:
  S{r, B.mix(c, new_len(H.length(~U32, H.new(~U32)))), h}

def do_new(st: St) -> St:
  S{r, c, h} = st
  new_with(B.lcg(r), c, h)

def null_with(+r: U32, c: U32, h: H.Heap<U32>) -> St:
  S{r, B.mix(c, r), h}

def do_null(st: St) -> St:
  S{r, c, h} = st
  null_with(B.lcg(r), c, h)

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

def loop_from(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_from(p, do_from(st))

def loop_sorted(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_sorted(p, do_sorted(st))

# ---- restoring pair ----
#
# A destructive operation cannot be measured on its own: a round can only
# remove what it built, so the measured batch is at most `size` operations
# while the round also pays for building those `size` elements, and the
# difference A - B never rises above the clock noise of the build
# (benchmarks/run.py documents the rule). The operation is therefore measured
# inside a pair that puts an element back, so the structure keeps its size and
# the batch can be made as long as needed. The reported nanoseconds are the
# PAIR's, charged to the destructive operation: this over-charges the Bend
# side by one insertion, it never flatters it, and the C reference runs the
# identical pair.

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

def measured(+op: U32, +k: Nat, st: St) -> St:
  match op:
    case 0:
      loop_push(k, st)
    case 1:
      loop_pop(k, st)
    case 2:
      loop_peek(k, st)
    case 3:
      loop_len(k, st)
    case 4:
      loop_from(k, st)
    case 5:
      loop_sorted(k, st)
    case 6:
      loop_new(k, st)
    case 7:
      loop_pair_pop(k, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

def settle_fold(r: U32, c: U32, p: H.Heap<U32> & List<&2, U32>) -> St:
  (h, xs) = p
  S{r, fold_vals(xs, c), h}

def settle(st: St) -> St:
  S{r, c, h} = st
  settle_fold(r, c, H.to_sorted_list(~U32, ~U32.cmp, h))

def keep_chk(c: U32, p: H.Heap<U32> & Nat) -> U32:
  (h, n) = p
  c

def drain_loop(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, do_peek(st))

def drain_end(st: St) -> U32:
  S{r, c, h} = st
  keep_chk(c, H.length(~U32, h))

def drain(st: St) -> U32:
  S{+r, c, h} = st
  drain_end(drain_loop(16n, S{r, B.mix(c, r), h}))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, settle(loop_push(size, init(seed))))))

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
