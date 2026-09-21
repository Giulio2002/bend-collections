import Base
import ./common.bend as B
import ../../src/balanced_search_tree.bend as BT
import ../../types/balanced_search_tree.bend as E

# Native benchmark driver for src/balanced_search_tree.bend at the checked U32
# key instance (U32.cmp) with U32 values. argv = [op, size, count, reps, seed];
# benchmarks/native/balanced_search_tree.c performs the identical work.
# Op selectors: 0 insert, 1 remove, 2 lookup, 3 contains, 4 min, 5 max,
# 6 lower_bound, 7 range, 8 to_list, 9 length, 10 new, else stream only.

type St is Data:
  S{rng: U32, chk: U32, m: BT.OrdMap<U32, U32>}

def init(+seed: U32) -> St:
  S{seed, 0, BT.new(U32, U32)}

def hi(v: U32) -> U32:
  U32.shrn(v, 16n)

def val_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def entry_code(x: Result<&2, &2, E.Error, E.Entry<U32, U32>>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{E.Entry{k, v}}:
      B.mix(k, v)

def fin_val(r: U32, c: U32, p: BT.OrdMap<U32, U32> & Result<&2, &2, E.Error, U32>) -> St:
  (m, x) = p
  S{r, B.mix(c, val_code(x)), m}

def ins_with(+r: U32, c: U32, m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  S{r, B.mix(c, 1), BT.insert(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n)), r)}

def do_ins(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  ins_with(B.lcg(r), c, m, n)

def rm_with(+r: U32, c: U32, m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  fin_val(r, c, BT.remove(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n))))

def do_rm(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  rm_with(B.lcg(r), c, m, n)

def look_with(+r: U32, c: U32, +m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  S{r, B.mix(c, val_code(BT.lookup(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n))))), m}

def do_look(st: St, +n: Nat) -> St:
  S{r, c, +m} = st
  look_with(B.lcg(r), c, m, n)

def bool_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def has_with(+r: U32, c: U32, +m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  S{r, B.mix(c, bool_bit(BT.contains(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n))))), m}

def do_has(st: St, +n: Nat) -> St:
  S{r, c, +m} = st
  has_with(B.lcg(r), c, m, n)

def do_min(st: St) -> St:
  S{r, c, +m} = st
  S{B.lcg(r), B.mix(c, entry_code(BT.min(U32, U32, m))), m}

def do_max(st: St) -> St:
  S{r, c, +m} = st
  S{B.lcg(r), B.mix(c, entry_code(BT.max(U32, U32, m))), m}

def lb_with(+r: U32, c: U32, +m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  S{r, B.mix(c, entry_code(BT.lower_bound(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n))))), m}

def do_lb(st: St, +n: Nat) -> St:
  S{r, c, +m} = st
  lb_with(B.lcg(r), c, m, n)

def fold_entries(xs: List<&2, E.Entry<U32, U32>>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{E.Entry{k, v}, t}:
      fold_entries(t, B.mix(B.mix(c, k), v))

def range_with(+r: U32, c: U32, +m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  S{r, fold_entries(BT.range(~U32, ~U32.cmp, U32, m, B.below(r, U32.from_nat(1n+n)), B.below(hi(r), U32.from_nat(1n+n))), c), m}

def do_range(st: St, +n: Nat) -> St:
  S{r, c, +m} = st
  range_with(B.lcg(r), c, m, n)

def do_to_list(st: St) -> St:
  S{r, c, +m} = st
  S{B.lcg(r), fold_entries(BT.to_list(U32, U32, m), c), m}

def do_len(st: St) -> St:
  S{r, c, +m} = st
  S{B.lcg(r), B.mix(c, U32.from_nat(BT.length(U32, U32, m))), m}

def do_new(st: St) -> St:
  S{r, c, m} = st
  S{B.lcg(r), B.mix(c, U32.from_nat(BT.length(U32, U32, BT.new(U32, U32)))), m}

def do_null(st: St) -> St:
  S{r, c, m} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), m}

# ---- restoring pair ----
#
# `remove` cannot be measured on its own: a round can only remove what it
# built, so the measured batch is at most `size` operations while the round
# also pays for building those `size` entries, and the difference A - B never
# rises above the clock noise of the build (benchmarks/run.py documents the
# rule). `remove` is therefore measured inside a pair that reinserts the SAME
# key, so the map keeps its size (the key stream is the built range, so after
# a few passes every key is present and each pair removes and reinserts a
# random existing key) and the batch can be made as long as needed. The
# reported nanoseconds are the PAIR's, charged to `remove`: this over-charges
# the Bend side by one insert, it never flatters it, and the C reference runs
# the identical pair.

def pair_rm_go(+r: U32, c: U32, +k: U32, p: BT.OrdMap<U32, U32> & Result<&2, &2, E.Error, U32>) -> St:
  (m, x) = p
  S{r, B.mix(B.mix(c, val_code(x)), 1), BT.insert(~U32, ~U32.cmp, U32, m, k, r)}

def pair_rm_with(+r: U32, c: U32, m: BT.OrdMap<U32, U32>, +n: Nat) -> St:
  +k = B.below(r, U32.from_nat(1n+n))
  pair_rm_go(r, c, k, BT.remove(~U32, ~U32.cmp, U32, m, k))

def do_pair_rm(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  pair_rm_with(B.lcg(r), c, m, n)

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_ins(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ins(p, n, do_ins(st, n))

def loop_rm(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rm(p, n, do_rm(st, n))

def loop_pair_rm(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair_rm(p, n, do_pair_rm(st, n))

def loop_look(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_look(p, n, do_look(st, n))

def loop_has(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_has(p, n, do_has(st, n))

def loop_min(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_min(p, do_min(st))

def loop_max(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_max(p, do_max(st))

def loop_lb(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_lb(p, n, do_lb(st, n))

def loop_range(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_range(p, n, do_range(st, n))

def loop_to_list(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_to_list(p, do_to_list(st))

def loop_len(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_len(p, do_len(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_ins(k, n, st)
    case 1:
      loop_rm(k, n, st)
    case 2:
      loop_look(k, n, st)
    case 3:
      loop_has(k, n, st)
    case 4:
      loop_min(k, st)
    case 5:
      loop_max(k, st)
    case 6:
      loop_lb(k, n, st)
    case 7:
      loop_range(k, n, st)
    case 8:
      loop_to_list(k, st)
    case 9:
      loop_len(k, st)
    case 10:
      loop_new(k, st)
    case 11:
      loop_pair_rm(k, n, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

# Observe the whole built map before the measured loop, without advancing the
# value stream.
def settle(st: St) -> St:
  S{r, c, +m} = st
  S{r, fold_entries(BT.to_list(U32, U32, m), c), m}

def drain(st: St) -> U32:
  S{+r, c, +m} = st
  B.mix(B.mix(B.mix(c, r), U32.from_nat(BT.length(U32, U32, m))), entry_code(BT.min(U32, U32, m)))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, size, settle(loop_ins(size, size, init(seed))))))

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
