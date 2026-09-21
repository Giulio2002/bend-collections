import Base
import ./common.bend as B
import ../../src/segment_tree.bend as SG
import ../../types/segment_tree.bend as E

# Native benchmark driver for src/segment_tree.bend.
# argv = [op, size, count, reps, seed, order]; benchmarks/native/segment_tree.c
# performs the identical work on the identical flat split-point layout.
# Op selectors: 0 range_add, 1 get, 2 range_query, 3 length, 4 new,
# 5 from_list, 6 set, anything else = value-stream only.
#
# The cell arrays are linear, so every operation gives the tree back and the
# driver threads it; `drain` releases it.

type St is Type:
  S{rng: U32, chk: U32, f: SG.SegTree}

def init(+seed: U32, +size: Nat) -> St:
  S{seed, 0, SG.new(size)}

def hi(v: U32) -> U32:
  U32.shrn(v, 16n)

def unit_code(x: Result<&2, &2, E.Error, Unit>) -> U32:
  match x:
    case Fail{e}:
      7
    case Done{u}:
      1

def sum_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      v

def fin_unit(+r: U32, +c: U32, p: SG.SegTree & Result<&2, &2, E.Error, Unit>) -> St:
  (f, x) = p
  S{r, B.mix(c, unit_code(x)), f}

def fin_sum(+r: U32, +c: U32, p: SG.SegTree & Result<&2, &2, E.Error, U32>) -> St:
  (f, x) = p
  S{r, B.mix(c, sum_code(x)), f}

def fin_nat(+r: U32, +c: U32, p: SG.SegTree & Nat) -> St:
  (f, x) = p
  S{r, B.mix(c, U32.from_nat(x)), f}

def add_with(+r: U32, +c: U32, f: SG.SegTree, +n: Nat) -> St:
  fin_unit(r, c, SG.range_add(f, B.nat_below(r, 1n+n), B.nat_below(hi(r), 1n+n), r))

def do_add(st: St, +n: Nat) -> St:
  S{r, c, f} = st
  add_with(B.lcg(r), c, f, n)

def set_with(+r: U32, +c: U32, f: SG.SegTree, +n: Nat) -> St:
  fin_unit(r, c, SG.set(f, B.nat_below(r, 1n+n), r))

def do_set(st: St, +n: Nat) -> St:
  S{r, c, f} = st
  set_with(B.lcg(r), c, f, n)

def get_with(+r: U32, +c: U32, f: SG.SegTree, +n: Nat) -> St:
  fin_sum(r, c, SG.get(f, B.nat_below(r, 1n+n)))

def do_prefix(st: St, +n: Nat) -> St:
  S{r, c, f} = st
  get_with(B.lcg(r), c, f, n)

def range_with(+r: U32, +c: U32, f: SG.SegTree, +n: Nat) -> St:
  fin_sum(r, c, SG.range_query(f, B.nat_below(r, 1n+n), B.nat_below(hi(r), 1n+n)))

def do_range(st: St, +n: Nat) -> St:
  S{r, c, f} = st
  range_with(B.lcg(r), c, f, n)

def do_len(st: St) -> St:
  S{r, c, f} = st
  fin_nat(B.lcg(r), c, SG.length(f))

def drop_new_go(+r: U32, +c: U32, f: SG.SegTree, z: Unit) -> St:
  match z:
    case Unit{}:
      S{r, c, f}

def drop_new(+r: U32, +c: U32, f: SG.SegTree, p: SG.SegTree & Nat) -> St:
  (f2, x) = p
  drop_new_go(r, B.mix(c, U32.from_nat(x)), f, SG.dispose(f2))

def do_new(st: St) -> St:
  S{r, c, f} = st
  drop_new(B.lcg(r), c, f, SG.length(SG.new(1n)))

def draw(k: Nat, +r: U32, acc: List<&2, U32>) -> U32 & List<&2, U32>:
  match k:
    case 0n:
      (r, acc)
    case 1n+p:
      draw(p, B.lcg(r), Con{B.lcg(r), acc})

def from_go(+r: U32, +c: U32, f: SG.SegTree, z: Unit) -> St:
  match z:
    case Unit{}:
      S{r, c, f}

def from_with(+c: U32, old: SG.SegTree, p: U32 & List<&2, U32>) -> St:
  (r, xs) = p
  from_go(r, B.mix(c, 5), SG.from_list(xs), SG.dispose(old))

def do_from(st: St) -> St:
  S{r, c, f} = st
  from_with(c, f, draw(8n, r, Nil{}))

def do_null(st: St) -> St:
  S{r, c, f} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), f}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_add(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_add(p, n, do_add(st, n))

def loop_prefix(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_prefix(p, n, do_prefix(st, n))

def loop_range(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_range(p, n, do_range(st, n))

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

def loop_from(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_from(p, do_from(st))

def loop_set(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set(p, n, do_set(st, n))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_add(k, n, st)
    case 1:
      loop_prefix(k, n, st)
    case 2:
      loop_range(k, n, st)
    case 3:
      loop_len(k, st)
    case 4:
      loop_new(k, st)
    case 5:
      loop_from(k, st)
    case 6:
      loop_set(k, n, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

# Observe the whole tree once, so the build is fully evaluated before the
# measured loop and every region pays for it identically.
def observe(+r: U32, +c: U32, p: SG.SegTree & Nat) -> St:
  (f, +n) = p
  fin_sum(r, c, SG.range_query(f, 0n, n))

def settle(st: St) -> St:
  S{r, c, f} = st
  observe(r, c, SG.length(f))

def drain_go(+c: U32, z: Unit) -> U32:
  match z:
    case Unit{}:
      c

def drain_fin(+c: U32, p: SG.SegTree & Result<&2, &2, E.Error, U32>) -> U32:
  (f, x) = p
  drain_go(B.mix(c, sum_code(x)), SG.dispose(f))

def drain_len(+c: U32, p: SG.SegTree & Nat) -> U32:
  (f, +n) = p
  drain_fin(B.mix(c, U32.from_nat(n)), SG.range_query(f, 0n, n))

def drain(st: St) -> U32:
  S{+r, c, f} = st
  drain_len(B.mix(c, r), SG.length(f))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, size, settle(loop_set(size, size, init(seed, size))))))

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
