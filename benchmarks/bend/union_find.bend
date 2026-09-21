import Base
import ./common.bend as B
import ../../src/union_find.bend as UF
import ../../types/union_find.bend as E

# Native benchmark driver for src/union_find.bend.
# argv = [op, size, count, reps, seed]; `size` is both the universe size and
# the number of unions performed while building. benchmarks/native/union_find.c
# performs the identical work. Op selectors: 0 find, 1 union, 2 connected,
# 3 component_size, 4 component_count, 5 new, anything else = stream only.

type St is Type:
  S{rng: U32, chk: U32, u: UF.UnionFind}

def init(+seed: U32, +size: Nat) -> St:
  S{seed, 0, UF.new(size)}

def hi(v: U32) -> U32:
  U32.shrn(v, 16n)

def nat_code(x: Result<&2, &2, E.Error, Nat>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{v}:
      U32.from_nat(v)

def bool_code(x: Result<&2, &2, E.Error, Bool>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{True{}}:
      1
    case Done{False{}}:
      0

def fin_bool(r: U32, c: U32, p: UF.UnionFind & Result<&2, &2, E.Error, Bool>) -> St:
  (u, x) = p
  S{r, B.mix(c, bool_code(x)), u}

def fin_item(r: U32, c: U32, p: UF.UnionFind & Result<&2, &2, E.Error, Nat>) -> St:
  (u, x) = p
  S{r, B.mix(c, nat_code(x)), u}

def fin_nat(r: U32, c: U32, p: UF.UnionFind & Nat) -> St:
  (u, x) = p
  S{r, B.mix(c, U32.from_nat(x)), u}

def drop_new_go(r: U32, c: U32, u: UF.UnionFind, z: Unit) -> St:
  match z:
    case Unit{}:
      S{r, c, u}

def drop_new(r: U32, c: U32, u: UF.UnionFind, p: UF.UnionFind & Nat) -> St:
  (u2, x) = p
  drop_new_go(r, B.mix(c, U32.from_nat(x)), u, UF.dispose(u2))


def union_with(+r: U32, c: U32, u: UF.UnionFind, +n: Nat) -> St:
  fin_bool(r, c, UF.union(u, B.nat_below(r, 1n+n), B.nat_below(hi(r), 1n+n)))

def do_union(st: St, +n: Nat) -> St:
  S{r, c, u} = st
  union_with(B.lcg(r), c, u, n)

def find_with(+r: U32, c: U32, u: UF.UnionFind, +n: Nat) -> St:
  fin_item(r, c, UF.find(u, B.nat_below(r, 1n+n)))

def do_find(st: St, +n: Nat) -> St:
  S{r, c, u} = st
  find_with(B.lcg(r), c, u, n)

def conn_with(+r: U32, c: U32, u: UF.UnionFind, +n: Nat) -> St:
  fin_bool(r, c, UF.connected(u, B.nat_below(r, 1n+n), B.nat_below(hi(r), 1n+n)))

def do_conn(st: St, +n: Nat) -> St:
  S{r, c, u} = st
  conn_with(B.lcg(r), c, u, n)

def size_with(+r: U32, c: U32, u: UF.UnionFind, +n: Nat) -> St:
  fin_item(r, c, UF.component_size(u, B.nat_below(r, 1n+n)))

def do_size(st: St, +n: Nat) -> St:
  S{r, c, u} = st
  size_with(B.lcg(r), c, u, n)

def do_count(st: St) -> St:
  S{r, c, u} = st
  fin_nat(B.lcg(r), c, UF.component_count(u))

def do_new(st: St) -> St:
  S{r, c, u} = st
  drop_new(B.lcg(r), c, u, UF.component_count(UF.new(1n)))

def do_null(st: St) -> St:
  S{r, c, u} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), u}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_union(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_union(p, n, do_union(st, n))

def loop_find(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_find(p, n, do_find(st, n))

def loop_conn(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_conn(p, n, do_conn(st, n))

def loop_size(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_size(p, n, do_size(st, n))

def loop_count(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_count(p, do_count(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_find(k, n, st)
    case 1:
      loop_union(k, n, st)
    case 2:
      loop_conn(k, n, st)
    case 3:
      loop_size(k, n, st)
    case 4:
      loop_count(k, st)
    case 5:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

# Observe every representative once, so the build is fully evaluated before
# the measured loop and both regions pay for it identically.
def peek_at(+i: Nat, st: St) -> St:
  S{r, c, u} = st
  fin_item(r, c, UF.find(u, i))

def sweep(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+ +p:
      sweep(p, n, peek_at(p, st))

def settle(+size: Nat, st: St) -> St:
  sweep(size, size, st)

def drain_go(c: U32, z: Unit) -> U32:
  match z:
    case Unit{}:
      c

def drain_fin(r: U32, c: U32, p: UF.UnionFind & Nat) -> U32:
  (u, x) = p
  drain_go(B.mix(c, U32.from_nat(x)), UF.dispose(u))

def drain(st: St) -> U32:
  S{+r, c, u} = st
  drain_fin(r, B.mix(c, r), UF.component_count(u))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop_null(kn, measured(op, k, size, settle(size, loop_union(size, size, init(seed, size))))))

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
