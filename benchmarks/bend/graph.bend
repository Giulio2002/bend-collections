import Base
import ./common.bend as B
import ../../src/graph.bend as GR
import ../../types/graph.bend as E

# Native benchmark driver for src/graph.bend.
# argv = [op, size, count, reps, seed]; `size` is the vertex count (the build
# adds vertices 0 .. size-1 and then `size` random edges).
# benchmarks/native/graph.c performs the identical work. Op selectors:
# 0 add_vertex, 1 remove_vertex, 2 add_edge, 3 remove_edge, 4 has_vertex,
# 5 has_edge, 6 neighbors, 7 vertices, 8 edges, 9 new, else stream only.
# The graph is undirected (the harder case: both endpoint sets are updated).

type St is Type:
  S{rng: U32, chk: U32, g: GR.Graph}

def init(+seed: U32) -> St:
  S{seed, 0, GR.new(False{})}

def hi(v: U32) -> U32:
  U32.shrn(v, 16n)

def err_code(e: E.Error) -> U32:
  match e:
    case E.VertexExists{}:
      2
    case E.VertexNotFound{}:
      3
    case E.SelfLoop{}:
      4
    case E.EdgeNotFound{}:
      5

def unit_code(x: Result<&2, &2, E.Error, Unit>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{u}:
      1

def bool_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def flag_code(x: Result<&2, &2, E.Error, Bool>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{b}:
      bool_bit(b)

def fold_u32(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_u32(t, B.mix(c, x))

def nbr_code(c: U32, x: Result<&2, &2, E.Error, List<&2, U32>>) -> U32:
  match x:
    case Fail{e}:
      B.mix(c, err_code(e))
    case Done{xs}:
      fold_u32(xs, c)

def fold_edges(es: List<&2, E.Edge>, c: U32) -> U32:
  match es:
    case Nil{}:
      c
    case Con{E.Edge{u, v}, t}:
      fold_edges(t, B.mix(B.mix(c, u), v))

def fin_unit(r: U32, c: U32, p: GR.Graph & Result<&2, &2, E.Error, Unit>) -> St:
  (g, x) = p
  S{r, B.mix(c, unit_code(x)), g}

def av_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_unit(r, c, GR.add_vertex(g, B.below(r, U32.from_nat(1n+n))))

def do_av(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  av_with(B.lcg(r), c, g, n)

def rv_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_unit(r, c, GR.remove_vertex(g, B.below(r, U32.from_nat(1n+n))))

def do_rv(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  rv_with(B.lcg(r), c, g, n)

def ae_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_unit(r, c, GR.add_edge(g, B.below(r, U32.from_nat(1n+n)), B.below(hi(r), U32.from_nat(1n+n))))

def do_ae(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  ae_with(B.lcg(r), c, g, n)

def re_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_unit(r, c, GR.remove_edge(g, B.below(r, U32.from_nat(1n+n)), B.below(hi(r), U32.from_nat(1n+n))))

def do_re(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  re_with(B.lcg(r), c, g, n)

def fin_bool(r: U32, c: U32, p: GR.Graph & Bool) -> St:
  (g, b) = p
  S{r, B.mix(c, bool_bit(b)), g}

def hv_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_bool(r, c, GR.has_vertex(g, B.below(r, U32.from_nat(1n+n))))

def do_hv(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  hv_with(B.lcg(r), c, g, n)

def fin_flag(r: U32, c: U32, p: GR.Graph & Result<&2, &2, E.Error, Bool>) -> St:
  (g, x) = p
  S{r, B.mix(c, flag_code(x)), g}

def he_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_flag(r, c, GR.has_edge(g, B.below(r, U32.from_nat(1n+n)), B.below(hi(r), U32.from_nat(1n+n))))

def do_he(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  he_with(B.lcg(r), c, g, n)

def fin_nbr(r: U32, c: U32, p: GR.Graph & Result<&2, &2, E.Error, List<&2, U32>>) -> St:
  (g, x) = p
  S{r, nbr_code(c, x), g}

def nb_with(+r: U32, c: U32, g: GR.Graph, +n: Nat) -> St:
  fin_nbr(r, c, GR.neighbors(g, B.below(r, U32.from_nat(1n+n))))

def do_nb(st: St, +n: Nat) -> St:
  S{r, c, g} = st
  nb_with(B.lcg(r), c, g, n)

def fin_vs(r: U32, c: U32, p: GR.Graph & List<&2, U32>) -> St:
  (g, xs) = p
  S{r, fold_u32(xs, c), g}

def do_vs(st: St) -> St:
  S{r, c, g} = st
  fin_vs(B.lcg(r), c, GR.vertices(g))

def fin_es(r: U32, c: U32, p: GR.Graph & List<&2, E.Edge>) -> St:
  (g, es) = p
  S{r, fold_edges(es, c), g}

def do_es(st: St) -> St:
  S{r, c, g} = st
  fin_es(B.lcg(r), c, GR.edges(g))

def drop_graph(g: GR.Graph, c: U32) -> U32:
  GR.G{d, glo, ghi, cap, depth, ids, adj} = g
  c

def drop_new(p: GR.Graph & List<&2, U32>, c: U32) -> U32:
  (g, xs) = p
  drop_graph(g, fold_u32(xs, c))

def do_new(st: St) -> St:
  S{r, c, g} = st
  S{B.lcg(r), drop_new(GR.vertices(GR.new(False{})), c), g}

def do_null(st: St) -> St:
  S{r, c, g} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), g}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_av(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_av(p, n, do_av(st, n))

def loop_rv(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rv(p, n, do_rv(st, n))

def loop_ae(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ae(p, n, do_ae(st, n))

def loop_re(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_re(p, n, do_re(st, n))

def loop_hv(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_hv(p, n, do_hv(st, n))

def loop_he(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_he(p, n, do_he(st, n))

def loop_nb(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_nb(p, n, do_nb(st, n))

def loop_vs(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_vs(p, do_vs(st))

def loop_es(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_es(p, do_es(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_av(k, n, st)
    case 1:
      loop_rv(k, n, st)
    case 2:
      loop_ae(k, n, st)
    case 3:
      loop_re(k, n, st)
    case 4:
      loop_hv(k, n, st)
    case 5:
      loop_he(k, n, st)
    case 6:
      loop_nb(k, n, st)
    case 7:
      loop_vs(k, st)
    case 8:
      loop_es(k, st)
    case 9:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- build / settle / drain ----

# vertices 0 .. size-1, added without consuming the value stream
def keep_unit(r: U32, c: U32, p: GR.Graph & Result<&2, &2, E.Error, Unit>) -> St:
  (g, x) = p
  S{r, B.mix(c, unit_code(x)), g}

def add_at(+i: Nat, st: St) -> St:
  S{r, c, g} = st
  keep_unit(r, c, GR.add_vertex(g, U32.from_nat(i)))

def seed_vs(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+ +p:
      seed_vs(p, add_at(p, st))

def settle(st: St) -> St:
  S{r, c, g} = st
  fin_es(r, c, GR.edges(g))

# The drain is deliberately independent of how many elements the measured
# operation added or removed, so region A and region B pay the same
# observation cost and the difference is the measured operation alone. Every
# measured operation folds its own result into the checksum inside the loop,
# and `settle` forces the built structure before the loop starts.
def drain_loop(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, n, do_he(do_hv(st, n), n))

def drain_end(st: St) -> U32:
  S{r, c, g} = st
  c

def drain(+size: Nat, st: St) -> U32:
  S{+r, c, g} = st
  drain_end(drain_loop(16n, size, S{r, B.mix(c, r), g}))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(size, loop_null(kn, measured(op, k, size, settle(loop_ae(size, size, seed_vs(size, init(seed)))))))

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
