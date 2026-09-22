import Base
import ./common.bend as B
import ../../src/containers/bitset.bend as BI
import ../../src/containers/types/bitset.bend as E

# Native benchmark driver for src/bitset.bend.
# argv = [op, size, count, reps, seed]; benchmarks/native/bitset.c performs the
# identical work. `size` is the logical bit count. Op selectors:
# 0 set, 1 clear, 2 get, 3 count, 4 length, 5 to_list, 6 union,
# 7 intersection, 8 difference, 9 xor, 10 new, anything else = stream only.
#
# The second operand of a binary operation is a copy of the built bitset,
# taken once per round in `settle` (the C reference memcpy's the same copy),
# and the binary operations give it back, so a combine measures the word-wise
# combine and not the operand.

type St is Type:
  S{rng: U32, chk: U32, s: BI.Bitset, b: BI.Bitset}

def init(+seed: U32, +size: Nat) -> St:
  S{seed, 0, BI.new(size), BI.new(0n)}

def unit_code(x: Result<&2, &2, E.Error, Unit>) -> U32:
  match x:
    case Fail{e}:
      7
    case Done{u}:
      1

def bit_code(x: Result<&2, &2, E.Error, Bool>) -> U32:
  match x:
    case Fail{e}:
      9
    case Done{True{}}:
      1
    case Done{False{}}:
      0

def fin_unit(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & Result<&2, &2, E.Error, Unit>) -> St:
  (s, x) = p
  S{r, B.mix(c, unit_code(x)), s, b}

def fin_bit(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & Result<&2, &2, E.Error, Bool>) -> St:
  (s, x) = p
  S{r, B.mix(c, bit_code(x)), s, b}

def fin_nat(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & Nat) -> St:
  (s, n) = p
  S{r, B.mix(c, U32.from_nat(n)), s, b}

def fold_nats(xs: List<&2, Nat>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_nats(t, B.mix(c, U32.from_nat(x)))

def fin_list(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & List<&2, Nat>) -> St:
  (s, xs) = p
  S{r, fold_nats(xs, c), s, b}

def fin_comb(r: U32, c: U32, p: BI.Bitset & BI.Bitset & Result<&2, &2, E.Error, Unit>) -> St:
  (s, b, x) = p
  S{r, B.mix(c, unit_code(x)), s, b}

# ---- one step of each operation ----

def set_with(+r: U32, c: U32, s: BI.Bitset, b: BI.Bitset, +n: Nat) -> St:
  fin_unit(r, c, b, BI.set(s, B.nat_below(r, 1n+n)))

def do_set(st: St, +n: Nat) -> St:
  S{r, c, s, b} = st
  set_with(B.lcg(r), c, s, b, n)

def clear_with(+r: U32, c: U32, s: BI.Bitset, b: BI.Bitset, +n: Nat) -> St:
  fin_unit(r, c, b, BI.clear(s, B.nat_below(r, 1n+n)))

def do_clear(st: St, +n: Nat) -> St:
  S{r, c, s, b} = st
  clear_with(B.lcg(r), c, s, b, n)

def get_with(+r: U32, c: U32, s: BI.Bitset, b: BI.Bitset, +n: Nat) -> St:
  fin_bit(r, c, b, BI.get(s, B.nat_below(r, 1n+n)))

def do_get(st: St, +n: Nat) -> St:
  S{r, c, s, b} = st
  get_with(B.lcg(r), c, s, b, n)

def do_count(st: St) -> St:
  S{r, c, s, b} = st
  fin_nat(B.lcg(r), c, b, BI.count(s))

def do_len(st: St) -> St:
  S{r, c, s, b} = st
  fin_nat(B.lcg(r), c, b, BI.length(s))

def do_to_list(st: St) -> St:
  S{r, c, s, b} = st
  fin_list(B.lcg(r), c, b, BI.to_list(s))

def do_union(st: St) -> St:
  S{r, c, s, b} = st
  fin_comb(B.lcg(r), c, BI.union(s, b))

def do_inter(st: St) -> St:
  S{r, c, s, b} = st
  fin_comb(B.lcg(r), c, BI.intersection(s, b))

def do_diff(st: St) -> St:
  S{r, c, s, b} = st
  fin_comb(B.lcg(r), c, BI.difference(s, b))

def do_xor(st: St) -> St:
  S{r, c, s, b} = st
  fin_comb(B.lcg(r), c, BI.xor(s, b))

def new_drop(u: Unit, +r: U32, c: U32, s: BI.Bitset, b: BI.Bitset) -> St:
  match u:
    case Unit{}:
      S{r, B.mix(c, 0), s, b}

def do_new(st: St) -> St:
  S{r, c, s, b} = st
  new_drop(BI.dispose(BI.new(0n)), B.lcg(r), c, s, b)

def do_null(st: St) -> St:
  S{r, c, s, b} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), s, b}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_set(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set(p, n, do_set(st, n))

def loop_clear(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_clear(p, n, do_clear(st, n))

def loop_get(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_get(p, n, do_get(st, n))

def loop_count(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_count(p, do_count(st))

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

def loop_union(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_union(p, do_union(st))

def loop_inter(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_inter(p, do_inter(st))

def loop_diff(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_diff(p, do_diff(st))

def loop_xor(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_xor(p, do_xor(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_set(k, n, st)
    case 1:
      loop_clear(k, n, st)
    case 2:
      loop_get(k, n, st)
    case 3:
      loop_count(k, st)
    case 4:
      loop_len(k, st)
    case 5:
      loop_to_list(k, st)
    case 6:
      loop_union(k, st)
    case 7:
      loop_inter(k, st)
    case 8:
      loop_diff(k, st)
    case 9:
      loop_xor(k, st)
    case 10:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- build / settle / drain ----

# Observe the population count and take the operand copy, exactly as the C
# reference does before it starts the measured loop.
def settle_drop(r: U32, c: U32, s: BI.Bitset, s2: BI.Bitset, u: Unit) -> St:
  match u:
    case Unit{}:
      S{r, c, s, s2}

def settle_copy(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & BI.Bitset) -> St:
  (s, s2) = p
  settle_drop(r, c, s, s2, BI.dispose(b))

def settle_count(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & Nat) -> St:
  (s, n) = p
  settle_copy(r, B.mix(c, U32.from_nat(n)), b, BI.clone(s))

def settle(st: St) -> St:
  S{r, c, s, b} = st
  settle_count(r, c, b, BI.count(s))

def drain_end(r: U32, c: U32, u: Unit) -> U32:
  match u:
    case Unit{}:
      c

def drain_last(r: U32, c: U32, b: BI.Bitset, p: BI.Bitset & Nat) -> U32:
  (s, n) = p
  drain_end(r, B.mix(c, U32.from_nat(n)), BI.dispose2(s, b))

def drain(st: St) -> U32:
  S{+r, c, s, b} = st
  drain_last(r, B.mix(c, r), b, BI.count(s))

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
