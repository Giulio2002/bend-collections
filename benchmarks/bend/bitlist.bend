import Base
import ./common.bend as B
import ../../src/containers/bitlist.bend as BL
import ../../src/containers/types/bitlist.bend as E

# Native benchmark driver for src/containers/bitlist.bend.
# argv = [op, size, count, reps, seed, order]; benchmarks/native/bitlist.c
# performs the identical work. `size` is the number of bits a round pushes
# (pseudo-random, from the value stream) before the measured operations.
# Op selectors: 0 push, 2 get, 3 set, 4 length, 5 count, 6 to_list,
# 7 pop (restoring pair: pop, then push the popped bit back), 10 new,
# anything else = stream only.

type St is Type:
  S{rng: U32, chk: U32, s: BL.Bitlist}

def init(+seed: U32) -> St:
  S{seed, 0, BL.new()}

def low(r: U32) -> Bool:
  U32.is_eq(U32.and(r, 1), 1)

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

def fin_unit(r: U32, c: U32, p: BL.Bitlist & Result<&2, &2, E.Error, Unit>) -> St:
  (s, x) = p
  S{r, B.mix(c, unit_code(x)), s}

def fin_bit(r: U32, c: U32, p: BL.Bitlist & Result<&2, &2, E.Error, Bool>) -> St:
  (s, x) = p
  S{r, B.mix(c, bit_code(x)), s}

def fin_nat(r: U32, c: U32, p: BL.Bitlist & Nat) -> St:
  (s, n) = p
  S{r, B.mix(c, U32.from_nat(n)), s}

def bval(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def fold_bits(xs: List<&2, Bool>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_bits(t, B.mix(c, bval(x)))

def fin_list(r: U32, c: U32, p: BL.Bitlist & List<&2, Bool>) -> St:
  (s, xs) = p
  S{r, fold_bits(xs, c), s}

# ---- one step of each operation ----

def push_with(+r: U32, c: U32, s: BL.Bitlist) -> St:
  fin_unit(r, c, BL.push(s, low(r)))

def do_push(st: St) -> St:
  S{r, c, s} = st
  push_with(B.lcg(r), c, s)

def get_with(+r: U32, c: U32, s: BL.Bitlist, +n: Nat) -> St:
  fin_bit(r, c, BL.get(s, B.nat_below(r, 1n+n)))

def do_get(st: St, +n: Nat) -> St:
  S{r, c, s} = st
  get_with(B.lcg(r), c, s, n)

def set_with(+r: U32, c: U32, s: BL.Bitlist, +n: Nat) -> St:
  fin_unit(r, c, BL.set(s, B.nat_below(r, 1n+n)))

def do_set(st: St, +n: Nat) -> St:
  S{r, c, s} = st
  set_with(B.lcg(r), c, s, n)

def do_len(st: St) -> St:
  S{r, c, s} = st
  fin_nat(B.lcg(r), c, BL.length(s))

def do_count(st: St) -> St:
  S{r, c, s} = st
  fin_nat(B.lcg(r), c, BL.count(s))

def do_to_list(st: St) -> St:
  S{r, c, s} = st
  fin_list(B.lcg(r), c, BL.to_list(s))

# pop, then push the popped bit back (the list keeps its length)
def pair_back(r: U32, c: U32, p: BL.Bitlist & Result<&2, &2, E.Error, Unit>) -> St:
  (s, x) = p
  S{r, c, s}

def pair_popped(+r: U32, c: U32, p: BL.Bitlist & Result<&2, &2, E.Error, Bool>) -> St:
  match p:
    case Tuple{s, Done{+b}}:
      pair_back(r, B.mix(c, bval(b)), BL.push(s, b))
    case Tuple{s, Fail{e}}:
      S{r, B.mix(c, 9), s}

def do_pair(st: St) -> St:
  S{r, c, s} = st
  pair_popped(B.lcg(r), c, BL.pop(s))

def new_len(+r: U32, c: U32, s: BL.Bitlist, p: BL.Bitlist & Nat) -> St:
  (t, n) = p
  S{r, B.mix(c, U32.from_nat(n)), s}

def do_new(st: St) -> St:
  S{r, c, s} = st
  new_len(B.lcg(r), c, s, BL.length(BL.new()))

def do_null(st: St) -> St:
  S{r, c, s} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), s}

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

def loop_count(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_count(p, do_count(st))

def loop_to_list(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_to_list(p, do_to_list(st))

def loop_pair(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pair(p, do_pair(st))

def loop_new(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, do_new(st))

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_push(k, st)
    case 2:
      loop_get(k, n, st)
    case 3:
      loop_set(k, n, st)
    case 4:
      loop_len(k, st)
    case 5:
      loop_count(k, st)
    case 6:
      loop_to_list(k, st)
    case 7:
      loop_pair(k, st)
    case 10:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- build / settle / drain ----

def settle(st: St) -> St:
  S{r, c, s} = st
  fin_nat(r, c, BL.count(s))

def drain_last(r: U32, c: U32, p: BL.Bitlist & Nat) -> U32:
  (s, n) = p
  B.mix(c, U32.from_nat(n))

def drain(st: St) -> U32:
  S{+r, c, s} = st
  drain_last(r, B.mix(c, r), BL.count(s))

# One round: push `size` bits, settle, run `k` measured operations, then
# `kn` value-stream steps. The three timed regions run this same round with
# the SAME total number of loop iterations, so the build, the settle, the
# loop barrier and the argument generation all cancel in the differences.
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
