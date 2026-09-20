import Base
import ./common.bend as B
import ../../src/doubly_linked_list.bend as DL
import ../../types/doubly_linked_list.bend as E

# Native benchmark driver for src/doubly_linked_list.bend (U32 values).
# argv = [op, size, count, reps, seed]; the build pushes `size` elements at the
# back, so the live ids are 0 .. size-1 and a handle id drawn from 0 .. size is
# live with probability size/(size+1) and stale otherwise.
# benchmarks/native/doubly_linked_list.c performs the identical work. Op selectors:
# 0 push_front, 1 push_back, 2 insert_before, 3 insert_after, 4 remove, 5 get,
# 6 set, 7 next, 8 prev, 9 length, 10 to_list, 11 new, else stream only.

type St is Data:
  S{rng: U32, chk: U32, l: DL.DList<U32>}

def tag() -> Nat:
  1n

def init(+seed: U32) -> St:
  S{seed, 0, DL.new(U32, tag())}

def handle_of(+r: U32, +n: Nat) -> E.Handle:
  E.H{tag(), B.nat_below(r, 1n+n)}

def err_code(e: E.Error) -> U32:
  match e:
    case E.ForeignHandle{}:
      2
    case E.StaleHandle{}:
      3

def val_code(x: Result<&2, &2, E.Error, U32>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{v}:
      v

def unit_code(x: Result<&2, &2, E.Error, Unit>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{u}:
      1

def handle_code(h: E.Handle) -> U32:
  match h:
    case E.H{l, i}:
      B.mix(U32.from_nat(l), U32.from_nat(i))

def ins_code(x: Result<&2, &2, E.Error, E.Handle>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{h}:
      handle_code(h)

def nbr_code(x: Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> U32:
  match x:
    case Fail{e}:
      err_code(e)
    case Done{None{}}:
      7
    case Done{Some{h}}:
      handle_code(h)

def fin_handle(r: U32, c: U32, p: DL.DList<U32> & E.Handle) -> St:
  (l, h) = p
  S{r, B.mix(c, handle_code(h)), l}

def fin_ins(r: U32, c: U32, p: DL.DList<U32> & Result<&2, &2, E.Error, E.Handle>) -> St:
  (l, x) = p
  S{r, B.mix(c, ins_code(x)), l}

def fin_val(r: U32, c: U32, p: DL.DList<U32> & Result<&2, &2, E.Error, U32>) -> St:
  (l, x) = p
  S{r, B.mix(c, val_code(x)), l}

def fin_unit(r: U32, c: U32, p: DL.DList<U32> & Result<&2, &2, E.Error, Unit>) -> St:
  (l, x) = p
  S{r, B.mix(c, unit_code(x)), l}

def pf_with(+r: U32, c: U32, l: DL.DList<U32>) -> St:
  fin_handle(r, c, DL.push_front(U32, l, r))

def do_pf(st: St) -> St:
  S{r, c, l} = st
  pf_with(B.lcg(r), c, l)

def pb_with(+r: U32, c: U32, l: DL.DList<U32>) -> St:
  fin_handle(r, c, DL.push_back(U32, l, r))

def do_pb(st: St) -> St:
  S{r, c, l} = st
  pb_with(B.lcg(r), c, l)

def ib_with(+r: U32, c: U32, l: DL.DList<U32>, +n: Nat) -> St:
  fin_ins(r, c, DL.insert_before(U32, l, handle_of(r, n), r))

def do_ib(st: St, +n: Nat) -> St:
  S{r, c, l} = st
  ib_with(B.lcg(r), c, l, n)

def ia_with(+r: U32, c: U32, l: DL.DList<U32>, +n: Nat) -> St:
  fin_ins(r, c, DL.insert_after(U32, l, handle_of(r, n), r))

def do_ia(st: St, +n: Nat) -> St:
  S{r, c, l} = st
  ia_with(B.lcg(r), c, l, n)

def rm_with(+r: U32, c: U32, l: DL.DList<U32>, +n: Nat) -> St:
  fin_val(r, c, DL.remove(U32, l, handle_of(r, n)))

def do_rm(st: St, +n: Nat) -> St:
  S{r, c, l} = st
  rm_with(B.lcg(r), c, l, n)

def get_with(+r: U32, c: U32, +l: DL.DList<U32>, +n: Nat) -> St:
  S{r, B.mix(c, val_code(DL.get(U32, l, handle_of(r, n)))), l}

def do_get(st: St, +n: Nat) -> St:
  S{r, c, +l} = st
  get_with(B.lcg(r), c, l, n)

def set_with(+r: U32, c: U32, l: DL.DList<U32>, +n: Nat) -> St:
  fin_unit(r, c, DL.set(U32, l, handle_of(r, n), r))

def do_set(st: St, +n: Nat) -> St:
  S{r, c, l} = st
  set_with(B.lcg(r), c, l, n)

def next_with(+r: U32, c: U32, +l: DL.DList<U32>, +n: Nat) -> St:
  S{r, B.mix(c, nbr_code(DL.next(U32, l, handle_of(r, n)))), l}

def do_next(st: St, +n: Nat) -> St:
  S{r, c, +l} = st
  next_with(B.lcg(r), c, l, n)

def prev_with(+r: U32, c: U32, +l: DL.DList<U32>, +n: Nat) -> St:
  S{r, B.mix(c, nbr_code(DL.prev(U32, l, handle_of(r, n)))), l}

def do_prev(st: St, +n: Nat) -> St:
  S{r, c, +l} = st
  prev_with(B.lcg(r), c, l, n)

def do_len(st: St) -> St:
  S{r, c, +l} = st
  S{B.lcg(r), B.mix(c, U32.from_nat(DL.length(U32, l))), l}

def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

def do_to_list(st: St) -> St:
  S{r, c, +l} = st
  S{B.lcg(r), fold_vals(DL.to_list(U32, l), c), l}

def do_new(st: St) -> St:
  S{r, c, l} = st
  S{B.lcg(r), B.mix(c, U32.from_nat(DL.length(U32, DL.new(U32, tag())))), l}

def do_null(st: St) -> St:
  S{r, c, l} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), l}

# ---- loops ----

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def loop_pf(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pf(p, do_pf(st))

def loop_pb(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pb(p, do_pb(st))

def loop_ib(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ib(p, n, do_ib(st, n))

def loop_ia(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ia(p, n, do_ia(st, n))

def loop_rm(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rm(p, n, do_rm(st, n))

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

def loop_next(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_next(p, n, do_next(st, n))

def loop_prev(k: Nat, +n: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_prev(p, n, do_prev(st, n))

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

def measured(+op: U32, +k: Nat, +n: Nat, st: St) -> St:
  match op:
    case 0:
      loop_pf(k, st)
    case 1:
      loop_pb(k, st)
    case 2:
      loop_ib(k, n, st)
    case 3:
      loop_ia(k, n, st)
    case 4:
      loop_rm(k, n, st)
    case 5:
      loop_get(k, n, st)
    case 6:
      loop_set(k, n, st)
    case 7:
      loop_next(k, n, st)
    case 8:
      loop_prev(k, n, st)
    case 9:
      loop_len(k, st)
    case 10:
      loop_to_list(k, st)
    case 11:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

def settle(st: St) -> St:
  S{r, c, +l} = st
  S{r, fold_vals(DL.to_list(U32, l), c), l}

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
      drain_loop(p, n, do_get(st, n))

def drain_end(st: St) -> U32:
  S{r, c, +l} = st
  B.mix(c, U32.from_nat(DL.length(U32, l)))

def drain(+size: Nat, st: St) -> U32:
  S{+r, c, l} = st
  drain_end(drain_loop(16n, size, S{r, B.mix(c, r), l}))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(size, loop_null(kn, measured(op, k, size, settle(loop_pb(size, init(seed))))))

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
