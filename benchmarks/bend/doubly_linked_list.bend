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

type St is Type:
  S{rng: U32, chk: U32, l: DL.DList<U32>}

def tag() -> U32:
  1

def init(+seed: U32) -> St:
  S{seed, 0, DL.new(~U32, tag())}

# A handle id drawn from 0 .. n: live when it is below the number of elements
# the build pushed, stale otherwise. Ids are U32, so this is one modulo.
def handle_of(+r: U32, +m: U32) -> E.Handle:
  E.H{tag(), B.below(r, m)}

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
    case E.H{+l, +i}:
      B.mix(l, i)

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
  fin_handle(r, c, DL.push_front(~U32, l, r))

def do_pf(st: St) -> St:
  S{r, c, l} = st
  pf_with(B.lcg(r), c, l)

def pb_with(+r: U32, c: U32, l: DL.DList<U32>) -> St:
  fin_handle(r, c, DL.push_back(~U32, l, r))

def do_pb(st: St) -> St:
  S{r, c, l} = st
  pb_with(B.lcg(r), c, l)

def ib_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_ins(r, c, DL.insert_before(~U32, l, handle_of(r, m), r))

def do_ib(st: St, +m: U32) -> St:
  S{r, c, l} = st
  ib_with(B.lcg(r), c, l, m)

def ia_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_ins(r, c, DL.insert_after(~U32, l, handle_of(r, m), r))

def do_ia(st: St, +m: U32) -> St:
  S{r, c, l} = st
  ia_with(B.lcg(r), c, l, m)

def rm_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_val(r, c, DL.remove(~U32, l, handle_of(r, m)))

def do_rm(st: St, +m: U32) -> St:
  S{r, c, l} = st
  rm_with(B.lcg(r), c, l, m)

def get_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_val(r, c, DL.get(~U32, l, handle_of(r, m)))

def do_get(st: St, +m: U32) -> St:
  S{r, c, l} = st
  get_with(B.lcg(r), c, l, m)

def set_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_unit(r, c, DL.set(~U32, l, handle_of(r, m), r))

def do_set(st: St, +m: U32) -> St:
  S{r, c, l} = st
  set_with(B.lcg(r), c, l, m)

def fin_nbr(r: U32, c: U32, p: DL.DList<U32> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>) -> St:
  (l, x) = p
  S{r, B.mix(c, nbr_code(x)), l}

def next_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_nbr(r, c, DL.next(~U32, l, handle_of(r, m)))

def do_next(st: St, +m: U32) -> St:
  S{r, c, l} = st
  next_with(B.lcg(r), c, l, m)

def prev_with(+r: U32, c: U32, l: DL.DList<U32>, +m: U32) -> St:
  fin_nbr(r, c, DL.prev(~U32, l, handle_of(r, m)))

def do_prev(st: St, +m: U32) -> St:
  S{r, c, l} = st
  prev_with(B.lcg(r), c, l, m)

def fin_nat(r: U32, c: U32, p: DL.DList<U32> & Nat) -> St:
  (l, n) = p
  S{r, B.mix(c, U32.from_nat(n)), l}

def do_len(st: St) -> St:
  S{r, c, l} = st
  fin_nat(B.lcg(r), c, DL.length(~U32, l))

def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

def fin_list(r: U32, c: U32, p: DL.DList<U32> & List<&2, U32>) -> St:
  (l, xs) = p
  S{r, fold_vals(xs, c), l}

def do_to_list(st: St) -> St:
  S{r, c, l} = st
  fin_list(B.lcg(r), c, DL.to_list(~U32, l))

def new_code(p: DL.DList<U32> & Nat) -> U32:
  (l2, n) = p
  U32.from_nat(n)

def do_new(st: St) -> St:
  S{r, c, l} = st
  S{B.lcg(r), B.mix(c, new_code(DL.length(~U32, DL.new(~U32, tag())))), l}

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

def loop_ib(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ib(p, m, do_ib(st, m))

def loop_ia(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ia(p, m, do_ia(st, m))

def loop_rm(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rm(p, m, do_rm(st, m))

def loop_get(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_get(p, m, do_get(st, m))

def loop_set(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set(p, m, do_set(st, m))

def loop_next(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_next(p, m, do_next(st, m))

def loop_prev(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_prev(p, m, do_prev(st, m))

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

def measured(+op: U32, +k: Nat, +m: U32, st: St) -> St:
  match op:
    case 0:
      loop_pf(k, st)
    case 1:
      loop_pb(k, st)
    case 2:
      loop_ib(k, m, st)
    case 3:
      loop_ia(k, m, st)
    case 4:
      loop_rm(k, m, st)
    case 5:
      loop_get(k, m, st)
    case 6:
      loop_set(k, m, st)
    case 7:
      loop_next(k, m, st)
    case 8:
      loop_prev(k, m, st)
    case 9:
      loop_len(k, st)
    case 10:
      loop_to_list(k, st)
    case 11:
      loop_new(k, st)
    case _:
      loop_null(k, st)

# ---- settle / drain ----

def settle_fin(+r: U32, c: U32, p: DL.DList<U32> & List<&2, U32>) -> St:
  (l, xs) = p
  S{r, fold_vals(xs, c), l}

def settle(st: St) -> St:
  S{r, c, l} = st
  settle_fin(r, c, DL.to_list(~U32, l))

# The drain is deliberately independent of how many elements the measured
# operation added or removed, so region A and region B pay the same
# observation cost and the difference is the measured operation alone. Every
# measured operation folds its own result into the checksum inside the loop,
# and `settle` forces the built structure before the loop starts.
def drain_loop(k: Nat, +m: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, m, do_get(st, m))

def drop_blocks(vals: Array<Maybe<&2, U32>>, prevs: Array<U32>, nexts: Array<U32>, +c: U32) -> U32:
  c

def drop_list(l: DL.DList<U32>, +c: U32) -> U32:
  DL.DL{t0, f0, c0, h0, t1, d0, k0, vals, prevs, nexts} = l
  drop_blocks(vals, prevs, nexts, c)

def drain_fin(c: U32, p: DL.DList<U32> & Nat) -> U32:
  (l, n) = p
  drop_list(l, B.mix(c, U32.from_nat(n)))

def drain_end(st: St) -> U32:
  S{r, c, l} = st
  drain_fin(c, DL.length(~U32, l))

def drain(+m: U32, st: St) -> U32:
  S{+r, c, l} = st
  drain_end(drain_loop(16n, m, S{r, B.mix(c, r), l}))

# One round: build a structure of `size`, settle it, run `k` measured
# operations, then `kn` value-stream steps, then destroy it. The three timed
# regions below run this same round with the SAME total number of loop
# iterations, so the build, the settle, the loop barrier, the argument
# generation and the destruction all cancel in the differences.
def round_with(+op: U32, +k: Nat, +kn: Nat, +seed: U32, +m: U32, +size: Nat) -> U32:
  drain(m, loop_null(kn, measured(op, k, m, settle(loop_pb(size, init(seed))))))

def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  round_with(op, k, kn, seed, U32.from_nat(1n+size), size)

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
