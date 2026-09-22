import Base
import ./common.bend as B
import ../../src/containers/dlist_iterator.bend as I
import ../../src/containers/doubly_linked_list.bend as D
import ../../src/containers/types/doubly_linked_list.bend as E

type St is Type:
  S{rng: U32, chk: U32, it: I.Iterator<U32>}

def fold_vals(xs: List<&2, U32>, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{x, t}:
      fold_vals(t, B.mix(c, x))

def built(r: U32, c: U32, p: D.DList<U32> & List<&2, U32>) -> St:
  (s, xs) = p
  S{r, fold_vals(xs, c), I.iter_first(~U32, s)}

def pushed(+r: U32, p: D.DList<U32> & E.Handle) -> U32 & D.DList<U32>:
  (s, h) = p
  (r, s)

def build_step(+r: U32, s: D.DList<U32>) -> U32 & D.DList<U32>:
  pushed(r, D.push_back(~U32, s, r))

def build_go(n: Nat, st: U32 & D.DList<U32>) -> St:
  match n:
    case 0n:
      (r, s) = st
      built(r, 0, D.to_list(~U32, s))
    case 1n+p:
      (r, s) = st
      build_go(p, build_step(B.lcg(r), s))

def val_code(r: Result<&2, &2, I.Error, U32>) -> U32:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      9

def val(r: U32, c: U32, p: I.Iterator<U32> & Result<&2, &2, I.Error, U32>) -> St:
  (it, x) = p
  S{r, B.mix(c, val_code(x)), it}

def unit_code(r: Result<&2, &2, I.Error, Unit>) -> U32:
  match r:
    case Done{x}:
      1
    case Fail{e}:
      9

def unit(r: U32, c: U32, p: I.Iterator<U32> & Result<&2, &2, I.Error, Unit>) -> St:
  (it, x) = p
  S{r, B.mix(c, unit_code(x)), it}

def flag_code(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def flag(r: U32, c: U32, p: I.Iterator<U32> & Bool) -> St:
  (it, b) = p
  S{r, B.mix(c, flag_code(b)), it}

def position(r: U32, c: U32, p: I.Iterator<U32> & Nat) -> St:
  (it, n) = p
  S{r, B.mix(c, U32.from_nat(n)), it}

def forward_cursor(p: I.Iterator<U32> & Bool) -> I.Iterator<U32>:
  match p:
    case Tuple{it, True{}}:
      it
    case Tuple{it, False{}}:
      I.iter_first(~U32, I.finish(~U32, it))

def forward_ready(r: U32, c: U32, p: I.Iterator<U32> & Bool) -> St:
  val(r, c, I.next(~U32, forward_cursor(p)))

def backward_cursor(p: I.Iterator<U32> & Bool) -> I.Iterator<U32>:
  match p:
    case Tuple{it, True{}}:
      it
    case Tuple{it, False{}}:
      I.iter_last(~U32, I.finish(~U32, it))

def backward_ready(r: U32, c: U32, p: I.Iterator<U32> & Bool) -> St:
  val(r, c, I.previous(~U32, backward_cursor(p)))

def pair_remove(st: St) -> St:
  S{r, c, it} = st
  unit(r, c, I.remove(~U32, it))

def pair_previous(st: St) -> St:
  S{r, c, it} = st
  pair_remove(val(r, c, I.previous(~U32, it)))

def step_0(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  position(r, c, I.position(~U32, I.iter_first(~U32, I.finish(~U32, it))))

def step_1(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  position(r, c, I.position(~U32, I.iter_last(~U32, I.finish(~U32, it))))

def step_2(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  forward_ready(r, c, I.has_next(~U32, it))

def step_3(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  backward_ready(r, c, I.has_previous(~U32, it))

def step_4(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  unit(r, c, I.set(~U32, it, r))

def step_5(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  pair_previous(unit(r, c, I.add(~U32, it, r)))

def step_6(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  flag(r, c, I.has_next(~U32, it))

def step_7(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  flag(r, c, I.has_previous(~U32, it))

def step_8(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  position(r, c, I.position(~U32, it))

def step_null(st: St) -> St:
  S{r0, c, it} = st
  +r = B.lcg(r0)
  S{r, B.mix(c, r), it}

def loop(~f: St -> St, k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop(~f, p, f(st))

def measured(op: U32, k: Nat, st: St) -> St:
  match op:
    case 0:
      loop(~step_0, k, st)
    case 1:
      loop(~step_1, k, st)
    case 2:
      loop(~step_2, k, st)
    case 3:
      loop(~step_3, k, st)
    case 4:
      loop(~step_4, k, st)
    case 5:
      loop(~step_5, k, st)
    case 6:
      loop(~step_6, k, st)
    case 7:
      loop(~step_7, k, st)
    case 8:
      loop(~step_8, k, st)
    case _:
      loop(~step_null, k, st)

def prepare(st: St) -> St:
  S{r, c, it} = st
  val(r, c, I.next(~U32, it))

def drain_list(c: U32, p: D.DList<U32> & List<&2, U32>) -> U32:
  (s, xs) = p
  fold_vals(xs, c)

def drain(st: St) -> U32:
  S{r, c, it} = st
  drain_list(B.mix(c, r), D.to_list(~U32, I.finish(~U32, it)))

def round(+op: U32, +size: Nat, +k: Nat, +kn: Nat, +seed: U32) -> U32:
  drain(loop(~step_null, kn, measured(op, k, prepare(build_go(size, (seed, D.new(~U32, 1)))))))

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
