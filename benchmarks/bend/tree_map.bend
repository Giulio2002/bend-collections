import Base
import ./common.bend as B
import ../../src/balanced_search_tree.bend as BT

# Same workloads, stream, checksums, and timing harness as the unchanged C RB
# reference. Iteration folds entries directly, as C does; no output list.
type St is Type:
  S{rng: U32, chk: U32, m: BT.TreeMap<U32, U32, U32.cmp>}

def init(+seed: U32) -> St:
  S{seed, 0, BT.new(~U32, ~U32, ~U32.cmp)}

def hi(v: U32) -> U32:
  U32.shrn(v, 16n)

def val_code(x: Maybe<&2, U32>) -> U32:
  match x:
    case None{}:
      9
    case Some{v}:
      v

def entry_code(x: Maybe<&2, BT.Entry<U32, U32>>) -> U32:
  match x:
    case None{}:
      9
    case Some{BT.Entry{k, v}}:
      B.mix(k, v)

def fin_val(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>) -> St:
  (m, x) = p
  S{r, B.mix(c, val_code(x)), m}

def fin_entry(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Maybe<&2, BT.Entry<U32, U32>>) -> St:
  (m, x) = p
  S{r, B.mix(c, entry_code(x)), m}

def fin_put(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Result<&2, &2, BT.Rejected<U32, U32>, Maybe<&2, U32>>) -> St:
  match p:
    case Tuple{m, Done{old}}:
      S{r, B.mix(c, 1), m}
    case Tuple{m, Fail{e}}:
      S{r, B.mix(c, 999), m}

def ins_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  fin_put(r, c, BT.put(~U32, ~U32, ~U32.cmp, m, B.below(r, U32.from_nat(1n+n)), r))

def look_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  fin_val(r, c, BT.get(~U32, ~U32, ~U32.cmp, m, B.below(r, U32.from_nat(1n+n))))

def bool_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def fin_has(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Bool) -> St:
  (m, b) = p
  S{r, B.mix(c, bool_bit(b)), m}

def has_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  fin_has(r, c, BT.contains_key(~U32, ~U32, ~U32.cmp, m, B.below(r, U32.from_nat(1n+n))))

def lb_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  fin_entry(r, c, BT.ceiling_entry(~U32, ~U32, ~U32.cmp, m, B.below(r, U32.from_nat(1n+n))))

def rm_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  fin_val(r, c, BT.remove(~U32, ~U32, ~U32.cmp, m, B.below(r, U32.from_nat(1n+n))))

def pair_rm_go(+r: U32, c: U32, k: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Maybe<&2, U32>) -> St:
  (m, x) = p
  fin_put(r, B.mix(c, val_code(x)), BT.put(~U32, ~U32, ~U32.cmp, m, k, r))

def pair_rm_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  +k = B.below(r, U32.from_nat(1n+n))
  pair_rm_go(r, c, k, BT.remove(~U32, ~U32, ~U32.cmp, m, k))

def do_ins(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  ins_with(B.lcg(r), c, m, n)

def do_rm(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  rm_with(B.lcg(r), c, m, n)

def do_look(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  look_with(B.lcg(r), c, m, n)

def do_has(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  has_with(B.lcg(r), c, m, n)

def do_lb(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  lb_with(B.lcg(r), c, m, n)

def do_pair_rm(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  pair_rm_with(B.lcg(r), c, m, n)

def do_min(st: St) -> St:
  S{r, c, m} = st
  fin_entry(B.lcg(r), c, BT.first_entry(~U32, ~U32, ~U32.cmp, m))

def do_max(st: St) -> St:
  S{r, c, m} = st
  fin_entry(B.lcg(r), c, BT.last_entry(~U32, ~U32, ~U32.cmp, m))

def fold_loop(fuel: Nat, r: U32, c: U32, st: BT.Cursor<U32, U32, U32.cmp> & Maybe<&2, BT.Entry<U32, U32>>) -> St:
  match fuel st:
    case 0n Tuple{cursor, item}:
      S{r, c, BT.iterator_finish(~U32, ~U32, ~U32.cmp, cursor)}
    case 1n+f Tuple{cursor, None{}}:
      S{r, c, BT.iterator_finish(~U32, ~U32, ~U32.cmp, cursor)}
    case 1n+f Tuple{cursor, Some{BT.Entry{k, v}}}:
      fold_loop(f, r, B.mix(B.mix(c, k), v), BT.iterator_next(~U32, ~U32, ~U32.cmp, cursor))

def fold_start(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Nat) -> St:
  (m, n) = p
  fold_loop(1n+n, r, c, BT.iterator_next(~U32, ~U32, ~U32.cmp, BT.iterator(~U32, ~U32, ~U32.cmp, m)))

def range_ready(r: U32, c: U32, n: Nat, p: Result<&1, &1, BT.InvalidView<U32, U32, U32.cmp>, BT.View<U32, U32, U32.cmp>>) -> St:
  match p:
    case Fail{BT.InvalidView{m, e}}:
      S{r, c, m}
    case Done{view}:
      fold_loop(1n+n, r, c, BT.iterator_next(~U32, ~U32, ~U32.cmp, BT.view_iterator(~U32, ~U32, ~U32.cmp, view)))

def range_with(+r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, +n: Nat) -> St:
  range_ready(r, c, 1n+n, BT.sub_map(~U32, ~U32, ~U32.cmp, m, BT.Inclusive{B.below(r, U32.from_nat(1n+n))}, BT.Exclusive{B.below(hi(r), U32.from_nat(1n+n))}))

def do_range(st: St, +n: Nat) -> St:
  S{r, c, m} = st
  range_with(B.lcg(r), c, m, n)

def do_to_list(st: St) -> St:
  S{r, c, m} = st
  fold_start(B.lcg(r), c, BT.size(~U32, ~U32, ~U32.cmp, m))

def fin_len(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Nat) -> St:
  (m, n) = p
  S{r, B.mix(c, U32.from_nat(n)), m}

def do_len(st: St) -> St:
  S{r, c, m} = st
  fin_len(B.lcg(r), c, BT.size(~U32, ~U32, ~U32.cmp, m))

def new_observed(r: U32, c: U32, m: BT.TreeMap<U32, U32, U32.cmp>, p: BT.TreeMap<U32, U32, U32.cmp> & Nat) -> St:
  (empty, n) = p
  S{r, B.mix(c, U32.from_nat(n)), m}

def do_new(st: St) -> St:
  S{r, c, m} = st
  new_observed(B.lcg(r), c, m, BT.size(~U32, ~U32, ~U32.cmp, BT.new(~U32, ~U32, ~U32.cmp)))

def do_null(st: St) -> St:
  S{r, c, m} = st
  +r2 = B.lcg(r)
  S{r2, B.mix(c, r2), m}
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


def settle(st: St) -> St:
  S{r, c, m} = st
  fold_start(r, c, BT.size(~U32, ~U32, ~U32.cmp, m))

def drain_entry(c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Maybe<&2, BT.Entry<U32, U32>>) -> U32:
  (m, e) = p
  B.mix(c, entry_code(e))

def drain_size(r: U32, c: U32, p: BT.TreeMap<U32, U32, U32.cmp> & Nat) -> U32:
  (m, n) = p
  drain_entry(B.mix(B.mix(c, r), U32.from_nat(n)), BT.first_entry(~U32, ~U32, ~U32.cmp, m))

def drain(st: St) -> U32:
  S{r, c, m} = st
  drain_size(r, c, BT.size(~U32, ~U32, ~U32.cmp, m))

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
