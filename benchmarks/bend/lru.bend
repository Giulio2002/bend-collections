import Base
import ./common.bend as B
import ../../src/lru/fast.bend as L
import ../../types/lru_model.bend as T
import ../../src/lru/wide.bend as W

# Native benchmark driver for src/lru/fast.bend (the retained LRU semantics
# over a native Map plus an indexed doubly linked recency arena).
# argv = [op, size, count, reps, seed, order]. benchmarks/native/lru.c
# performs the identical work and folds the identical checksum.
#
# A round builds a cache of capacity max(size, 1) holding keys 0 .. size-1
# (key i is the one-character String Chr{65536 + i}, value i+1), oldest first, and
# settles it by folding its key list. The measured argument of a keyed
# operation is i = lcg % (size + 1): usually a hit, sometimes a miss.
#
#  0 add            insert/replace i; folds 1 if an entry was evicted
#  1 get            touches; folds the value or 0
#  2 peek           no touch, no metric; folds the value or 0
#  3 contains       folds 1 or 0
#  4 remove         folds the removed value or 0
#  5 purge          folds the number removed (plain; edge rows only)
#  6 resize         to t = i; folds t and the evictions, or 2^32-1 on failure
#  7 keys           folds every key, oldest first
#  8 len            folds the length
#  9 new            constructs a cache of capacity `size`; folds its
#                   capacity and length, or 2^32-1 when rejected (size 0)
# 10 remove + add   restoring pair: remove i (folds the value or 0), add it
#                   back (folds the eviction bit)
# 11 purge + refill restoring pair: purge a FULL cache (folds the count),
#                   then add keys 0 .. size-1 again
# 12 resize + back  restoring pair: shrink to t = 1 + lcg % size (folds t and
#                   the evictions), grow back to max(size, 1) (folds the
#                   evictions, always 0), and re-add exactly the evicted keys.
#                   The evicted keys are the oldest ones; the recency order is
#                   always the rotation o, o+1, ... (mod size) of the build,
#                   so both drivers track the offset `o` and re-add keys
#                   o .. o+e-1, restoring a full cache every time.
# else  value-stream step only (the A/B/C control)

type St is Type:
  S{rng: U32, chk: U32, o: U32, c: L.Fast<U32>}

# Key i is the one-character String Chr{65536 + i}: a valid Unicode scalar
# for every benchmark size (the supplementary planes have no surrogates).
def key(+i: U32) -> String:
  SCon{Chr{U32.add(i, 65536)}, SNil{}}

def now() -> L.Stamp:
  L.ST{0, 0}

def capof(+size: U32) -> U32:
  L.pick(U32.is_eq(size, 0), 1, size)

def bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def val_or(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{v}:
      v

def key_code(s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{Chr{x}, t}:
      U32.sub(x, 65536)

# ---- measured operations ----

def fold_keys(ks: List<&2, String>, c: U32) -> U32:
  match ks:
    case Nil{}:
      c
    case Con{k, t}:
      fold_keys(t, B.mix(c, key_code(k)))

def fin_bit(+r: U32, c: U32, +o: U32, p: L.Fast<U32> & Bool) -> St:
  (f, b) = p
  S{r, B.mix(c, bit(b)), o, f}

def fin_val(+r: U32, c: U32, +o: U32, p: L.Fast<U32> & Maybe<&2, U32>) -> St:
  (f, m) = p
  S{r, B.mix(c, val_or(m)), o, f}

def fin_num(+r: U32, c: U32, +o: U32, p: L.Fast<U32> & U32) -> St:
  (f, x) = p
  S{r, B.mix(c, x), o, f}

def draw(+r: U32, +size: U32) -> U32:
  U32.mod(r, U32.inc(size))

def do_add(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  fin_bit(r, c, o, L.add(~U32, f, key(i), U32.inc(i), now()))

def do_get(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.get(~U32, f, key(draw(r, size)), now()))

def do_peek(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.peek(~U32, f, key(draw(r, size)), now()))

def do_contains(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_bit(r, c, o, L.contains(~U32, f, key(draw(r, size)), now()))

def do_remove(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.remove(~U32, f, key(draw(r, size))))

def do_purge(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_num(B.lcg(r0), c, o, L.purge(~U32, f))

def rs_code(c: U32, +t: U32, x: Result<&2, &2, String, U32>) -> U32:
  match x:
    case Fail{e}:
      B.mix(c, 4294967295)
    case Done{e}:
      B.mix(B.mix(c, t), e)

def fin_rs(+r: U32, c: U32, +o: U32, +t: U32, p: L.Fast<U32> & Result<&2, &2, String, U32>) -> St:
  (f, x) = p
  S{r, rs_code(c, t, x), o, f}

def do_resize(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +t = draw(r, size)
  fin_rs(r, c, o, t, L.resize(~U32, f, t))

def fin_keys(+r: U32, c: U32, +o: U32, p: L.Fast<U32> & List<&2, String>) -> St:
  (f, ks) = p
  S{r, fold_keys(ks, c), o, f}

def do_keys(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_keys(B.lcg(r0), c, o, L.keys(~U32, f, now()))

def do_len(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_num(B.lcg(r0), c, o, L.len(~U32, f))

def new_len(c: U32, p: L.Fast<U32> & U32) -> U32:
  (g, n) = p
  B.mix(c, n)

def new_cap(c: U32, p: L.Fast<U32> & U32) -> U32:
  (g, k) = p
  new_len(B.mix(c, k), L.len(~U32, g))

def new_code(c: U32, x: L.Made<U32>) -> U32:
  match x:
    case L.Rejected{e}:
      B.mix(c, 4294967295)
    case L.Made{g}:
      new_cap(c, L.capacity(~U32, g))

def do_new(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  S{B.lcg(r0), new_code(c, L.new(~U32, size)), o, f}

def drop_bit(p: L.Fast<U32> & Bool) -> L.Fast<U32>:
  (f, b) = p
  f

def put(f: L.Fast<U32>, +i: U32) -> L.Fast<U32>:
  drop_bit(L.add(~U32, f, key(i), U32.inc(i), now()))

def ra_fin(+r: U32, c: U32, +o: U32, +i: U32, p: L.Fast<U32> & Maybe<&2, U32>) -> St:
  (f, m) = p
  fin_bit(r, B.mix(c, val_or(m)), o, L.add(~U32, f, key(i), U32.inc(i), now()))

# add keys (from + j) mod m for j = 0 .. k-1
def do_remove_add(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  ra_fin(r, c, o, i, L.remove(~U32, f, key(i)))

def wrap(+x: U32, +m: U32) -> U32:
  L.pick(U32.is_lt(x, m), x, 0)

def refill(k: Nat, f: L.Fast<U32>, +at: U32, +m: U32) -> L.Fast<U32>:
  match k:
    case 0n:
      f
    case 1n+p:
      refill(p, put(f, at), wrap(U32.inc(at), m), m)

def pr_fin(+r: U32, c: U32, +size: U32, p: L.Fast<U32> & U32) -> St:
  (f, n) = p
  S{r, B.mix(c, n), 0, refill(U32.to_nat(size), f, 0, capof(size))}

def do_purge_refill(st: St, +size: U32) -> St:
  S{r0, c, o, f} = st
  pr_fin(B.lcg(r0), c, size, L.purge(~U32, f))

def ev_of(x: Result<&2, &2, String, U32>) -> U32:
  match x:
    case Fail{e}:
      0
    case Done{e}:
      e

def wrap_add(+o: U32, +e: U32, +m: U32) -> U32:
  U32.mod(U32.add(o, e), m)

def rb_back(+r: U32, c: U32, +o: U32, +e: U32, +size: U32, p: L.Fast<U32> & Result<&2, &2, String, U32>) -> St:
  (f, x) = p
  S{r, B.mix(c, ev_of(x)), wrap_add(o, e, capof(size)), refill(U32.to_nat(e), f, o, capof(size))}

def rb_down(+r: U32, c: U32, +o: U32, +t: U32, +size: U32, p: L.Fast<U32> & Result<&2, &2, String, U32>) -> St:
  (f, +x) = p
  rb_back(r, rs_code(c, t, x), o, ev_of(x), size, L.resize(~U32, f, capof(size)))

def do_resize_back(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +t = U32.inc(U32.mod(r, capof(size)))
  rb_down(r, c, o, t, size, L.resize(~U32, f, t))

def do_null(st: St) -> St:
  S{r0, c, o, f} = st
  +r = B.lcg(r0)
  S{r, B.mix(c, r), o, f}

# ---- loops ----

def loop_add(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_add(p, n, do_add(st, n))

def loop_get(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_get(p, n, do_get(st, n))

def loop_peek(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_peek(p, n, do_peek(st, n))

def loop_contains(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_contains(p, n, do_contains(st, n))

def loop_remove(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_remove(p, n, do_remove(st, n))

def loop_purge(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_purge(p, do_purge(st))

def loop_resize(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_resize(p, n, do_resize(st, n))

def loop_keys(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_keys(p, do_keys(st))

def loop_len(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_len(p, do_len(st))

def loop_new(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_new(p, n, do_new(st, n))

def loop_ra(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_ra(p, n, do_remove_add(st, n))

def loop_pr(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_pr(p, n, do_purge_refill(st, n))

def loop_rb(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_rb(p, n, do_resize_back(st, n))

def loop_null(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_null(p, do_null(st))

def measured(+op: U32, +k: Nat, +n: U32, st: St) -> St:
  match op:
    case 0:
      loop_add(k, n, st)
    case 1:
      loop_get(k, n, st)
    case 2:
      loop_peek(k, n, st)
    case 3:
      loop_contains(k, n, st)
    case 4:
      loop_remove(k, n, st)
    case 5:
      loop_purge(k, st)
    case 6:
      loop_resize(k, n, st)
    case 7:
      loop_keys(k, st)
    case 8:
      loop_len(k, st)
    case 9:
      loop_new(k, n, st)
    case 10:
      loop_ra(k, n, st)
    case 11:
      loop_pr(k, n, st)
    case 12:
      loop_rb(k, n, st)
    case _:
      loop_null(k, st)

# ---- build / settle / drain ----

def init(+seed: U32, +size: U32) -> St:
  S{seed, 0, 0, refill(U32.to_nat(size), L.init(~U32, capof(size)), 0, capof(size))}

def settle(st: St) -> St:
  S{r, c, o, f} = st
  fin_keys(r, c, o, L.keys(~U32, f, now()))

def lo_hi(c: U32, p: U32 & U32) -> U32:
  (lo, hi) = p
  B.mix(B.mix(c, lo), hi)

def fold_metrics(c: U32, +m: T.Metrics) -> U32:
  lo_hi(lo_hi(lo_hi(lo_hi(lo_hi(c, W.unpack(T.inserts(m))), W.unpack(T.evictions(m))), W.unpack(T.removals(m))), W.unpack(T.hits(m))), W.unpack(T.misses(m)))

def drain_m(c: U32, p: L.Fast<U32> & T.Metrics) -> U32:
  (f, +m) = p
  fold_metrics(c, m)

def drain_n(c: U32, p: L.Fast<U32> & U32) -> U32:
  (f, n) = p
  drain_m(B.mix(c, n), L.metrics(~U32, f))

def drain_loop(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, n, do_peek(st, n))

def drain_end(st: St) -> U32:
  S{r, c, o, f} = st
  drain_n(c, L.len(~U32, f))

# The drain is independent of the measured operation: sixteen peeks, the
# length and the five metrics (so every side effect on them is checked).
def drain(+size: U32, st: St) -> U32:
  S{+r, c, o, f} = st
  drain_end(drain_loop(16n, size, S{r, B.mix(c, r), o, f}))

def round(+op: U32, +size: U32, +k: Nat, +seed: U32) -> U32:
  drain(size, measured(op, k, size, settle(init(seed, size))))

def reps_go(reps: Nat, +op: U32, +size: U32, +k: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, seed, B.mix(acc, round(op, size, k, U32.add(seed, U32.from_nat(p)))))

def regions(+g: B.Args, +k: Nat) -> U32:
  reps_go(U32.to_nat(B.a_reps(g)), B.a_op(g), B.a_size(g), k, B.a_seed(g), 0)

def kof(+g: B.Args) -> Nat:
  U32.to_nat(B.a_count(g))

def run_a(+g: B.Args) -> U32:
  regions(g, Nat.add(kof(g), kof(g)))

def run_b(+g: B.Args) -> U32:
  regions(g, kof(g))

def run_c(+g: B.Args) -> U32:
  regions(g, 0n)

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
