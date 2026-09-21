import Base
import ../../src/lru/fast.bend as F
import ../../src/lru/cache.bend as C
import ../../src/lru/model.bend as T
import ../../src/lru/time.bend as Time
import ../../src/lru/wide.bend as W

# Behavioural differential: src/lru/fast.bend (native Map + indexed doubly
# linked recency arena) against src/lru/cache.bend (the natively compilable
# copy of the retained reference/lru cache, list recency).
#
# A pseudo-random sequence of add / get / peek / contains / remove / purge /
# keys / len / set_lifetime / clock-advance requests is run on both caches
# (capacity 3, keys drawn from six one-character Strings, lifetimes 0, 5 ms
# and 20 ms, a clock that advances 0..9 ms), and after EVERY request the
# returned observation, the length, the key order and all five 64-bit metrics
# are compared. The program prints the number of steps and the number of
# mismatching steps; `tools/validate.py` requires the second to be 0.
#
# Purge and Keys follow the retained PUBLIC semantics (reference/lru/src/
# public.bend): purge replaces the table and clears the metrics; Keys first
# removes the oldest expired prefix (one removal each) with the current
# clock.

type TS is Type:
  TS{rng: U32, now: U32, steps: U32, bad: U32, f: F.Fast<U32>, c: C.Cache<String, U32>}

def ident(s: String) -> String:
  s

def key(+i: U32) -> String:
  SCon{Chr{U32.add(65, i)}, SNil{}}

def i64(+x: U32) -> T.Int64:
  T.I64{W.pack(x, 0)}

def stamp(+x: U32) -> F.Stamp:
  F.ST{x, 0}

def lcg(+s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def pick3(+r: U32) -> U32:
  U32.mod(U32.shrn(r, 8n), 6)

def bump_bad(+bad: U32, same: Bool) -> U32:
  match same:
    case True{}:
      bad
    case False{}:
      U32.inc(bad)

def mval(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{v}:
      U32.inc(v)

# The retained Step's `flag` says whether `item` is a result: an expired read
# returns the removed entry with flag False (a miss), exactly as the public
# layer reads it (reference/lru/src/public.bend `item_value`).
def eval(m: Maybe<&2, T.Entry<String, U32>>, present: Bool) -> U32:
  match m present:
    case Some{T.Item{k, v, d}} True{}:
      U32.inc(v)
    case x y:
      0

def bbit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def mix(c: U32, v: U32) -> U32:
  U32.add(U32.mul(c, 31), v)

def lohi(c: U32, p: U32 & U32) -> U32:
  (lo, hi) = p
  mix(mix(c, lo), hi)

def msum(+m: T.Metrics) -> U32:
  lohi(lohi(lohi(lohi(lohi(0, W.unpack(T.inserts(m))), W.unpack(T.evictions(m))), W.unpack(T.removals(m))), W.unpack(T.hits(m))), W.unpack(T.misses(m)))

def fold_keys(ks: List<&2, String>, c: U32) -> U32:
  match ks:
    case Nil{}:
      c
    case Con{SCon{Chr{x}, t}, rest}:
      fold_keys(rest, mix(c, x))
    case Con{SNil{}, rest}:
      fold_keys(rest, mix(c, 999))

def fold_entries(es: List<&2, T.Entry<String, U32>>, c: U32) -> U32:
  match es:
    case Nil{}:
      c
    case Con{T.Item{SCon{Chr{x}, t}, v, d}, rest}:
      fold_entries(rest, mix(c, x))
    case Con{T.Item{SNil{}, v, d}, rest}:
      fold_entries(rest, mix(c, 999))

# ---- the observable state of each side after a step ----

def f_len(p: F.Fast<U32> & U32) -> F.Fast<U32> & U32:
  p

def f_state_m(+n: U32, p: F.Fast<U32> & T.Metrics) -> F.Fast<U32> & U32:
  (f, +m) = p
  (f, mix(n, msum(m)))

def f_state_n(p: F.Fast<U32> & U32) -> F.Fast<U32> & U32:
  (f, +n) = p
  f_state_m(n, F.metrics(~U32, f))

def f_order(ks: List<&2, String>) -> U32:
  fold_keys(ks, 7)

# fast: length and metrics (the order is compared by the Keys request)
def f_state(f: F.Fast<U32>) -> F.Fast<U32> & U32:
  f_state_n(F.len(~U32, f))

def c_state(+c: C.Cache<String, U32>) -> U32:
  mix(U32.from_nat(C.len(String, U32, c)), msum(C.metrics(String, U32, c)))

# ---- compare after one request ----

def finish(+r: U32, +now: U32, +steps: U32, +bad: U32, +fo: U32, +co: U32, p: F.Fast<U32> & U32, +c: C.Cache<String, U32>) -> TS:
  (f, +fs) = p
  TS{r, now, U32.inc(steps), bump_bad(bad, Bool.and(U32.is_eq(fo, co), U32.is_eq(fs, c_state(c)))), f, c}

def done(+r: U32, +now: U32, +steps: U32, +bad: U32, +fo: U32, +co: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  finish(r, now, steps, bad, fo, co, f_state(f), c)

# ---- requests ----

def rq_add_c(+r: U32, +now: U32, +steps: U32, +bad: U32, s: C.Step<String, U32>, p: F.Fast<U32> & Bool) -> TS:
  C.Out{+c, item, flag, evs} = s
  (f, b) = p
  done(r, now, steps, bad, bbit(b), bbit(flag), f, c)

def rq_add(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +k = pick3(r)
  rq_add_c(r, now, steps, bad, C.add(String, U32, ident, c, key(k), U32.mul(k, 10), i64(now)), F.add(~U32, f, key(k), U32.mul(k, 10), stamp(now)))

def rq_read_c(+r: U32, +now: U32, +steps: U32, +bad: U32, s: C.Step<String, U32>, p: F.Fast<U32> & Maybe<&2, U32>) -> TS:
  C.Out{+c, item, flag, evs} = s
  (f, m) = p
  done(r, now, steps, bad, mval(m), eval(item, flag), f, c)

def rq_get(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +k = pick3(r)
  rq_read_c(r, now, steps, bad, C.get(String, U32, ident, c, key(k), i64(now)), F.get(~U32, f, key(k), stamp(now)))

def rq_peek(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +k = pick3(r)
  rq_read_c(r, now, steps, bad, C.peek(String, U32, ident, c, key(k), i64(now)), F.peek(~U32, f, key(k), stamp(now)))

def rq_has_c(+r: U32, +now: U32, +steps: U32, +bad: U32, s: C.Step<String, U32>, p: F.Fast<U32> & Bool) -> TS:
  C.Out{+c, item, flag, evs} = s
  (f, b) = p
  done(r, now, steps, bad, bbit(b), bbit(flag), f, c)

def rq_contains(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +k = pick3(r)
  rq_has_c(r, now, steps, bad, C.peek(String, U32, ident, c, key(k), i64(now)), F.contains(~U32, f, key(k), stamp(now)))

def rq_remove(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +k = pick3(r)
  rq_read_c(r, now, steps, bad, C.remove(String, U32, ident, c, key(k)), F.remove(~U32, f, key(k)))

# the retained public purge
def c_purge(c: C.Cache<String, U32>) -> C.Cache<String, U32>:
  C.State{cap, table, order, life, counts, cb} = c
  C.State{cap, Map.new(&2, Maybe<&2, T.Entry<String, U32>>), Nil{}, life, T.zero_metrics(), cb}

def rq_purge_f(+r: U32, +now: U32, +steps: U32, +bad: U32, +c: C.Cache<String, U32>, p: F.Fast<U32> & U32) -> TS:
  (f, n) = p
  done(r, now, steps, bad, 0, 0, f, c)

def rq_purge(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  rq_purge_f(r, now, steps, bad, c_purge(c), F.purge(~U32, f))

# the retained public Keys: remove the oldest expired prefix with `now`
def c_exp_if(+c: C.Cache<String, U32>, go: Bool) -> C.Cache<String, U32> & Bool:
  match go:
    case False{}:
      (c, False{})
    case True{}:
      (C.step_cache(String, U32, C.remove_oldest(String, U32, c, False{})), True{})

def c_exp_pick(+now: U32, +c: C.Cache<String, U32>, e: Maybe<&2, T.Entry<String, U32>>) -> C.Cache<String, U32> & Bool:
  match e:
    case None{}:
      (c, False{})
    case Some{T.Item{k, v, +d}}:
      c_exp_if(c, Bool.and(Bool.not(Time.is_zero(d)), Time.expired(d, i64(now))))

def c_exp_step(+now: U32, +c: C.Cache<String, U32>) -> C.Cache<String, U32> & Bool:
  c_exp_pick(now, c, C.oldest_entry(String, U32, c))

def c_expire(fuel: Nat, +now: U32, r: C.Cache<String, U32> & Bool) -> C.Cache<String, U32>:
  match fuel r:
    case 0n Tuple{c, more}:
      c
    case 1n+p Tuple{c, False{}}:
      c
    case 1n+p Tuple{+c, True{}}:
      c_expire(p, now, c_exp_step(now, c))

def rq_keys_f(+r: U32, +now: U32, +steps: U32, +bad: U32, +c: C.Cache<String, U32>, p: F.Fast<U32> & List<&2, String>) -> TS:
  (f, ks) = p
  done(r, now, steps, bad, f_order(ks), fold_entries(C.entries(String, U32, c), 7), f, c)

def rq_keys(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  rq_keys_f(r, now, steps, bad, c_expire(C.len(String, U32, c), now, (c, True{})), F.keys(~U32, f, stamp(now)))

def rq_len_f(+r: U32, +now: U32, +steps: U32, +bad: U32, +c: C.Cache<String, U32>, p: F.Fast<U32> & U32) -> TS:
  (f, +n) = p
  done(r, now, steps, bad, n, U32.from_nat(C.len(String, U32, c)), f, c)

def rq_len(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  rq_len_f(r, now, steps, bad, c, F.len(~U32, f))

def life_sel(+x: U32) -> U32:
  match x:
    case 0:
      0
    case 1:
      5000000
    case _:
      20000000

def life_of(+r: U32) -> U32:
  life_sel(U32.mod(U32.shrn(r, 12n), 3))

def rq_life(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  +ns = life_of(r)
  done(r, now, steps, bad, 0, 0, F.set_lifetime(~U32, f, i64(ns)), C.set_lifetime(String, U32, c, i64(ns)))

def rq_tick(+r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  done(r, U32.add(now, U32.mod(U32.shrn(r, 16n), 10)), steps, bad, 0, 0, f, c)

def request(+sel: U32, +r: U32, +now: U32, +steps: U32, +bad: U32, f: F.Fast<U32>, +c: C.Cache<String, U32>) -> TS:
  match sel:
    case 0:
      rq_add(r, now, steps, bad, f, c)
    case 1:
      rq_add(r, now, steps, bad, f, c)
    case 2:
      rq_get(r, now, steps, bad, f, c)
    case 3:
      rq_peek(r, now, steps, bad, f, c)
    case 4:
      rq_contains(r, now, steps, bad, f, c)
    case 5:
      rq_remove(r, now, steps, bad, f, c)
    case 6:
      rq_keys(r, now, steps, bad, f, c)
    case 7:
      rq_len(r, now, steps, bad, f, c)
    case 8:
      rq_life(r, now, steps, bad, f, c)
    case 9:
      rq_tick(r, now, steps, bad, f, c)
    case 10:
      rq_tick(r, now, steps, bad, f, c)
    case 11:
      rq_get(r, now, steps, bad, f, c)
    case _:
      rq_purge(r, now, steps, bad, f, c)

def one(t: TS) -> TS:
  TS{r0, +now, +steps, +bad, f, +c} = t
  +r = lcg(r0)
  request(U32.mod(U32.shrn(r, 20n), 13), r, now, steps, bad, f, c)

def run(k: Nat, t: TS) -> TS:
  match k:
    case 0n:
      t
    case 1n+p:
      run(p, one(t))

def start_c(x: Result<&2, &2, String, C.Cache<String, U32>>) -> C.Cache<String, U32>:
  match x:
    case Fail{e}:
      C.init(String, U32, 3n)
    case Done{c}:
      c

def start_f(x: F.Made<U32>) -> F.Fast<U32>:
  match x:
    case F.Rejected{e}:
      F.init(~U32, 3)
    case F.Made{f}:
      f

def report(t: TS) -> String:
  TS{r, now, steps, bad, f, c} = t
  String.append("steps ", String.append(U32.show(steps), String.append(" mismatches ", U32.show(bad))))

# Constructor agreement: both sides accept/reject the same capacities.
def made_code(x: F.Made<U32>) -> U32:
  match x:
    case F.Rejected{e}:
      0
    case F.Made{f}:
      1

def res_code(x: Result<&2, &2, String, C.Cache<String, U32>>) -> U32:
  match x:
    case Fail{e}:
      0
    case Done{c}:
      1

def ctor_bad(+cap: U32) -> U32:
  bump_bad(0, U32.is_eq(made_code(F.new(~U32, cap)), res_code(C.new(String, U32, cap))))

def seeds(k: Nat, +seed: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+p:
      seeds(p, U32.add(seed, 7919), String.append(acc, String.append("\n", report(run(3000n, TS{seed, 1000, 0, 0, start_f(F.new(~U32, 3)), start_c(C.new(String, U32, 3))})))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(seeds(8n, 12345, String.append("constructor mismatches ", U32.show(U32.add(U32.add(ctor_bad(0), ctor_bad(1)), U32.add(ctor_bad(3), ctor_bad(4294967295)))))))
