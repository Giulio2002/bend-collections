import Base
import ./common.bend as B
import ../../src/containers/lru.bend as L
import ../../src/math/u64.bend as W

# Native benchmark driver for src/lru.bend (open-addressing table plus an
# indexed doubly linked recency arena).
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
# 13 capacity       folds the capacity
# 14 set_lifetime   sets the lifetime to the drawn nanosecond count; folds it
#                   and the length
# 15 metrics        folds the five 64-bit counters (ten U32 limbs)
# 16 expiry         the round sets a one millisecond lifetime once, before the
#                   measured region; every step then adds key i at stamp 0
#                   (deadline 1) and gets it back at stamp 2, so the read
#                   finds it EXPIRED, drops it and answers a miss (composite:
#                   add + get)
# 17 remove_seq     isolated removal of the distinct, present key (o + j) mod
#                   cap from the cache the round prepared; used only with
#                   2 * count <= size, so region A never empties the cache
# 18 purge (pool)  ISOLATED purge: both regions build the SAME pool of
#                   2 * count full caches, then purge k of them; the
#                   preparation cancels in A - B and every measured purge
#                   empties a freshly built, full cache
# 19 resize (pool)  ISOLATED shrink over the same pool: resize cache j to
#                   1 + lcg mod cap, folding the target and the evictions
# else  value-stream step only (the A/B/C control)

type St is Type:
  S{rng: U32, chk: U32, o: U32, c: L.LRU<&2, U32>}

# Key i is the one-character String Chr{65536 + i}: a valid Unicode scalar
# for every benchmark size (the supplementary planes have no surrogates).
def key(+i: U32) -> String:
  SCon{Chr{U32.add(i, 65536)}, SNil{}}

def now() -> W.U64:
  W.U64{0, 0}

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

# ---- metric folding (shared by the `metrics` row and the drain) ----

def lo_hi(c: U32, p: U32 & U32) -> U32:
  (lo, hi) = p
  B.mix(B.mix(c, lo), hi)

# ---- measured operations ----

def fold_keys(ks: List<&2, String>, c: U32) -> U32:
  match ks:
    case Nil{}:
      c
    case Con{k, t}:
      fold_keys(t, B.mix(c, key_code(k)))

def fin_bit(+r: U32, c: U32, +o: U32, p: L.LRU<&2, U32> & Bool) -> St:
  (f, b) = p
  S{r, B.mix(c, bit(b)), o, f}

def fin_val(+r: U32, c: U32, +o: U32, p: L.LRU<&2, U32> & Maybe<&2, U32>) -> St:
  (f, m) = p
  S{r, B.mix(c, val_or(m)), o, f}

def fin_num(+r: U32, c: U32, +o: U32, p: L.LRU<&2, U32> & U32) -> St:
  (f, x) = p
  S{r, B.mix(c, x), o, f}

def draw(+r: U32, +size: U32) -> U32:
  U32.mod(r, U32.inc(size))

def do_add(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  fin_bit(r, c, o, L.add(&2, U32, f, key(i), U32.inc(i), now()))

def do_get(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.get(U32, f, key(draw(r, size)), now()))

def do_peek(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.peek(U32, f, key(draw(r, size)), now()))

def do_contains(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_bit(r, c, o, L.contains(&2, U32, f, key(draw(r, size)), now()))

def do_remove(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  fin_val(r, c, o, L.remove(&2, U32, f, key(draw(r, size))))

def do_purge(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_num(B.lcg(r0), c, o, L.purge(&2, U32, f))

def rs_code(c: U32, +t: U32, x: Result<&2, &2, String, U32>) -> U32:
  match x:
    case Fail{e}:
      B.mix(c, 4294967295)
    case Done{e}:
      B.mix(B.mix(c, t), e)

def fin_rs(+r: U32, c: U32, +o: U32, +t: U32, p: L.LRU<&2, U32> & Result<&2, &2, String, U32>) -> St:
  (f, x) = p
  S{r, rs_code(c, t, x), o, f}

def do_resize(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +t = draw(r, size)
  fin_rs(r, c, o, t, L.resize(&2, U32, f, t))

def fin_keys(+r: U32, c: U32, +o: U32, p: L.LRU<&2, U32> & List<&2, String>) -> St:
  (f, ks) = p
  S{r, fold_keys(ks, c), o, f}

def do_keys(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_keys(B.lcg(r0), c, o, L.keys(&2, U32, f, now()))

def do_len(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_num(B.lcg(r0), c, o, L.len(&2, U32, f))

def new_len(c: U32, p: L.LRU<&2, U32> & U32) -> U32:
  (g, n) = p
  B.mix(c, n)

def new_cap(c: U32, p: L.LRU<&2, U32> & U32) -> U32:
  (g, k) = p
  new_len(B.mix(c, k), L.len(&2, U32, g))

def new_code(c: U32, x: L.Made<&2, U32>) -> U32:
  match x:
    case L.Rejected{e}:
      B.mix(c, 4294967295)
    case L.Made{g}:
      new_cap(c, L.capacity(&2, U32, g))

def do_new(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  S{B.lcg(r0), new_code(c, L.new(&2, U32, size)), o, f}

def drop_bit(p: L.LRU<&2, U32> & Bool) -> L.LRU<&2, U32>:
  (f, b) = p
  f

def put(f: L.LRU<&2, U32>, +i: U32) -> L.LRU<&2, U32>:
  drop_bit(L.add(&2, U32, f, key(i), U32.inc(i), now()))

def ra_fin(+r: U32, c: U32, +o: U32, +i: U32, p: L.LRU<&2, U32> & Maybe<&2, U32>) -> St:
  (f, m) = p
  fin_bit(r, B.mix(c, val_or(m)), o, L.add(&2, U32, f, key(i), U32.inc(i), now()))

# add keys (from + j) mod m for j = 0 .. k-1
def do_remove_add(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  ra_fin(r, c, o, i, L.remove(&2, U32, f, key(i)))

def wrap(+x: U32, +m: U32) -> U32:
  L.pick(U32.is_lt(x, m), x, 0)

def refill(k: Nat, f: L.LRU<&2, U32>, +at: U32, +m: U32) -> L.LRU<&2, U32>:
  match k:
    case 0n:
      f
    case 1n+p:
      refill(p, put(f, at), wrap(U32.inc(at), m), m)

def pr_fin(+r: U32, c: U32, +size: U32, p: L.LRU<&2, U32> & U32) -> St:
  (f, n) = p
  S{r, B.mix(c, n), 0, refill(U32.to_nat(size), f, 0, capof(size))}

def do_purge_refill(st: St, +size: U32) -> St:
  S{r0, c, o, f} = st
  pr_fin(B.lcg(r0), c, size, L.purge(&2, U32, f))

def ev_of(x: Result<&2, &2, String, U32>) -> U32:
  match x:
    case Fail{e}:
      0
    case Done{e}:
      e

def wrap_add(+o: U32, +e: U32, +m: U32) -> U32:
  U32.mod(U32.add(o, e), m)

def rb_back(+r: U32, c: U32, +o: U32, +e: U32, +size: U32, p: L.LRU<&2, U32> & Result<&2, &2, String, U32>) -> St:
  (f, x) = p
  S{r, B.mix(c, ev_of(x)), wrap_add(o, e, capof(size)), refill(U32.to_nat(e), f, o, capof(size))}

# rs_code and ev_of in one pass: sharing (`+`) the Result would make the
# runtime reference-count every Result and, through Fail, every String.
def rs_pair(c: U32, +t: U32, x: Result<&2, &2, String, U32>) -> U32 & U32:
  match x:
    case Fail{e}:
      (B.mix(c, 4294967295), 0)
    case Done{+e}:
      (B.mix(B.mix(c, t), e), e)

def rb_mid(+r: U32, +o: U32, +size: U32, f: L.LRU<&2, U32>, ce: U32 & U32) -> St:
  (c2, +e) = ce
  rb_back(r, c2, o, e, size, L.resize(&2, U32, f, capof(size)))

def rb_down(+r: U32, c: U32, +o: U32, +t: U32, +size: U32, p: L.LRU<&2, U32> & Result<&2, &2, String, U32>) -> St:
  (f, x) = p
  rb_mid(r, o, size, f, rs_pair(c, t, x))

def do_resize_back(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +t = U32.inc(U32.mod(r, capof(size)))
  rb_down(r, c, o, t, size, L.resize(&2, U32, f, t))

def do_null(st: St) -> St:
  S{r0, c, o, f} = st
  +r = B.lcg(r0)
  S{r, B.mix(c, r), o, f}


# ---- operations added for full public API coverage (selectors 13-17) ----
#
# 13 capacity        folds the capacity (an O(1) field read)
# 14 set_lifetime    sets the lifetime to the drawn nanosecond count and folds
#                    it together with the (unchanged) length. `set_lifetime`
#                    is an O(1) field write whose EFFECT is what selector 16
#                    measures and what the conformance suite checks; the cache
#                    is threaded on, so neither side can drop the call.
# 15 metrics         folds all five 64-bit counters (ten U32 limbs)
# 16 expiry          the round sets a one MILLISECOND lifetime ONCE, outside
#                    the measured step; every step then adds key i at stamp 0
#                    (deadline 1) and reads it back at stamp 2, so the read
#                    finds an EXPIRED entry, drops it (a removal) and answers
#                    a miss. This is the expiry path of `read`, which no other
#                    row reaches; it is a composite (add + get) and is
#                    labelled as one.
# 17 remove_seq      ISOLATED removal: step j removes key (o + j) mod cap,
#                    a distinct key that is still present, from the nonempty
#                    cache the round prepared before the measured region.
#                    The row is only used with 2 * count <= size, so region A
#                    (2k removals) never empties the cache and every measured
#                    removal in A - B really unlinks a live entry.

def do_capacity(st: St) -> St:
  S{r0, c, +o, f} = st
  fin_num(B.lcg(r0), c, o, L.capacity(&2, U32, f))

def sl_fin(+r: U32, c: U32, +o: U32, +ns: U32, p: L.LRU<&2, U32> & U32) -> St:
  (f, n) = p
  S{r, B.mix(B.mix(c, ns), n), o, f}

def do_set_lifetime(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +ns = draw(r, size)
  sl_fin(r, c, o, ns, L.len(&2, U32, L.set_lifetime_packed(&2, U32, f, W.U64{ns, 0})))

def lstep_fin(c: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, x) = r
  (a, B.mix(c, x))

def lstep(+i: U32, st: Array<U32> & U32) -> Array<U32> & U32:
  (a, c) = st
  lstep_fin(c, Array.get(U32, a, i))

def lsnd(st: Array<U32> & U32) -> U32:
  (a, c) = st
  c

def fold_limbs(c: U32, a: Array<U32>) -> U32:
  lsnd(lstep(25, lstep(24, lstep(23, lstep(22, lstep(21, lstep(20, lstep(19, lstep(18, lstep(17, lstep(16, (a, c))))))))))))

def met_fin(+r: U32, c: U32, +o: U32, p: L.LRU<&2, U32> & Array<U32>) -> St:
  (f, a) = p
  S{r, fold_limbs(c, a), o, f}

def do_metrics(st: St) -> St:
  S{r0, c, +o, f} = st
  met_fin(B.lcg(r0), c, o, L.counters(&2, U32, f))

def stamp(+t: U32) -> W.U64:
  W.U64{t, 0}

def set_ttl1(st: St) -> St:
  S{r, c, o, f} = st
  S{r, c, o, L.set_lifetime_packed(&2, U32, f, W.U64{1000000, 0})}

def ex_get(+r: U32, c: U32, +o: U32, +i: U32, p: L.LRU<&2, U32> & Bool) -> St:
  (f, b) = p
  fin_val(r, B.mix(c, bit(b)), o, L.get(U32, f, key(i), stamp(2)))

def do_expiry(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  +r = B.lcg(r0)
  +i = draw(r, size)
  ex_get(r, c, o, i, L.add(&2, U32, f, key(i), U32.inc(i), stamp(0)))

def rsq_fin(+r: U32, c: U32, +o: U32, +m: U32, p: L.LRU<&2, U32> & Maybe<&2, U32>) -> St:
  (f, v) = p
  S{r, B.mix(c, val_or(v)), wrap(U32.inc(o), m), f}

def do_remove_seq(st: St, +size: U32) -> St:
  S{r0, c, +o, f} = st
  rsq_fin(B.lcg(r0), c, o, capof(size), L.remove(&2, U32, f, key(o)))


# ---- selectors 18/19: ISOLATED purge and resize over a prepared pool ----
#
# A purge empties its cache and a shrink evicts from it, so measuring k of
# them in region B and 2k in region A only works if every measured call gets
# its OWN full cache. Both regions therefore build the SAME pool of
# 2 * count independent full caches (the pool size is the row's `count`, NOT
# the region's k), so the whole preparation cancels in A - B, and then region
# A destroys 2k of them while region B destroys k: the difference is exactly
# k destructive calls, each on a freshly prepared, nonempty cache, and no
# call ever hits an already emptied or already shrunk one. The caches that a
# region does not reach are dropped unmeasured.
#
# The preparation is much more expensive than the operation it isolates, so
# these rows need long regions (and therefore modest sizes) to keep A - B
# above the harness's noise floor; that is the price of isolation and it is
# recorded with the rows.

def pool_one(+size: U32) -> L.LRU<&2, U32>:
  refill(U32.to_nat(size), L.init(&2, U32, capof(size)), 0, capof(size))

def pool_go(m: Nat, +size: U32, acc: List<&1, L.LRU<&2, U32>>) -> List<&1, L.LRU<&2, U32>>:
  match m:
    case 0n:
      acc
    case 1n+p:
      pool_go(p, size, Con{pool_one(size), acc})

# every element is affine and simply dropped
def drop_pool(xs: List<&1, L.LRU<&2, U32>>) -> Unit:
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      drop_pool(t)

type PSt is Type:
  P{rng: U32, chk: U32, pool: List<&1, L.LRU<&2, U32>>}

def drop_cache(f: L.LRU<&2, U32>, rest: List<&1, L.LRU<&2, U32>>) -> List<&1, L.LRU<&2, U32>>:
  rest

def pp_one(+r: U32, c: U32, rest: List<&1, L.LRU<&2, U32>>, p: L.LRU<&2, U32> & U32) -> PSt:
  (f, n) = p
  P{r, B.mix(c, n), drop_cache(f, rest)}

def pp_pick(+r: U32, c: U32, xs: List<&1, L.LRU<&2, U32>>) -> PSt:
  match xs:
    case Nil{}:
      P{r, B.mix(c, 4294967295), Nil{}}
    case Con{h, t}:
      pp_one(r, c, t, L.purge(&2, U32, h))

def pp_step(ps: PSt) -> PSt:
  P{r0, c, pool} = ps
  pp_pick(B.lcg(r0), c, pool)

def pool_purge(k: Nat, ps: PSt) -> PSt:
  match k:
    case 0n:
      ps
    case 1n+j:
      pool_purge(j, pp_step(ps))

def pr_one(+r: U32, c: U32, +t: U32, rest: List<&1, L.LRU<&2, U32>>, p: L.LRU<&2, U32> & Result<&2, &2, String, U32>) -> PSt:
  (f, x) = p
  P{r, rs_code(c, t, x), drop_cache(f, rest)}

def pr_go(+r: U32, c: U32, +t: U32, rest: List<&1, L.LRU<&2, U32>>, h: L.LRU<&2, U32>) -> PSt:
  pr_one(r, c, t, rest, L.resize(&2, U32, h, t))

def pr_pick(+r: U32, c: U32, +size: U32, xs: List<&1, L.LRU<&2, U32>>) -> PSt:
  match xs:
    case Nil{}:
      P{r, B.mix(c, 4294967295), Nil{}}
    case Con{h, t}:
      pr_go(r, c, U32.inc(U32.mod(r, capof(size))), t, h)

def pz_step(+size: U32, ps: PSt) -> PSt:
  P{r0, c, pool} = ps
  pr_pick(B.lcg(r0), c, size, pool)

def pool_resize(k: Nat, +size: U32, ps: PSt) -> PSt:
  match k:
    case 0n:
      ps
    case 1n+j:
      pool_resize(j, size, pz_step(size, ps))

def pool_end(+r: U32, c: U32, +o: U32, f: L.LRU<&2, U32>, z: Unit) -> St:
  match z:
    case Unit{}:
      S{r, c, o, f}

def pool_fin(+o: U32, f: L.LRU<&2, U32>, ps: PSt) -> St:
  P{r, c, pool} = ps
  pool_end(r, c, o, f, drop_pool(pool))

def run_pool_purge(+k: Nat, +m: Nat, +size: U32, st: St) -> St:
  S{r, c, +o, f} = st
  pool_fin(o, f, pool_purge(k, P{r, c, pool_go(Nat.add(m, m), size, Nil{})}))

def run_pool_resize(+k: Nat, +m: Nat, +size: U32, st: St) -> St:
  S{r, c, +o, f} = st
  pool_fin(o, f, pool_resize(k, size, P{r, c, pool_go(Nat.add(m, m), size, Nil{})}))

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

def loop_capacity(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_capacity(p, do_capacity(st))

def loop_set_lifetime(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_set_lifetime(p, n, do_set_lifetime(st, n))

def loop_metrics(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_metrics(p, do_metrics(st))

def loop_expiry(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_expiry(p, n, do_expiry(st, n))

def loop_remove_seq(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      loop_remove_seq(p, n, do_remove_seq(st, n))

def measured(+op: U32, +k: Nat, +m: Nat, +n: U32, st: St) -> St:
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
    case 13:
      loop_capacity(k, st)
    case 14:
      loop_set_lifetime(k, n, st)
    case 15:
      loop_metrics(k, st)
    case 16:
      loop_expiry(k, n, set_ttl1(st))
    case 17:
      loop_remove_seq(k, n, st)
    case 18:
      run_pool_purge(k, m, n, st)
    case 19:
      run_pool_resize(k, m, n, st)
    case _:
      loop_null(k, st)

# ---- build / settle / drain ----

def init(+seed: U32, +size: U32) -> St:
  S{seed, 0, 0, refill(U32.to_nat(size), L.init(&2, U32, capof(size)), 0, capof(size))}

def settle(st: St) -> St:
  S{r, c, o, f} = st
  fin_keys(r, c, o, L.keys(&2, U32, f, now()))

def drain_m(c: U32, p: L.LRU<&2, U32> & Array<U32>) -> U32:
  (f, a) = p
  fold_limbs(c, a)

def drain_n(c: U32, p: L.LRU<&2, U32> & U32) -> U32:
  (f, n) = p
  drain_m(B.mix(c, n), L.counters(&2, U32, f))

def drain_loop(k: Nat, +n: U32, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+p:
      drain_loop(p, n, do_peek(st, n))

def drain_end(st: St) -> U32:
  S{r, c, o, f} = st
  drain_n(c, L.len(&2, U32, f))

# The drain is independent of the measured operation: sixteen peeks, the
# length and the five metrics (so every side effect on them is checked).
def drain(+size: U32, st: St) -> U32:
  S{+r, c, o, f} = st
  drain_end(drain_loop(16n, size, S{r, B.mix(c, r), o, f}))

def round(+op: U32, +size: U32, +k: Nat, +m: Nat, +seed: U32) -> U32:
  drain(size, measured(op, k, m, size, settle(init(seed, size))))

def reps_go(reps: Nat, +op: U32, +size: U32, +k: Nat, +m: Nat, +seed: U32, acc: U32) -> U32:
  match reps:
    case 0n:
      acc
    case 1n+ +p:
      reps_go(p, op, size, k, m, seed, B.mix(acc, round(op, size, k, m, U32.add(seed, U32.from_nat(p)))))

# `m` is the row's `count`, identical in every region: the pooled selectors
# 18/19 build 2 * m caches whatever the region's k is.
def regions(+g: B.Args, +k: Nat) -> U32:
  reps_go(U32.to_nat(B.a_reps(g)), B.a_op(g), B.a_size(g), k, U32.to_nat(B.a_count(g)), B.a_seed(g), 0)

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
