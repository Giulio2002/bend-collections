import Base
import ../math/u64.bend as W
import ../math/hash.bend as HS
import ./hash_table.bend as H

# LRU cache, performance layout (experiment). Same observable semantics as
# src/lru/fast.bend and benchmarks/native/lru.c: capacity eviction of the
# oldest entry, lifetimes, five 64-bit metrics, touch-on-get, no-touch peek
# and contains, expired entries dropped (as removals) when a read finds them.
#
# Layout, chosen for Bend 2's native backend:
#   - every record field is a register word, so the state is kept NARROW:
#     F{cap, n, head, tail, free, m, tab, ks, ents, lk} is ten words;
#   - cold scalars and the counters live in one packed Array<U32> `m`;
#   - `tab` is the hash map's bucket table (src/containers/hash_table.bend):
#     (check word, link) pairs, linear probing over a power-of-two size, load
#     <= 1/2, backward-shift delete; probing, placement, growth and deletion
#     are the hash map's own functions, so their proofs are shared;
#   - per slot: key `ks`, entry `ents`, and (prev, next, check word, timed,
#     deadline lo, deadline hi) in `lk` (8 words).
# Links are slot + 1; 0 = none. Nothing here is ever shared with `+` unless it
# is an unboxed word: sharing a boxed value makes the runtime reference-count
# every node of its type program-wide.

# ---- m: meta words ----
#  0 fresh  1 size  2 depth  3 ttl  4 life lo  5 life hi  6 tmask  7 tbits
#  16 + 2c, 17 + 2c: counter c (0 inserts, 1 evictions, 2 removals, 3 hits, 4 misses)

def pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def link(+s: U32) -> U32:
  U32.inc(s)

def slot(+l: U32) -> U32:
  U32.sub(l, 1)

def pidx(+s: U32) -> U32:
  U32.shl(U32.shl(U32.shl(s)))

def nidx(+s: U32) -> U32:
  U32.inc(pidx(s))

# ---- the cache ----

# An entry about to be stored: its value, whether it is timed, its deadline.
type Ent<a, -V: Kind(a)> is Kind(a):
  E{v: V, t: U32, lo: U32, hi: U32}

# An entry array of `depth` vacant cells (Array.new needs Data values).
def vac(a, -V: Kind(a), d: Nat) -> Array<Maybe<a, V>>:
  match d:
    case 0n:
      ALeaf{None{}}
    case 1n+ +p:
      ANode{vac(a, V, p), vac(a, V, p)}

type Fast<a, -V: Kind(a)> is Type:
  F{cap: U32, n: U32, head: U32, tail: U32, free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>}

# ---- keys: hashing and equality (short keys stay out of recursion) ----

def bump_hi_go(+i: U32, r: Array<U32> & U32) -> Array<U32>:
  (k, +h) = r
  Array.set(U32, k, i, U32.inc(h))

type Made<a, -V: Kind(a)> is Type:
  Made{f: Fast<a, V>}
  Rejected{reason: String}

def meta0() -> Array<U32>:
  Array.set(U32, Array.set(U32, Array.set(U32, Array.new(U32, 5n, 0), 1, 1), 6, 1), 7, 1)

def init(a, -V: Kind(a), +cap: U32) -> Fast<a, V>:
  F{cap, 0, 0, 0, 0, meta0(), Array.new(U32, 2n, 0), Array.new(String, 0n, ""), ALeaf{None{}}, Array.new(U32, 3n, 0)}

def capacity(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & U32:
  F{+cap, n, head, tail, free, m, tab, ks, ents, lk} = f
  (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, cap)

def new_checked(a, -V: Kind(a), +cap: U32, zero: Bool, reserved: Bool) -> Made<a, V>:
  match zero reserved:
    case True{} r:
      Rejected{"capacity must be positive"}
    case False{} True{}:
      Rejected{"size must not be 0XFFFFFFFF"}
    case False{} False{}:
      Made{init(a, V, cap)}

def new(a, -V: Kind(a), +cap: U32) -> Made<a, V>:
  new_checked(a, V, cap, U32.is_eq(cap, 0), U32.is_eq(cap, 4294967295))

# ---- add ----

def grow_tab_b(tab: Array<U32>, +mask: U32, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  (m2, +bits) = r
  +nmask = U32.inc(U32.shl(mask))
  (Array.set(U32, Array.set(U32, m2, 6, nmask), 7, U32.inc(bits)),
   H.mv_fin(H.mv_go(U32.to_nat(U32.inc(mask)), 0, nmask, H.MV{tab, Array.new(U32, U32.to_nat(U32.add(bits, 2)), 0)})))

def grow_tab(m: Array<U32>, tab: Array<U32>, +mask: U32, over: Bool) -> Array<U32> & Array<U32>:
  match over:
    case False{}:
      (m, tab)
    case True{}:
      grow_tab_b(tab, mask, Array.get(U32, m, 7))

def room_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, r: Array<U32> & Array<U32>) -> Fast<a, V>:
  (m, tab) = r
  F{cap, n, head, tail, free, m, tab, ks, ents, lk}

def room_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +mask) = r
  room_fin(a, V, cap, n, head, tail, free, ks, ents, lk, grow_tab(m, tab, mask, U32.is_gt(U32.shl(U32.inc(n)), U32.inc(mask))))

# Keep the table load <= 1/2 for one more entry.
def room(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  room_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, Array.get(U32, m, 6))

def ent_dl(a, -V: Kind(a), v: V, d: W.U64) -> Ent<a, V>:
  W.U64{lo, hi} = d
  E{v, 1, lo, hi}

def life_hi(a, -V: Kind(a), v: V, now: W.U64, +lo: U32, r: Array<U32> & U32) -> Array<U32> & Ent<a, V>:
  (m, +hi) = r
  (m, ent_dl(a, V, v, W.add(now, W.U64{lo, hi})))

def life_lo(a, -V: Kind(a), v: V, now: W.U64, r: Array<U32> & U32) -> Array<U32> & Ent<a, V>:
  (m, +lo) = r
  life_hi(a, V, v, now, lo, Array.get(U32, m, 5))

def ent_if(a, -V: Kind(a), v: V, now: W.U64, m: Array<U32>, on: Bool) -> Array<U32> & Ent<a, V>:
  match on:
    case False{}:
      (m, E{v, 0, 0, 0})
    case True{}:
      life_lo(a, V, v, now, Array.get(U32, m, 4))

def ent_ttl(a, -V: Kind(a), v: V, now: W.U64, r: Array<U32> & U32) -> Array<U32> & Ent<a, V>:
  (m, +t) = r
  ent_if(a, V, v, now, m, U32.is_ne(t, 0))

# The entry to store: immortal without a lifetime, else due at now + lifetime.
def entry_of(a, -V: Kind(a), m: Array<U32>, v: V, now: W.U64) -> Array<U32> & Ent<a, V>:
  ent_ttl(a, V, v, now, Array.get(U32, m, 3))

def set_if(a: Array<U32>, +i: U32, +x: U32, skip: Bool) -> Array<U32>:
  match skip:
    case True{}:
      a
    case False{}:
      Array.set(U32, a, i, x)

# ---- recency links ----

def ul_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, +p: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (lk, +q) = r
  F{cap, n, pick(U32.is_eq(p, 0), q, head), pick(U32.is_eq(q, 0), p, tail), free, m, tab, ks, ents,
    set_if(set_if(lk, pidx(slot(q)), p, U32.is_eq(q, 0)), nidx(slot(p)), q, U32.is_eq(p, 0))}

def ul_p(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, +s: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (lk, +p) = r
  ul_fin(a, V, cap, n, head, tail, free, m, tab, ks, ents, p, Array.get(U32, lk, nidx(s)))

# Detach slot s from the recency list.
def unlink(a, -V: Kind(a), f: Fast<a, V>, +s: U32) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  ul_p(a, V, cap, n, head, tail, free, m, tab, ks, ents, s, Array.get(U32, lk, pidx(s)))

# Attach slot s as the newest.
def link_tail(a, -V: Kind(a), f: Fast<a, V>, +s: U32) -> Fast<a, V>:
  F{cap, n, head, +tail, free, m, tab, ks, ents, lk} = f
  F{cap, n, pick(U32.is_eq(tail, 0), link(s), head), link(s), free, m, tab, ks, ents,
    set_if(Array.set(U32, Array.set(U32, lk, pidx(s), tail), nidx(s), 0), nidx(slot(tail)), link(s), U32.is_eq(tail, 0))}

def touch_go(a, -V: Kind(a), f: Fast<a, V>, +s: U32, newest: Bool) -> Fast<a, V>:
  match newest:
    case True{}:
      f
    case False{}:
      link_tail(a, V, unlink(a, V, f, s), s)

def touch(a, -V: Kind(a), f: Fast<a, V>, +s: U32) -> Fast<a, V>:
  F{cap, n, head, +tail, free, m, tab, ks, ents, lk} = f
  touch_go(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, s, U32.is_eq(link(s), tail))

def bump_hi(k: Array<U32>, +c: U32, zero: Bool) -> Array<U32>:
  match zero:
    case False{}:
      k
    case True{}:
      bump_hi_go(U32.add(17, U32.shl(c)), Array.get(U32, k, U32.add(17, U32.shl(c))))

def bump_lo(+c: U32, r: Array<U32> & U32) -> Array<U32>:
  (k, +l) = r
  +l2 = U32.inc(l)
  bump_hi(Array.set(U32, k, U32.add(16, U32.shl(c)), l2), c, U32.is_eq(l2, 0))

def bump(+c: U32, k: Array<U32>) -> Array<U32>:
  bump_lo(c, Array.get(U32, k, U32.add(16, U32.shl(c))))

def tidx(+s: U32) -> U32:
  U32.add(pidx(s), 3)

def dlo_idx(+s: U32) -> U32:
  U32.add(pidx(s), 4)

def dhi_idx(+s: U32) -> U32:
  U32.add(pidx(s), 5)

# Present key: new entry in place, touched, counted as an insertion.
def put_ent(a, -V: Kind(a), ents: Array<Maybe<a, V>>, lk: Array<U32>, +s: U32, e: Ent<a, V>) -> Array<Maybe<a, V>> & Array<U32>:
  E{v, +t, +lo, +hi} = e
  (Array.set(Maybe<a, V>, ents, s, Some{v}), Array.set(U32, Array.set(U32, Array.set(U32, lk, tidx(s), t), dlo_idx(s), lo), dhi_idx(s), hi))

def repl_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, +s: U32, r: Array<Maybe<a, V>> & Array<U32>) -> Fast<a, V>:
  (ents, lk) = r
  touch(a, V, F{cap, n, head, tail, free, bump(0, m), tab, ks, ents, lk}, s)

# Present key: new entry in place, touched, counted as an insertion.
def replace(a, -V: Kind(a), f: Fast<a, V>, +s: U32, e: Ent<a, V>) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  repl_fin(a, V, cap, n, head, tail, free, m, tab, ks, s, put_ent(a, V, ents, lk, s, e))



# ---- dropping a live slot ----

def drop_e(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, lk: Array<U32>, +s: U32, +c: U32, r: Array<Maybe<a, V>> & Maybe<a, V>) -> Fast<a, V> & Maybe<a, V>:
  (ents, old) = r
  (F{cap, U32.sub(n, 1), head, tail, link(s), bump(c, m), tab, ks, ents, Array.set(U32, lk, nidx(s), free)}, old)

# Unlink live slot s, free it and count it (c = 1 eviction, 2 removal); the
# table is updated by the caller.
def drop_core(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +c: U32) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  drop_e(a, V, cap, n, head, tail, free, m, tab, ks, lk, s, c, Array.swap(Maybe<a, V>, ents, s, None{}))

def drop_slot(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +c: U32) -> Fast<a, V> & Maybe<a, V>:
  drop_core(a, V, unlink(a, V, f, s), s, c)

type DStep is Type:
  DHit{tab: Array<U32>}
  DNext{tab: Array<U32>}

def ds_if(tab: Array<U32>, e: Bool) -> DStep:
  match e:
    case True{}:
      DHit{tab}
    case False{}:
      DNext{tab}

def ds_l(+l: U32, r: Array<U32> & U32) -> DStep:
  (tab, +x) = r
  ds_if(tab, U32.is_eq(x, l))

def dstep(tab: Array<U32>, +i: U32, +l: U32) -> DStep:
  ds_l(l, Array.get(U32, tab, U32.inc(U32.shl(i))))

def dfind(fuel: Nat, s: DStep, +mask: U32, +l: U32, +i: U32) -> Array<U32>:
  match fuel s:
    case 0n DHit{tab}:
      tab
    case 0n DNext{tab}:
      tab
    case 1n+p DHit{tab}:
      H.del_at(tab, mask, i)
    case 1n+p DNext{tab}:
      +j = H.bnext(i, mask)
      dfind(p, dstep(tab, j, l), mask, l, j)

# Delete the bucket holding link l (its check word is w): no key comparison.
def del_link(tab: Array<U32>, +mask: U32, +w: U32, +l: U32) -> Array<U32>:
  dfind(U32.to_nat(U32.inc(mask)), dstep(tab, HS.bucket(w, mask), l), mask, l, HS.bucket(w, mask))

def dl_h(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, +s: U32, +c: U32, +mask: U32, m: Array<U32>, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (lk, +h) = r
  drop_slot(a, V, F{cap, n, head, tail, free, m, del_link(tab, mask, h, link(s)), ks, ents, lk}, s, c)

def hidx(+s: U32) -> U32:
  U32.add(pidx(s), 2)

def dl_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +s: U32, +c: U32, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  dl_h(a, V, cap, n, head, tail, free, tab, ks, ents, s, c, mask, m, Array.get(U32, lk, hidx(s)))

# Drop slot s and its bucket (found by its stored hash and link).
def remove_slot(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +c: U32) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  dl_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, s, c, Array.get(U32, m, 6))

def drop_v(a, -V: Kind(a), r: Fast<a, V> & Maybe<a, V>) -> Fast<a, V>:
  (f, v) = r
  f

def evict_oldest(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V>:
  F{cap, n, +head, tail, free, m, tab, ks, ents, lk} = f
  drop_v(a, V, remove_slot(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, slot(head), 1))

def ps_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, +s: U32, +h: U32, r: Array<Maybe<a, V>> & Array<U32>) -> Fast<a, V>:
  (ents, lk) = r
  link_tail(a, V, F{cap, U32.inc(n), head, tail, free, bump(0, m), tab, ks, ents, Array.set(U32, lk, hidx(s), h)}, s)

def put_slot(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +s: U32, key: String, +h: U32, e: Ent<a, V>) -> Fast<a, V>:
  ps_fin(a, V, cap, n, head, tail, free, m, tab, Array.set(String, ks, s, key), s, h, put_ent(a, V, ents, lk, s, e))

def grow_sz(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +h: U32, e: Ent<a, V>, +fresh: U32, +size: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +depth) = r
  +d = U32.to_nat(depth)
  put_slot(a, V, cap, n, head, tail, free,
    Array.set(U32, Array.set(U32, Array.set(U32, m, 0, U32.inc(fresh)), 1, U32.shl(size)), 2, U32.inc(depth)), tab,
    ANode{ks, Array.new(String, d, "")}, ANode{ents, vac(a, V, d)}, ANode{lk, Array.new(U32, Nat.add(d, 3n), 0)},
    fresh, key, h, e)

def fresh_room(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +h: U32, e: Ent<a, V>, +fresh: U32, +size: U32, room: Bool) -> Fast<a, V>:
  match room:
    case True{}:
      put_slot(a, V, cap, n, head, tail, free, Array.set(U32, m, 0, U32.inc(fresh)), tab, ks, ents, lk, fresh, key, h, e)
    case False{}:
      grow_sz(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, h, e, fresh, size, Array.get(U32, m, 2))

def fresh_sz(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +h: U32, e: Ent<a, V>, +fresh: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +size) = r
  fresh_room(a, V, cap, n, head, tail, free, m, tab, ks, ents, lk, key, h, e, fresh, size, U32.is_lt(fresh, size))

def fresh_f(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +h: U32, e: Ent<a, V>, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +fresh) = r
  fresh_sz(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, h, e, fresh, Array.get(U32, m, 1))

def free_next(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +s: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, key: String, +h: U32, e: Ent<a, V>, r: Array<U32> & U32) -> Fast<a, V>:
  (lk, +nf) = r
  put_slot(a, V, cap, n, head, tail, nf, m, tab, ks, ents, lk, s, key, h, e)

def alloc_pick(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +h: U32, e: Ent<a, V>, none: Bool) -> Fast<a, V>:
  match none:
    case True{}:
      fresh_f(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, h, e, Array.get(U32, m, 0))
    case False{}:
      free_next(a, V, cap, n, head, tail, slot(free), m, tab, ks, ents, key, h, e, Array.get(U32, lk, nidx(slot(free))))

# Store a new key (its bucket already written) in a free or fresh slot.
def insert_slot(a, -V: Kind(a), f: Fast<a, V>, key: String, +h: U32, e: Ent<a, V>) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  alloc_pick(a, V, cap, n, head, tail, free, m, tab, ks, ents, lk, key, h, e, U32.is_eq(free, 0))

# The slot insert_slot will take: the free-list head, else the next fresh one.
def next_slot_m(+free: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (m, +fresh) = r
  (m, pick(U32.is_eq(free, 0), fresh, slot(free)))

def set_bucket_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +at: U32, +h: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +s) = r
  F{cap, n, head, tail, free, m, H.put_bucket(tab, at, h, link(s)), ks, ents, lk}


def ins_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +h: U32, +mask: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +s) = r
  F{cap, n, head, tail, free, m, H.ins_raw(tab, mask, h, link(s)), ks, ents, lk}

def ins_mask(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +h: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +mask) = r
  ins_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, h, mask, next_slot_m(free, Array.get(U32, m, 0)))

# Full: evict the oldest first (which may shift buckets), then re-probe for
# an empty bucket; the key is known absent.
def miss_full(a, -V: Kind(a), f: Fast<a, V>, key: String, +h: U32, e: Ent<a, V>) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  insert_slot(a, V, ins_mask(a, V, cap, n, head, tail, free, tab, ks, ents, lk, h, Array.get(U32, m, 6)), key, h, e)

# Not full: the probe's empty bucket takes the key.
def mr_size(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, e: Ent<a, V>, +fresh: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +size) = r
  fresh_room(a, V, cap, n, head, tail, 0, m, H.put_bucket(tab, at, h, link(fresh)), ks, ents, lk, key, h, e, fresh, size, U32.is_lt(fresh, size))

def mr_fresh(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, e: Ent<a, V>, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +fresh) = r
  mr_size(a, V, cap, n, head, tail, tab, ks, ents, lk, key, at, h, e, fresh, Array.get(U32, m, 1))

def mr_pick(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, e: Ent<a, V>, none: Bool) -> Fast<a, V>:
  match none:
    case True{}:
      mr_fresh(a, V, cap, n, head, tail, tab, ks, ents, lk, key, at, h, e, Array.get(U32, m, 0))
    case False{}:
      free_next(a, V, cap, n, head, tail, slot(free), m, H.put_bucket(tab, at, h, free), ks, ents, key, h, e, Array.get(U32, lk, nidx(slot(free))))

# Not full: the probe's empty bucket takes the key; the slot is chosen once.
def miss_room(a, -V: Kind(a), f: Fast<a, V>, key: String, +at: U32, +h: U32, e: Ent<a, V>) -> Fast<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  mr_pick(a, V, cap, n, head, tail, free, m, tab, ks, ents, lk, key, at, h, e, U32.is_eq(free, 0))

def add_miss(a, -V: Kind(a), f: Fast<a, V>, key: String, +at: U32, +h: U32, e: Ent<a, V>, full: Bool) -> Fast<a, V> & Bool:
  match full:
    case False{}:
      (miss_room(a, V, f, key, at, h, e), False{})
    case True{}:
      (miss_full(a, V, evict_oldest(a, V, f), key, h, e), True{})

def add_full(a, -V: Kind(a), f: Fast<a, V>, key: String, +at: U32, +h: U32, e: Ent<a, V>) -> Fast<a, V> & Bool:
  F{+cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  add_miss(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, key, at, h, e, U32.is_le(cap, n))

def add_pick(a, -V: Kind(a), f: Fast<a, V>, key: String, +at: U32, +h: U32, +l: U32, e: Ent<a, V>, absent: Bool) -> Fast<a, V> & Bool:
  match absent:
    case False{}:
      (replace(a, V, f, slot(l), e), False{})
    case True{}:
      add_full(a, V, f, key, at, h, e)

def add_e(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, +l: U32, r: Array<U32> & Ent<a, V>) -> Fast<a, V> & Bool:
  (m, e) = r
  add_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, key, at, h, l, e, U32.is_eq(l, 0))

def add_fd(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, v: V, now: W.U64, +h: U32, fd: H.Found) -> Fast<a, V> & Bool:
  H.FD{tab, ks, key, +at, +l} = fd
  add_e(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, at, h, l, entry_of(a, V, m, v, now))

def add_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, v: V, now: W.U64, r: H.Found & U32) -> Fast<a, V> & Bool:
  (fd, +h) = r
  add_fd(a, V, cap, n, head, tail, free, m, ents, lk, v, now, h, fd)

def add_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, v: V, now: W.U64, r: Array<U32> & U32) -> Fast<a, V> & Bool:
  (m, +mask) = r
  add_found(a, V, cap, n, head, tail, free, m, ents, lk, v, now, H.probe(tab, ks, mask, key))

def add_go(a, -V: Kind(a), f: Fast<a, V>, key: String, v: V, now: W.U64) -> Fast<a, V> & Bool:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  add_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, v, now, Array.get(U32, m, 6))

def add_long(a, -V: Kind(a), f: Fast<a, V>, key: String, v: V, now: W.U64) -> Fast<a, V> & Bool:
  add_go(a, V, room(a, V, f), key, v, now)

# Insert or replace key; the Bool reports whether an entry was evicted.
def add(a, -V: Kind(a), f: Fast<a, V>, key: String, v: V, now: W.U64) -> Fast<a, V> & Bool:
  add_long(a, V, f, key, v, now)

def fbump(a, -V: Kind(a), +c: U32, f: Fast<a, V>) -> Fast<a, V>:
  F{cap, n, head, tail, free, m, tab, ks, ents, lk} = f
  F{cap, n, head, tail, free, bump(c, m), tab, ks, ents, lk}

def expired_choose(deadline: W.U64, now: W.U64, immortal: Bool) -> Bool:
  match immortal:
    case True{}:
      False{}
    case False{}:
      W.le_signed(deadline, now)

# A deadline of zero never expires; otherwise deadline <= now (signed).
def expired(+deadline: W.U64, now: W.U64) -> Bool:
  expired_choose(deadline, now, W.is_zero(deadline))

# Whether slot s holds an expired entry (from its timing words in lk).
def gone_hi(+lo: U32, now: W.U64, r: Array<U32> & U32) -> Array<U32> & Bool:
  (lk, +hi) = r
  (lk, expired(W.U64{lo, hi}, now))

def gone_lo(+s: U32, now: W.U64, r: Array<U32> & U32) -> Array<U32> & Bool:
  (lk, +lo) = r
  gone_hi(lo, now, Array.get(U32, lk, dhi_idx(s)))

def gone_t(+s: U32, now: W.U64, lk: Array<U32>, timed: Bool) -> Array<U32> & Bool:
  match timed:
    case False{}:
      (lk, False{})
    case True{}:
      gone_lo(s, now, Array.get(U32, lk, dlo_idx(s)))

def gone_r(+s: U32, now: W.U64, r: Array<U32> & U32) -> Array<U32> & Bool:
  (lk, +t) = r
  gone_t(s, now, lk, U32.is_ne(t, 0))

def gone(lk: Array<U32>, +s: U32, now: W.U64) -> Array<U32> & Bool:
  gone_r(s, now, Array.get(U32, lk, tidx(s)))

# ---- reads ----

def miss_if(a, -V: Kind(a), f: Fast<a, V>, +tracked: Bool) -> Fast<a, V>:
  match tracked:
    case True{}:
      fbump(a, V, 4, f)
    case False{}:
      f

def rd_live(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +tracked: Bool, v: V) -> Fast<a, V> & Maybe<a, V>:
  match tracked:
    case True{}:
      (touch(a, V, fbump(a, V, 3, f), s), Some{v})
    case False{}:
      (f, Some{v})

def rd_gone(a, -V: Kind(a), +tracked: Bool, r: Fast<a, V> & Maybe<a, V>) -> Fast<a, V> & Maybe<a, V>:
  (f, v) = r
  (miss_if(a, V, f, tracked), None{})

def rd_exp_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +s: U32, +at: U32, +tracked: Bool, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  rd_gone(a, V, tracked, drop_slot(a, V, F{cap, n, head, tail, free, m, H.del_at(tab, mask, at), ks, ents, lk}, s, 2))

# The expired entry found at bucket `at`: dropped as a removal, read as a miss.
def rd_expire(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +at: U32, +tracked: Bool) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rd_exp_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, s, at, tracked, Array.get(U32, m, 6))



def rd_val(-V: Data, f: Fast<&2, V>, +s: U32, +tracked: Bool, m: Maybe<&2, V>) -> Fast<&2, V> & Maybe<&2, V>:
  match m:
    case None{}:
      (miss_if(&2, V, f, tracked), None{})
    case Some{v}:
      rd_live(&2, V, f, s, tracked, v)

def rd_v(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, lk: Array<U32>, +s: U32, +tracked: Bool, r: Array<Maybe<&2, V>> & Maybe<&2, V>) -> Fast<&2, V> & Maybe<&2, V>:
  (ents, e) = r
  rd_val(V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, s, tracked, e)

def rd_live_f(-V: Data, f: Fast<&2, V>, +s: U32, +tracked: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rd_v(V, cap, n, head, tail, free, m, tab, ks, lk, s, tracked, Array.get(Maybe<&2, V>, ents, s))

def rd_gone_pick(-V: Data, f: Fast<&2, V>, +s: U32, +at: U32, +tracked: Bool, g: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  match g:
    case False{}:
      rd_live_f(V, f, s, tracked)
    case True{}:
      rd_expire(&2, V, f, s, at, tracked)

def rd_g(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<&2, V>>, +s: U32, +at: U32, +tracked: Bool, r: Array<U32> & Bool) -> Fast<&2, V> & Maybe<&2, V>:
  (lk, g) = r
  rd_gone_pick(V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, s, at, tracked, g)

def rd_hit(-V: Data, f: Fast<&2, V>, +s: U32, +at: U32, now: W.U64, +tracked: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rd_g(V, cap, n, head, tail, free, m, tab, ks, ents, s, at, tracked, gone(lk, s, now))

def rd_pick(-V: Data, f: Fast<&2, V>, +at: U32, +l: U32, now: W.U64, +tracked: Bool, absent: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  match absent:
    case True{}:
      (miss_if(&2, V, f, tracked), None{})
    case False{}:
      rd_hit(V, f, slot(l), at, now, tracked)

def rd_fd(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<&2, V>>, lk: Array<U32>, now: W.U64, +tracked: Bool, fd: H.Found) -> Fast<&2, V> & Maybe<&2, V>:
  H.FD{tab, ks, key, +at, +l} = fd
  rd_pick(V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, now, tracked, U32.is_eq(l, 0))

def rd_found(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<&2, V>>, lk: Array<U32>, now: W.U64, +tracked: Bool, r: H.Found & U32) -> Fast<&2, V> & Maybe<&2, V>:
  (fd, w) = r
  rd_fd(V, cap, n, head, tail, free, m, ents, lk, now, tracked, fd)

def rd_m(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<&2, V>>, lk: Array<U32>, key: String, now: W.U64, +tracked: Bool, r: Array<U32> & U32) -> Fast<&2, V> & Maybe<&2, V>:
  (m, +mask) = r
  rd_found(V, cap, n, head, tail, free, m, ents, lk, now, tracked, H.probe(tab, ks, mask, key))

def read_long(-V: Data, f: Fast<&2, V>, key: String, now: W.U64, +tracked: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rd_m(V, cap, n, head, tail, free, tab, ks, ents, lk, key, now, tracked, Array.get(U32, m, 6))

def read(-V: Data, f: Fast<&2, V>, key: String, now: W.U64, +tracked: Bool) -> Fast<&2, V> & Maybe<&2, V>:
  read_long(V, f, key, now, tracked)

def get(-V: Data, f: Fast<&2, V>, key: String, now: W.U64) -> Fast<&2, V> & Maybe<&2, V>:
  read(V, f, key, now, True{})

def len(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & U32:
  F{cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, n)

# A copy of the meta words: counter c is at 16 + 2c (low) and 17 + 2c (high).
def cnt_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, r: Array<U32> & Array<U32>) -> Fast<a, V> & Array<U32>:
  (m, copy) = r
  (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, copy)

def counters(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & Array<U32>:
  F{cap, n, head, tail, free, m, tab, ks, ents, lk} = f
  cnt_fin(a, V, cap, n, head, tail, free, tab, ks, ents, lk, Array.clone(U32, m))

def set_life(m: Array<U32>, s: W.U64, +on: U32) -> Array<U32>:
  W.U64{+lo, +hi} = s
  Array.set(U32, Array.set(U32, Array.set(U32, m, 3, on), 4, lo), 5, hi)

# Lifetime in nanoseconds; zero means entries never expire. It is kept in
# milliseconds, so a deadline is one limb addition.
def set_lifetime_packed(a, -V: Kind(a), f: Fast<a, V>, +ns: W.U64) -> Fast<a, V>:
  F{cap, n, head, tail, free, m, tab, ks, ents, lk} = f
  F{cap, n, head, tail, free, set_life(m, W.div_small_signed(ns, 1000000), W.carry(Bool.not(W.is_zero(ns)))), tab, ks, ents, lk}

def peek(-V: Data, f: Fast<&2, V>, key: String, now: W.U64) -> Fast<&2, V> & Maybe<&2, V>:
  read(V, f, key, now, False{})



def ct_expire(a, -V: Kind(a), r: Fast<a, V> & Maybe<a, V>) -> Fast<a, V> & Bool:
  (f, v) = r
  (f, False{})

def ct_pick(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +at: U32, g: Bool) -> Fast<a, V> & Bool:
  match g:
    case False{}:
      (f, True{})
    case True{}:
      ct_expire(a, V, rd_expire(a, V, f, s, at, False{}))

def ct_g(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, +s: U32, +at: U32, r: Array<U32> & Bool) -> Fast<a, V> & Bool:
  (lk, g) = r
  ct_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, s, at, g)

def ct_hit(a, -V: Kind(a), f: Fast<a, V>, +s: U32, +at: U32, now: W.U64) -> Fast<a, V> & Bool:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  ct_g(a, V, cap, n, head, tail, free, m, tab, ks, ents, s, at, gone(lk, s, now))

def ct_found_pick(a, -V: Kind(a), f: Fast<a, V>, +at: U32, +l: U32, now: W.U64, absent: Bool) -> Fast<a, V> & Bool:
  match absent:
    case True{}:
      (f, False{})
    case False{}:
      ct_hit(a, V, f, slot(l), at, now)

def ct_fd(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, now: W.U64, fd: H.Found) -> Fast<a, V> & Bool:
  H.FD{tab, ks, key, +at, +l} = fd
  ct_found_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, now, U32.is_eq(l, 0))

def ct_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, now: W.U64, r: H.Found & U32) -> Fast<a, V> & Bool:
  (fd, w) = r
  ct_fd(a, V, cap, n, head, tail, free, m, ents, lk, now, fd)

def ct_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, now: W.U64, r: Array<U32> & U32) -> Fast<a, V> & Bool:
  (m, +mask) = r
  ct_found(a, V, cap, n, head, tail, free, m, ents, lk, now, H.probe(tab, ks, mask, key))

def ct_long(a, -V: Kind(a), f: Fast<a, V>, key: String, now: W.U64) -> Fast<a, V> & Bool:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  ct_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, now, Array.get(U32, m, 6))

def contains(a, -V: Kind(a), f: Fast<a, V>, key: String, now: W.U64) -> Fast<a, V> & Bool:
  ct_long(a, V, f, key, now)

def rm_hit(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +at: U32, +l: U32, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  drop_slot(a, V, F{cap, n, head, tail, free, m, H.del_at(tab, mask, at), ks, ents, lk}, slot(l), 2)

def rm_go(a, -V: Kind(a), f: Fast<a, V>, +at: U32, +l: U32) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rm_hit(a, V, cap, n, head, tail, free, tab, ks, ents, lk, at, l, Array.get(U32, m, 6))

def rm_pick(a, -V: Kind(a), f: Fast<a, V>, +at: U32, +l: U32, absent: Bool) -> Fast<a, V> & Maybe<a, V>:
  match absent:
    case True{}:
      (f, None{})
    case False{}:
      rm_go(a, V, f, at, l)

def rm_pick2(a, -V: Kind(a), f: Fast<a, V>, +at: U32, +l: U32, absent: Bool) -> Fast<a, V> & Maybe<a, V>:
  rm_pick(a, V, f, at, l, absent)

def rm_fd(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, fd: H.Found) -> Fast<a, V> & Maybe<a, V>:
  H.FD{tab, ks, key, +at, +l} = fd
  rm_pick2(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, U32.is_eq(l, 0))

def rm_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, r: H.Found & U32) -> Fast<a, V> & Maybe<a, V>:
  (fd, w) = r
  rm_fd(a, V, cap, n, head, tail, free, m, ents, lk, fd)

def rm_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  rm_found(a, V, cap, n, head, tail, free, m, ents, lk, H.probe(tab, ks, mask, key))

# Fused one-character remove: the probe loop finishes the operation itself,
# so no continuation is pushed around it.
def qrm(a, -V: Kind(a), fuel: Nat, s: H.QStep, +mask: U32, +w: U32, +i: U32, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>) -> Fast<a, V> & Maybe<a, V>:
  match fuel s:
    case 0n H.QEnd{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 0n H.QHit{tab, +l}:
      drop_slot(a, V, F{cap, n, head, tail, free, m, H.del_at(tab, mask, i), ks, ents, lk}, slot(l), 2)
    case 0n H.QNext{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 1n+p H.QEnd{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 1n+p H.QHit{tab, +l}:
      drop_slot(a, V, F{cap, n, head, tail, free, m, H.del_at(tab, mask, i), ks, ents, lk}, slot(l), 2)
    case 1n+p H.QNext{tab}:
      +j = H.bnext(i, mask)
      qrm(a, V, p, H.qstep(tab, j, w), mask, w, j, cap, n, head, tail, free, m, ks, ents, lk)

def rm_q2(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +w: U32, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  qrm(a, V, U32.to_nat(U32.inc(mask)), H.qstep(tab, HS.bucket(w, mask), w), mask, w, HS.bucket(w, mask), cap, n, head, tail, free, m, ks, ents, lk)

def rm_q(a, -V: Kind(a), f: Fast<a, V>, +w: U32) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rm_q2(a, V, cap, n, head, tail, free, tab, ks, ents, lk, w, Array.get(U32, m, 6))

def remove_long(a, -V: Kind(a), f: Fast<a, V>, key: String) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rm_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, Array.get(U32, m, 6))

def rm_short(a, -V: Kind(a), f: Fast<a, V>, +c: U32, ok: Bool) -> Fast<a, V> & Maybe<a, V>:
  match ok:
    case True{}:
      rm_q(a, V, f, H.short_word(c))
    case False{}:
      remove_long(a, V, f, SCon{Chr{c}, SNil{}})

def rm_c(a, -V: Kind(a), f: Fast<a, V>, +c: U32, t: String) -> Fast<a, V> & Maybe<a, V>:
  match t:
    case SNil{}:
      rm_short(a, V, f, c, U32.is_lt(c, H.tag()))
    case SCon{d, t2}:
      remove_long(a, V, f, SCon{Chr{c}, SCon{d, t2}})

def remove(a, -V: Kind(a), f: Fast<a, V>, key: String) -> Fast<a, V> & Maybe<a, V>:
  match key:
    case SNil{}:
      remove_long(a, V, f, SNil{})
    case SCon{Chr{+c}, t}:
      rm_c(a, V, f, c, t)

# ---- purge / resize ----

def zero_ctrs(m: Array<U32>) -> Array<U32>:
  Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32,
    Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32,
      Array.set(U32, m, 0, 0), 16, 0), 17, 0), 18, 0), 19, 0), 20, 0), 21, 0), 22, 0), 23, 0), 24, 0), 25, 0)

def purge_b(a, -V: Kind(a), +cap: U32, +n: U32, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, r: Array<U32> & U32) -> Fast<a, V> & U32:
  (m2, +bits) = r
  (F{cap, 0, 0, 0, 0, zero_ctrs(m2), Array.new(U32, U32.to_nat(U32.inc(bits)), 0), ks, ents, lk}, n)

# Every entry and the metrics are cleared; the table keeps its size.
def purge(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & U32:
  F{+cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  purge_b(a, V, cap, n, ks, ents, lk, Array.get(U32, m, 7))

type Rz<a, -V: Kind(a)> is Type:
  RzMore{f: Fast<a, V>}
  RzDone{f: Fast<a, V>}

def rz_pick(a, -V: Kind(a), f: Fast<a, V>, over: Bool) -> Rz<a, V>:
  match over:
    case True{}:
      RzMore{f}
    case False{}:
      RzDone{f}

def rz_check(a, -V: Kind(a), f: Fast<a, V>) -> Rz<a, V>:
  F{+cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  rz_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, U32.is_lt(cap, n))

def rz_go(a, -V: Kind(a), fuel: Nat, s: Rz<a, V>, +ev: U32) -> Fast<a, V> & Result<&2, &2, String, U32>:
  match fuel s:
    case 0n RzMore{f}:
      (f, Done{ev})
    case 0n RzDone{f}:
      (f, Done{ev})
    case 1n+p RzMore{f}:
      rz_go(a, V, p, rz_check(a, V, evict_oldest(a, V, f)), U32.inc(ev))
    case 1n+p RzDone{f}:
      (f, Done{ev})

def set_cap(a, -V: Kind(a), f: Fast<a, V>, +cap: U32) -> Fast<a, V>:
  F{c0, +n, head, tail, free, m, tab, ks, ents, lk} = f
  F{cap, n, head, tail, free, m, tab, ks, ents, lk}

def rz_start(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & Result<&2, &2, String, U32>:
  F{cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  rz_go(a, V, U32.to_nat(n), rz_check(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}), 0)

def resize_go(a, -V: Kind(a), f: Fast<a, V>, +cap: U32, zero: Bool) -> Fast<a, V> & Result<&2, &2, String, U32>:
  match zero:
    case True{}:
      (f, Fail{"capacity must be positive"})
    case False{}:
      rz_start(a, V, set_cap(a, V, f, cap))

# Set a positive capacity, evicting the oldest entries until the cache fits;
# reports how many were evicted. Capacity 0 fails and changes nothing.
def resize(a, -V: Kind(a), f: Fast<a, V>, +cap: U32) -> Fast<a, V> & Result<&2, &2, String, U32>:
  resize_go(a, V, f, cap, U32.is_eq(cap, 0))

# ---- keys ----

type Kx<a, -V: Kind(a)> is Type:
  KMore{f: Fast<a, V>}
  KDone{f: Fast<a, V>}

def kx_pick(a, -V: Kind(a), f: Fast<a, V>, gone: Bool) -> Kx<a, V>:
  match gone:
    case True{}:
      KMore{f}
    case False{}:
      KDone{f}



def kx_g(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, r: Array<U32> & Bool) -> Kx<a, V>:
  (lk, g) = r
  kx_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, g)

def kx_head(a, -V: Kind(a), f: Fast<a, V>, +now: W.U64) -> Kx<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  kx_g(a, V, cap, n, head, tail, free, m, tab, ks, ents, gone(lk, slot(head), now))

def kx_if(a, -V: Kind(a), f: Fast<a, V>, +now: W.U64, empty: Bool) -> Kx<a, V>:
  match empty:
    case True{}:
      KDone{f}
    case False{}:
      kx_head(a, V, f, now)

def kx_check(a, -V: Kind(a), f: Fast<a, V>, +now: W.U64) -> Kx<a, V>:
  F{cap, n, +head, tail, free, m, tab, ks, ents, lk} = f
  kx_if(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, now, U32.is_eq(head, 0))

def drop_head(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V>:
  F{cap, n, +head, tail, free, m, tab, ks, ents, lk} = f
  drop_v(a, V, remove_slot(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, slot(head), 2))

def kx_go(a, -V: Kind(a), fuel: Nat, +now: W.U64, s: Kx<a, V>) -> Fast<a, V>:
  match fuel s:
    case 0n KMore{f}:
      f
    case 0n KDone{f}:
      f
    case 1n+p KMore{f}:
      kx_go(a, V, p, now, kx_check(a, V, drop_head(a, V, f), now))
    case 1n+p KDone{f}:
      f

type Walk is Type:
  WK{ks: Array<String>, lk: Array<U32>, acc: List<&2, String>, at: U32}

def wk_p(ks: Array<String>, acc: List<&2, String>, r: Array<U32> & U32) -> Walk:
  (lk, +p) = r
  WK{ks, lk, acc, p}

def wk_c(ks: Array<String>, lk: Array<U32>, acc: List<&2, String>, +at: U32, kk: String & String) -> Walk:
  (k1, k2) = kk
  wk_p(Array.set(String, ks, slot(at), k1), Con{k2, acc}, Array.get(U32, lk, pidx(slot(at))))

def wk_k(lk: Array<U32>, acc: List<&2, String>, +at: U32, r: Array<String> & String) -> Walk:
  (ks, k) = r
  wk_c(ks, lk, acc, at, H.str_copy(k))

def wk_word(ks: Array<String>, acc: List<&2, String>, +at: U32, +kw: U32, lk: Array<U32>, short: Bool) -> Walk:
  match short:
    case True{}:
      wk_p(ks, Con{SCon{Chr{U32.and(kw, 2147483647)}, SNil{}}, acc}, Array.get(U32, lk, pidx(slot(at))))
    case False{}:
      wk_k(lk, acc, at, Array.swap(String, ks, slot(at), SNil{}))

def wk_w(ks: Array<String>, acc: List<&2, String>, +at: U32, r: Array<U32> & U32) -> Walk:
  (lk, +kw) = r
  wk_word(ks, acc, at, kw, lk, H.is_short(kw))

# A one-character key is stored only as its tagged word.
def wk_step(w: Walk) -> Walk:
  WK{ks, lk, acc, +at} = w
  wk_w(ks, acc, at, Array.get(U32, lk, hidx(slot(at))))

def wk_loop(fuel: Nat, w: Walk) -> Walk:
  match fuel:
    case 0n:
      w
    case 1n+p:
      wk_loop(p, wk_step(w))

def keys_fin(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ents: Array<Maybe<a, V>>, w: Walk) -> Fast<a, V> & List<&2, String>:
  WK{ks, lk, acc, at} = w
  (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, acc)

def keys_list(a, -V: Kind(a), f: Fast<a, V>) -> Fast<a, V> & List<&2, String>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  keys_fin(a, V, cap, n, head, tail, free, m, tab, ents, wk_loop(U32.to_nat(n), WK{ks, lk, Nil{}, tail}))

def keys_n(a, -V: Kind(a), +now: W.U64, f: Fast<a, V>) -> Fast<a, V>:
  F{cap, +n, head, tail, free, m, tab, ks, ents, lk} = f
  kx_go(a, V, U32.to_nat(n), now, kx_check(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, now))

# The keys oldest first, after the oldest EXPIRED prefix is removed (each a
# removal), stopping at the first immortal or live oldest entry.
def keys(a, -V: Kind(a), f: Fast<a, V>, +now: W.U64) -> Fast<a, V> & List<&2, String>:
  keys_list(a, V, keys_n(a, V, now, f))
