import Base
import ../math/u64.bend as W
import ../math/hash.bend as HS

# LRU cache, performance layout (experiment). Same observable semantics as
# src/lru/fast.bend and benchmarks/native/lru.c: capacity eviction of the
# oldest entry, lifetimes, five 64-bit metrics, touch-on-get, no-touch peek
# and contains, expired entries dropped (as removals) when a read finds them.
#
# Layout, chosen for Bend 2's native backend:
#   - every record field is a register word, so the state is kept NARROW:
#     F{cap, n, head, tail, free, m, tab, ks, ents, lk} is ten words;
#   - cold scalars and the counters live in one packed Array<U32> `m`;
#   - `tab` is an open-addressing table of interleaved (link, hash) U32 pairs
#     (linear probing, power-of-two size, load <= 1/2, backward-shift delete);
#   - per slot: key `ks`, entry `ents`, and (prev, next, hash, -) in `lk`.
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

type Found is Type:
  FD{tab: Array<U32>, ks: Array<String>, key: String, at: U32, link: U32, w: U32}

# All String walks are TAIL loops (reversed accumulator, then reversed
# back), so they compile inline and no caller needs a continuation.
def rev_onto(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      rev_onto(t, SCon{h, acc})

def hash_acc(s: String, +h: U32, acc: String) -> String & U32:
  match s:
    case SNil{}:
      (rev_onto(acc, SNil{}), h)
    case SCon{Chr{+c}, t}:
      hash_acc(t, HS.mix(h, c), SCon{Chr{c}, acc})

# The key's hash, handing the key back.
def hash(s: String) -> String & U32:
  hash_acc(s, 0, SNil{})

def eq_acc(a: String, b: String, ra: String, rb: String, +e: Bool) -> (String & String) & Bool:
  match a b:
    case SNil{} SNil{}:
      ((rev_onto(ra, SNil{}), rev_onto(rb, SNil{})), e)
    case SNil{} SCon{h, t}:
      ((rev_onto(ra, SNil{}), rev_onto(rb, SCon{h, t})), False{})
    case SCon{h, t} SNil{}:
      ((rev_onto(ra, SCon{h, t}), rev_onto(rb, SNil{})), False{})
    case SCon{Chr{+x}, ta} SCon{Chr{+y}, tb}:
      eq_acc(ta, tb, SCon{Chr{x}, ra}, SCon{Chr{y}, rb}, Bool.and(e, U32.is_eq(x, y)))

# String equality, handing both strings back.
def eq(a: String, b: String) -> (String & String) & Bool:
  eq_acc(a, b, SNil{}, SNil{}, True{})

def copy_acc(s: String, ra: String, rb: String) -> String & String:
  match s:
    case SNil{}:
      (rev_onto(ra, SNil{}), rev_onto(rb, SNil{}))
    case SCon{Chr{+c}, t}:
      copy_acc(t, SCon{Chr{c}, ra}, SCon{Chr{c}, rb})

# An explicit deep copy (sharing a String with `+` would refcount them all).
def str_copy(s: String) -> String & String:
  copy_acc(s, SNil{}, SNil{})

# ---- the table: probing ----

# One probed bucket: empty (the key is absent), holding the key, or not.
type Step is Type:
  SEnd{tab: Array<U32>, ks: Array<String>, key: String}
  SHit{tab: Array<U32>, ks: Array<String>, key: String, l: U32}
  SNext{tab: Array<U32>, ks: Array<String>, key: String}

def sk_pick(tab: Array<U32>, +l: U32, ks: Array<String>, key: String, e: Bool) -> Step:
  match e:
    case True{}:
      SHit{tab, ks, key, l}
    case False{}:
      SNext{tab, ks, key}

def sk_fin(tab: Array<U32>, +l: U32, +s: U32, ks: Array<String>, r: (String & String) & Bool) -> Step:
  ((key, k), e) = r
  sk_pick(tab, l, Array.set(String, ks, s, k), key, e)

def sk_cmp(tab: Array<U32>, +l: U32, +s: U32, key: String, r: Array<String> & String) -> Step:
  (ks, k) = r
  sk_fin(tab, l, s, ks, eq(key, k))

def sk_same(tab: Array<U32>, ks: Array<String>, +l: U32, key: String, same: Bool) -> Step:
  match same:
    case False{}:
      SNext{tab, ks, key}
    case True{}:
      sk_cmp(tab, l, slot(l), key, Array.swap(String, ks, slot(l), SNil{}))

def sk_h(ks: Array<String>, +l: U32, key: String, +h: U32, r: Array<U32> & U32) -> Step:
  (tab, +bh) = r
  sk_same(tab, ks, l, key, U32.is_eq(bh, h))

def sk_empty(tab: Array<U32>, ks: Array<String>, +i: U32, key: String, +h: U32, +l: U32, e: Bool) -> Step:
  match e:
    case True{}:
      SEnd{tab, ks, key}
    case False{}:
      sk_h(ks, l, key, h, Array.get(U32, tab, U32.inc(U32.shl(i))))

def sk_l(ks: Array<String>, +i: U32, key: String, +h: U32, r: Array<U32> & U32) -> Step:
  (tab, +l) = r
  sk_empty(tab, ks, i, key, h, l, U32.is_eq(l, 0))

def step(tab: Array<U32>, ks: Array<String>, +i: U32, key: String, +h: U32) -> Step:
  sk_l(ks, i, key, h, Array.get(U32, tab, U32.shl(i)))

def bnext(+i: U32, +mask: U32) -> U32:
  U32.and(U32.inc(i), mask)

# fuel bounds the probe; a table is never full, so an empty bucket ends it.
def find(fuel: Nat, s: Step, +mask: U32, +h: U32, +i: U32) -> Found:
  match fuel s:
    case 0n SEnd{tab, ks, key}:
      FD{tab, ks, key, i, 0, h}
    case 0n SHit{tab, ks, key, +l}:
      FD{tab, ks, key, i, l, h}
    case 0n SNext{tab, ks, key}:
      FD{tab, ks, key, i, 0, h}
    case 1n+p SEnd{tab, ks, key}:
      FD{tab, ks, key, i, 0, h}
    case 1n+p SHit{tab, ks, key, +l}:
      FD{tab, ks, key, i, l, h}
    case 1n+p SNext{tab, ks, key}:
      +j = bnext(i, mask)
      find(p, step(tab, ks, j, key, h), mask, h, j)

def long_word(+h: U32) -> U32:
  U32.and(h, 2147483647)

def probe_long_h(tab: Array<U32>, ks: Array<String>, +mask: U32, r: String & U32) -> Found:
  (key, +h) = r
  find(U32.to_nat(U32.inc(mask)), step(tab, ks, HS.bucket(long_word(h), mask), key, long_word(h)), mask, long_word(h), HS.bucket(long_word(h), mask))

def probe_long(tab: Array<U32>, ks: Array<String>, +mask: U32, key: String) -> Found:
  probe_long_h(tab, ks, mask, hash(key))

# Bucket check words: a one-character key (code < 2^31) is its code with the
# top bit set, so equal words mean equal keys and no String is compared; any
# other key is its hash with the top bit clear, confirmed by comparing Strings.
def tag() -> U32:
  2147483648

# One-character probe: buckets only, the key's cells already freed.
type SStep is Type:
  QEnd{tab: Array<U32>}
  QHit{tab: Array<U32>, l: U32}
  QNext{tab: Array<U32>}

def qs_same(tab: Array<U32>, +l: U32, same: Bool) -> SStep:
  match same:
    case True{}:
      QHit{tab, l}
    case False{}:
      QNext{tab}

def qs_w(+l: U32, +w: U32, r: Array<U32> & U32) -> SStep:
  (tab, +bw) = r
  qs_same(tab, l, U32.is_eq(bw, w))

def qs_empty(tab: Array<U32>, +i: U32, +w: U32, +l: U32, e: Bool) -> SStep:
  match e:
    case True{}:
      QEnd{tab}
    case False{}:
      qs_w(l, w, Array.get(U32, tab, U32.inc(U32.shl(i))))

def qs_l(+i: U32, +w: U32, r: Array<U32> & U32) -> SStep:
  (tab, +l) = r
  qs_empty(tab, i, w, l, U32.is_eq(l, 0))

def qstep(tab: Array<U32>, +i: U32, +w: U32) -> SStep:
  qs_l(i, w, Array.get(U32, tab, U32.shl(i)))

type QFound is Type:
  QF{tab: Array<U32>, at: U32, link: U32}

def qfind(fuel: Nat, s: SStep, +mask: U32, +w: U32, +i: U32) -> QFound:
  match fuel s:
    case 0n QEnd{tab}:
      QF{tab, i, 0}
    case 0n QHit{tab, +l}:
      QF{tab, i, l}
    case 0n QNext{tab}:
      QF{tab, i, 0}
    case 1n+p QEnd{tab}:
      QF{tab, i, 0}
    case 1n+p QHit{tab, +l}:
      QF{tab, i, l}
    case 1n+p QNext{tab}:
      +j = bnext(i, mask)
      qfind(p, qstep(tab, j, w), mask, w, j)

def short_fin(ks: Array<String>, +w: U32, r: QFound) -> Found:
  QF{tab, +at, +l} = r
  FD{tab, ks, SNil{}, at, l, w}

def probe_short(tab: Array<U32>, ks: Array<String>, +mask: U32, +c: U32, ok: Bool) -> Found:
  match ok:
    case True{}:
      short_fin(ks, U32.or(c, tag()), qfind(U32.to_nat(U32.inc(mask)), qstep(tab, HS.bucket(U32.or(c, tag()), mask), U32.or(c, tag())), mask, U32.or(c, tag()), HS.bucket(U32.or(c, tag()), mask)))
    case False{}:
      probe_long(tab, ks, mask, SCon{Chr{c}, SNil{}})

def probe_c(tab: Array<U32>, ks: Array<String>, +mask: U32, +c: U32, t: String) -> Found:
  match t:
    case SNil{}:
      probe_short(tab, ks, mask, c, U32.is_lt(c, tag()))
    case SCon{d, t2}:
      probe_long(tab, ks, mask, SCon{Chr{c}, SCon{d, t2}})

# The bucket of key (link != 0) or the empty bucket ending its probe, with the
# key's check word. A one-character key comes back as SNil (see key_back).
def probe(tab: Array<U32>, ks: Array<String>, +mask: U32, key: String) -> Found:
  match key:
    case SNil{}:
      probe_long(tab, ks, mask, SNil{})
    case SCon{Chr{+c}, t}:
      probe_c(tab, ks, mask, c, t)

def bump_hi_go(+i: U32, r: Array<U32> & U32) -> Array<U32>:
  (k, +h) = r
  Array.set(U32, k, i, U32.inc(h))

type Mv is Type:
  MV{old: Array<U32>, nt: Array<U32>}

# ---- the table: insertion without comparison, growth ----

type RStep is Type:
  REmpty{tab: Array<U32>}
  RFull{tab: Array<U32>}

def rs_if(tab: Array<U32>, e: Bool) -> RStep:
  match e:
    case True{}:
      REmpty{tab}
    case False{}:
      RFull{tab}

def rs_l(r: Array<U32> & U32) -> RStep:
  (tab, +l) = r
  rs_if(tab, U32.is_eq(l, 0))

def rstep(tab: Array<U32>, +i: U32) -> RStep:
  rs_l(Array.get(U32, tab, U32.shl(i)))

def put_bucket(tab: Array<U32>, +i: U32, +l: U32, +h: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, tab, U32.shl(i), l), U32.inc(U32.shl(i)), h)

def ins_go(fuel: Nat, s: RStep, +mask: U32, +i: U32, +l: U32, +h: U32) -> Array<U32>:
  match fuel s:
    case 0n REmpty{tab}:
      tab
    case 0n RFull{tab}:
      tab
    case 1n+p REmpty{tab}:
      put_bucket(tab, i, l, h)
    case 1n+p RFull{tab}:
      +j = bnext(i, mask)
      ins_go(p, rstep(tab, j), mask, j, l, h)

# Put (l, h) in the first empty bucket of h's probe (the key is known absent).
def ins_raw(tab: Array<U32>, +mask: U32, +l: U32, +h: U32) -> Array<U32>:
  ins_go(U32.to_nat(U32.inc(mask)), rstep(tab, HS.bucket(h, mask)), mask, HS.bucket(h, mask), l, h)

def mv_h(+l: U32, nt: Array<U32>, +nmask: U32, r: Array<U32> & U32) -> Mv:
  (old, +h) = r
  MV{old, ins_raw(nt, nmask, l, h)}

def mv_if(+k: U32, old: Array<U32>, nt: Array<U32>, +nmask: U32, +l: U32, e: Bool) -> Mv:
  match e:
    case True{}:
      MV{old, nt}
    case False{}:
      mv_h(l, nt, nmask, Array.get(U32, old, U32.inc(U32.shl(k))))

def mv_l(+k: U32, nt: Array<U32>, +nmask: U32, r: Array<U32> & U32) -> Mv:
  (old, +l) = r
  mv_if(k, old, nt, nmask, l, U32.is_eq(l, 0))

def mv_step(+k: U32, +nmask: U32, m: Mv) -> Mv:
  MV{old, nt} = m
  mv_l(k, nt, nmask, Array.get(U32, old, U32.shl(k)))

def mv_go(fuel: Nat, +k: U32, +nmask: U32, m: Mv) -> Mv:
  match fuel:
    case 0n:
      m
    case 1n+p:
      mv_go(p, U32.inc(k), nmask, mv_step(k, nmask, m))

def mv_fin(m: Mv) -> Array<U32>:
  MV{old, nt} = m
  nt

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
   mv_fin(mv_go(U32.to_nat(U32.inc(mask)), 0, nmask, MV{tab, Array.new(U32, U32.to_nat(U32.add(bits, 2)), 0)})))

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
  ds_l(l, Array.get(U32, tab, U32.shl(i)))

# One cluster bucket k after the hole i: empty (stop), movable into the hole
# (its home is not cyclically in (i, k]), or to be skipped.
type Sh is Type:
  HEnd{tab: Array<U32>}
  HMove{tab: Array<U32>, l: U32, h: U32}
  HSkip{tab: Array<U32>}

def sh_mv(tab: Array<U32>, +l: U32, +h: U32, mv: Bool) -> Sh:
  match mv:
    case True{}:
      HMove{tab, l, h}
    case False{}:
      HSkip{tab}

def sh_h(+l: U32, +mask: U32, +i: U32, +k: U32, r: Array<U32> & U32) -> Sh:
  (tab, +h) = r
  sh_mv(tab, l, h, U32.is_ge(U32.and(U32.sub(k, HS.bucket(h, mask)), mask), U32.and(U32.sub(k, i), mask)))

def sh_if(tab: Array<U32>, +mask: U32, +i: U32, +k: U32, +l: U32, e: Bool) -> Sh:
  match e:
    case True{}:
      HEnd{tab}
    case False{}:
      sh_h(l, mask, i, k, Array.get(U32, tab, U32.inc(U32.shl(k))))

def sh_l(+mask: U32, +i: U32, +k: U32, r: Array<U32> & U32) -> Sh:
  (tab, +l) = r
  sh_if(tab, mask, i, k, l, U32.is_eq(l, 0))

def sh_step(tab: Array<U32>, +mask: U32, +i: U32, +k: U32) -> Sh:
  sh_l(mask, i, k, Array.get(U32, tab, U32.shl(k)))

# ---- the table: backward-shift deletion ----

def clear_bucket(tab: Array<U32>, +i: U32) -> Array<U32>:
  put_bucket(tab, i, 0, 0)

def shift(fuel: Nat, s: Sh, +mask: U32, +i: U32, +k: U32) -> Array<U32>:
  match fuel s:
    case 0n HEnd{tab}:
      clear_bucket(tab, i)
    case 0n HMove{tab, l, h}:
      clear_bucket(tab, i)
    case 0n HSkip{tab}:
      clear_bucket(tab, i)
    case 1n+p HEnd{tab}:
      clear_bucket(tab, i)
    case 1n+p HMove{tab, +l, +h}:
      +k2 = bnext(k, mask)
      shift(p, sh_step(put_bucket(tab, i, l, h), mask, k, k2), mask, k, k2)
    case 1n+p HSkip{tab}:
      +k2 = bnext(k, mask)
      shift(p, sh_step(tab, mask, i, k2), mask, i, k2)

# Empty bucket i, closing the gap.
def del_at(tab: Array<U32>, +mask: U32, +i: U32) -> Array<U32>:
  shift(U32.to_nat(U32.inc(mask)), sh_step(tab, mask, i, bnext(i, mask)), mask, i, bnext(i, mask))

def dfind(fuel: Nat, s: DStep, +mask: U32, +l: U32, +i: U32) -> Array<U32>:
  match fuel s:
    case 0n DHit{tab}:
      tab
    case 0n DNext{tab}:
      tab
    case 1n+p DHit{tab}:
      del_at(tab, mask, i)
    case 1n+p DNext{tab}:
      +j = bnext(i, mask)
      dfind(p, dstep(tab, j, l), mask, l, j)

# Delete the bucket holding link l (its key hashed to h): no key comparison.
def del_link(tab: Array<U32>, +mask: U32, +h: U32, +l: U32) -> Array<U32>:
  dfind(U32.to_nat(U32.inc(mask)), dstep(tab, HS.bucket(h, mask), l), mask, l, HS.bucket(h, mask))

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
  F{cap, n, head, tail, free, m, put_bucket(tab, at, link(s), h), ks, ents, lk}


def ins_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +h: U32, +mask: U32, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +s) = r
  F{cap, n, head, tail, free, m, ins_raw(tab, mask, link(s), h), ks, ents, lk}

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
  fresh_room(a, V, cap, n, head, tail, 0, m, put_bucket(tab, at, link(fresh), h), ks, ents, lk, key, h, e, fresh, size, U32.is_lt(fresh, size))

def mr_fresh(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, e: Ent<a, V>, r: Array<U32> & U32) -> Fast<a, V>:
  (m, +fresh) = r
  mr_size(a, V, cap, n, head, tail, tab, ks, ents, lk, key, at, h, e, fresh, Array.get(U32, m, 1))

def mr_pick(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, +at: U32, +h: U32, e: Ent<a, V>, none: Bool) -> Fast<a, V>:
  match none:
    case True{}:
      mr_fresh(a, V, cap, n, head, tail, tab, ks, ents, lk, key, at, h, e, Array.get(U32, m, 0))
    case False{}:
      free_next(a, V, cap, n, head, tail, slot(free), m, put_bucket(tab, at, free, h), ks, ents, key, h, e, Array.get(U32, lk, nidx(slot(free))))

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

def add_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, v: V, now: W.U64, fd: Found) -> Fast<a, V> & Bool:
  FD{tab, ks, key, +at, +l, +h} = fd
  add_e(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, at, h, l, entry_of(a, V, m, v, now))

def add_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, v: V, now: W.U64, r: Array<U32> & U32) -> Fast<a, V> & Bool:
  (m, +mask) = r
  add_found(a, V, cap, n, head, tail, free, m, ents, lk, v, now, probe(tab, ks, mask, key))

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
  rd_gone(a, V, tracked, drop_slot(a, V, F{cap, n, head, tail, free, m, del_at(tab, mask, at), ks, ents, lk}, s, 2))

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

def rd_found(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<&2, V>>, lk: Array<U32>, now: W.U64, +tracked: Bool, fd: Found) -> Fast<&2, V> & Maybe<&2, V>:
  FD{tab, ks, key, +at, +l, w} = fd
  rd_pick(V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, now, tracked, U32.is_eq(l, 0))

def rd_m(-V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<&2, V>>, lk: Array<U32>, key: String, now: W.U64, +tracked: Bool, r: Array<U32> & U32) -> Fast<&2, V> & Maybe<&2, V>:
  (m, +mask) = r
  rd_found(V, cap, n, head, tail, free, m, ents, lk, now, tracked, probe(tab, ks, mask, key))

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

def ct_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, now: W.U64, fd: Found) -> Fast<a, V> & Bool:
  FD{tab, ks, key, +at, +l, w} = fd
  ct_found_pick(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, now, U32.is_eq(l, 0))

def ct_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, now: W.U64, r: Array<U32> & U32) -> Fast<a, V> & Bool:
  (m, +mask) = r
  ct_found(a, V, cap, n, head, tail, free, m, ents, lk, now, probe(tab, ks, mask, key))

def ct_long(a, -V: Kind(a), f: Fast<a, V>, key: String, now: W.U64) -> Fast<a, V> & Bool:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  ct_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, now, Array.get(U32, m, 6))

def contains(a, -V: Kind(a), f: Fast<a, V>, key: String, now: W.U64) -> Fast<a, V> & Bool:
  ct_long(a, V, f, key, now)

def rm_hit(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +at: U32, +l: U32, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  drop_slot(a, V, F{cap, n, head, tail, free, m, del_at(tab, mask, at), ks, ents, lk}, slot(l), 2)

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

def rm_found(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ents: Array<Maybe<a, V>>, lk: Array<U32>, fd: Found) -> Fast<a, V> & Maybe<a, V>:
  FD{tab, ks, key, +at, +l, w} = fd
  rm_pick2(a, V, F{cap, n, head, tail, free, m, tab, ks, ents, lk}, at, l, U32.is_eq(l, 0))

def rm_m(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, key: String, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  rm_found(a, V, cap, n, head, tail, free, m, ents, lk, probe(tab, ks, mask, key))

# Fused one-character remove: the probe loop finishes the operation itself,
# so no continuation is pushed around it.
def qrm(a, -V: Kind(a), fuel: Nat, s: SStep, +mask: U32, +w: U32, +i: U32, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>) -> Fast<a, V> & Maybe<a, V>:
  match fuel s:
    case 0n QEnd{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 0n QHit{tab, +l}:
      drop_slot(a, V, F{cap, n, head, tail, free, m, del_at(tab, mask, i), ks, ents, lk}, slot(l), 2)
    case 0n QNext{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 1n+p QEnd{tab}:
      (F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})
    case 1n+p QHit{tab, +l}:
      drop_slot(a, V, F{cap, n, head, tail, free, m, del_at(tab, mask, i), ks, ents, lk}, slot(l), 2)
    case 1n+p QNext{tab}:
      +j = bnext(i, mask)
      qrm(a, V, p, qstep(tab, j, w), mask, w, j, cap, n, head, tail, free, m, ks, ents, lk)

def rm_q2(a, -V: Kind(a), +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, tab: Array<U32>, ks: Array<String>, ents: Array<Maybe<a, V>>, lk: Array<U32>, +w: U32, r: Array<U32> & U32) -> Fast<a, V> & Maybe<a, V>:
  (m, +mask) = r
  qrm(a, V, U32.to_nat(U32.inc(mask)), qstep(tab, HS.bucket(w, mask), w), mask, w, HS.bucket(w, mask), cap, n, head, tail, free, m, ks, ents, lk)

def rm_q(a, -V: Kind(a), f: Fast<a, V>, +w: U32) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rm_q2(a, V, cap, n, head, tail, free, tab, ks, ents, lk, w, Array.get(U32, m, 6))

def remove_long(a, -V: Kind(a), f: Fast<a, V>, key: String) -> Fast<a, V> & Maybe<a, V>:
  F{+cap, +n, +head, +tail, +free, m, tab, ks, ents, lk} = f
  rm_m(a, V, cap, n, head, tail, free, tab, ks, ents, lk, key, Array.get(U32, m, 6))

def rm_short(a, -V: Kind(a), f: Fast<a, V>, +c: U32, ok: Bool) -> Fast<a, V> & Maybe<a, V>:
  match ok:
    case True{}:
      rm_q(a, V, f, U32.or(c, tag()))
    case False{}:
      remove_long(a, V, f, SCon{Chr{c}, SNil{}})

def rm_c(a, -V: Kind(a), f: Fast<a, V>, +c: U32, t: String) -> Fast<a, V> & Maybe<a, V>:
  match t:
    case SNil{}:
      rm_short(a, V, f, c, U32.is_lt(c, tag()))
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
  wk_c(ks, lk, acc, at, str_copy(k))

def wk_word(ks: Array<String>, acc: List<&2, String>, +at: U32, +kw: U32, lk: Array<U32>, short: Bool) -> Walk:
  match short:
    case True{}:
      wk_p(ks, Con{SCon{Chr{U32.and(kw, 2147483647)}, SNil{}}, acc}, Array.get(U32, lk, pidx(slot(at))))
    case False{}:
      wk_k(lk, acc, at, Array.swap(String, ks, slot(at), SNil{}))

def wk_w(ks: Array<String>, acc: List<&2, String>, +at: U32, r: Array<U32> & U32) -> Walk:
  (lk, +kw) = r
  wk_word(ks, acc, at, kw, lk, U32.is_ge(kw, tag()))

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
