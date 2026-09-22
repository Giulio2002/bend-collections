import Base
import ../math/hash.bend as HS

# A String-keyed hash table with Base.Map's shape of API:
#
#   new(a, V)                   -> HashMap<a, V>
#   set(a, V, m, key, x)        -> HashMap<a, V>              insert or replace
#   get(V, d, m, key)           -> HashMap<&2, V> & V         d when absent (V: Data)
#   has(a, V, m, key)           -> HashMap<a, V> & Bool
#   pop(a, V, m, key)           -> HashMap<a, V> & Maybe<a, V>
#   del(a, V, m, key)           -> HashMap<a, V>
#   size(a, V, m)               -> HashMap<a, V> & U32
#   keys(a, V, m)               -> HashMap<a, V> & List<&2, String>   (bucket order)
#
# The table owns arrays, so it is a Type and is threaded through every call.
#
# Layout:
#   - buckets: one packed Array<U32> of (check word, slot link) pairs; open
#     addressing with linear probing over a power-of-two number of buckets,
#     load <= 1/2, backward-shift deletion (no tombstones);
#   - entries: a dense slot arena (key `ks`, value `vs`), with a free list of
#     removed slots chained through `nx`. Growing the buckets rehashes U32
#     pairs only; keys and values never move.
# A one-character key (code < 2^31) has check word code | 2^31: equal words
# mean equal keys, so its String is never hashed, compared or stored (its
# `ks` cell holds SNil and `keys` rebuilds it). Any other key has check word
# (hash & (2^31 - 1)) | 1, confirmed by a String comparison. Links are
# slot + 1 (0 = none). Every String walk is a tail loop, and nothing boxed is
# shared with `+`.

type HashMap<a, -V: Kind(a)> is Type:
  HM{n: U32, mask: U32, td: U32, fresh: U32, ssz: U32, sd: U32, free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>}

def size(a, -V: Kind(a), m: HashMap<a, V>) -> HashMap<a, V> & U32:
  HM{+n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx} = m
  (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, n)

# ---- words, hashing, equality ----

def tag() -> U32:
  2147483648

def bnext(+i: U32, +mask: U32) -> U32:
  U32.and(U32.inc(i), mask)

def link(+s: U32) -> U32:
  U32.inc(s)

def slot(+l: U32) -> U32:
  U32.sub(l, 1)

def short_word(+c: U32) -> U32:
  U32.or(c, tag())

def long_word(+h: U32) -> U32:
  U32.or(U32.and(h, 2147483647), 1)

def is_short(+w: U32) -> Bool:
  U32.is_ge(w, tag())

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

# A deep copy (sharing a String with `+` would refcount every String).
def str_copy(s: String) -> String & String:
  copy_acc(s, SNil{}, SNil{})

def lw_fin(r: String & U32) -> String & U32:
  (k, +h) = r
  (k, long_word(h))

def key_long(key: String) -> String & U32:
  lw_fin(hash_acc(key, 0, SNil{}))

# ---- probing ----

type Found is Type:
  FD{tab: Array<U32>, ks: Array<String>, key: String, at: U32, link: U32}

# Long keys: a matching word is confirmed against the slot's stored String.
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

def sk_fin(tab: Array<U32>, +l: U32, ks: Array<String>, r: (String & String) & Bool) -> Step:
  ((key, k), e) = r
  sk_pick(tab, l, Array.set(String, ks, slot(l), k), key, e)

def sk_cmp(tab: Array<U32>, +l: U32, key: String, r: Array<String> & String) -> Step:
  (ks, k) = r
  sk_fin(tab, l, ks, eq(key, k))

def sk_same(tab: Array<U32>, ks: Array<String>, +l: U32, key: String, same: Bool) -> Step:
  match same:
    case False{}:
      SNext{tab, ks, key}
    case True{}:
      sk_cmp(tab, l, key, Array.swap(String, ks, slot(l), SNil{}))

def sk_l(ks: Array<String>, key: String, +x: U32, +w: U32, r: Array<U32> & U32) -> Step:
  (tab, +l) = r
  sk_same(tab, ks, l, key, U32.is_eq(x, w))

def sk_empty(tab: Array<U32>, ks: Array<String>, +i: U32, key: String, +w: U32, +x: U32, e: Bool) -> Step:
  match e:
    case True{}:
      SEnd{tab, ks, key}
    case False{}:
      sk_l(ks, key, x, w, Array.get(U32, tab, U32.inc(U32.shl(i))))

def sk_w(ks: Array<String>, +i: U32, key: String, +w: U32, r: Array<U32> & U32) -> Step:
  (tab, +x) = r
  sk_empty(tab, ks, i, key, w, x, U32.is_eq(x, 0))

def step(tab: Array<U32>, ks: Array<String>, +i: U32, key: String, +w: U32) -> Step:
  sk_w(ks, i, key, w, Array.get(U32, tab, U32.shl(i)))

def find(fuel: Nat, s: Step, +mask: U32, +w: U32, +i: U32) -> Found:
  match fuel s:
    case 0n SEnd{tab, ks, key}:
      FD{tab, ks, key, i, 0}
    case 0n SHit{tab, ks, key, +l}:
      FD{tab, ks, key, i, l}
    case 0n SNext{tab, ks, key}:
      FD{tab, ks, key, i, 0}
    case 1n+p SEnd{tab, ks, key}:
      FD{tab, ks, key, i, 0}
    case 1n+p SHit{tab, ks, key, +l}:
      FD{tab, ks, key, i, l}
    case 1n+p SNext{tab, ks, key}:
      +j = bnext(i, mask)
      find(p, step(tab, ks, j, key, w), mask, w, j)

def probe_lw(tab: Array<U32>, ks: Array<String>, +mask: U32, r: String & U32) -> Found & U32:
  (key, +w) = r
  (find(U32.to_nat(U32.inc(mask)), step(tab, ks, HS.bucket(w, mask), key, w), mask, w, HS.bucket(w, mask)), w)

def probe_long(tab: Array<U32>, ks: Array<String>, +mask: U32, key: String) -> Found & U32:
  probe_lw(tab, ks, mask, key_long(key))

# One-character keys: the bucket words alone decide.
type QStep is Type:
  QEnd{tab: Array<U32>}
  QHit{tab: Array<U32>, l: U32}
  QNext{tab: Array<U32>}

def qs_l(r: Array<U32> & U32) -> QStep:
  (tab, +l) = r
  QHit{tab, l}

def qs_same(tab: Array<U32>, +i: U32, same: Bool) -> QStep:
  match same:
    case True{}:
      qs_l(Array.get(U32, tab, U32.inc(U32.shl(i))))
    case False{}:
      QNext{tab}

def qs_if(tab: Array<U32>, +i: U32, +w: U32, +x: U32, e: Bool) -> QStep:
  match e:
    case True{}:
      QEnd{tab}
    case False{}:
      qs_same(tab, i, U32.is_eq(x, w))

def qs_w(+i: U32, +w: U32, r: Array<U32> & U32) -> QStep:
  (tab, +x) = r
  qs_if(tab, i, w, x, U32.is_eq(x, 0))

def qstep(tab: Array<U32>, +i: U32, +w: U32) -> QStep:
  qs_w(i, w, Array.get(U32, tab, U32.shl(i)))

type QFound is Type:
  QF{tab: Array<U32>, at: U32, link: U32}

def qfind(fuel: Nat, s: QStep, +mask: U32, +w: U32, +i: U32) -> QFound:
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

def q_fin(ks: Array<String>, +w: U32, r: QFound) -> Found & U32:
  QF{tab, +at, +l} = r
  (FD{tab, ks, SNil{}, at, l}, w)

def probe_short(tab: Array<U32>, ks: Array<String>, +mask: U32, +c: U32, ok: Bool) -> Found & U32:
  match ok:
    case True{}:
      q_fin(ks, short_word(c), qfind(U32.to_nat(U32.inc(mask)), qstep(tab, HS.bucket(short_word(c), mask), short_word(c)), mask, short_word(c), HS.bucket(short_word(c), mask)))
    case False{}:
      probe_long(tab, ks, mask, SCon{Chr{c}, SNil{}})

def probe_c(tab: Array<U32>, ks: Array<String>, +mask: U32, +c: U32, t: String) -> Found & U32:
  match t:
    case SNil{}:
      probe_short(tab, ks, mask, c, U32.is_lt(c, tag()))
    case SCon{d, t2}:
      probe_long(tab, ks, mask, SCon{Chr{c}, SCon{d, t2}})

# The bucket holding key (link != 0) or the empty bucket ending its probe,
# the key as it would be stored (SNil for a one-character key), and its word.
def probe(tab: Array<U32>, ks: Array<String>, +mask: U32, key: String) -> Found & U32:
  match key:
    case SNil{}:
      probe_long(tab, ks, mask, SNil{})
    case SCon{Chr{+c}, t}:
      probe_c(tab, ks, mask, c, t)

# ---- buckets: placement without comparison, growth, backward shift ----

def put_bucket(tab: Array<U32>, +i: U32, +w: U32, +l: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, tab, U32.shl(i), w), U32.inc(U32.shl(i)), l)

type RStep is Type:
  REmpty{tab: Array<U32>}
  RFull{tab: Array<U32>}

def rs_if(tab: Array<U32>, e: Bool) -> RStep:
  match e:
    case True{}:
      REmpty{tab}
    case False{}:
      RFull{tab}

def rs_w(r: Array<U32> & U32) -> RStep:
  (tab, +x) = r
  rs_if(tab, U32.is_eq(x, 0))

def rstep(tab: Array<U32>, +i: U32) -> RStep:
  rs_w(Array.get(U32, tab, U32.shl(i)))

def ins_go(fuel: Nat, s: RStep, +mask: U32, +i: U32, +w: U32, +l: U32) -> Array<U32>:
  match fuel s:
    case 0n REmpty{tab}:
      tab
    case 0n RFull{tab}:
      tab
    case 1n+p REmpty{tab}:
      put_bucket(tab, i, w, l)
    case 1n+p RFull{tab}:
      +j = bnext(i, mask)
      ins_go(p, rstep(tab, j), mask, j, w, l)

# Put (w, l) in the first empty bucket of w's probe.
def ins_raw(tab: Array<U32>, +mask: U32, +w: U32, +l: U32) -> Array<U32>:
  ins_go(U32.to_nat(U32.inc(mask)), rstep(tab, HS.bucket(w, mask)), mask, HS.bucket(w, mask), w, l)

type Mv is Type:
  MV{old: Array<U32>, nt: Array<U32>}

def mv_l(+w: U32, nt: Array<U32>, +nmask: U32, r: Array<U32> & U32) -> Mv:
  (old, +l) = r
  MV{old, ins_raw(nt, nmask, w, l)}

def mv_if(+k: U32, old: Array<U32>, nt: Array<U32>, +nmask: U32, +w: U32, e: Bool) -> Mv:
  match e:
    case True{}:
      MV{old, nt}
    case False{}:
      mv_l(w, nt, nmask, Array.get(U32, old, U32.inc(U32.shl(k))))

def mv_w(+k: U32, nt: Array<U32>, +nmask: U32, r: Array<U32> & U32) -> Mv:
  (old, +w) = r
  mv_if(k, old, nt, nmask, w, U32.is_eq(w, 0))

def mv_step(+k: U32, +nmask: U32, m: Mv) -> Mv:
  MV{old, nt} = m
  mv_w(k, nt, nmask, Array.get(U32, old, U32.shl(k)))

def mv_go(fuel: Nat, +k: U32, +nmask: U32, m: Mv) -> Mv:
  match fuel:
    case 0n:
      m
    case 1n+p:
      mv_go(p, U32.inc(k), nmask, mv_step(k, nmask, m))

def mv_fin(m: Mv) -> Array<U32>:
  MV{old, nt} = m
  nt

def clear_bucket(tab: Array<U32>, +i: U32) -> Array<U32>:
  put_bucket(tab, i, 0, 0)

type Sh is Type:
  HEnd{tab: Array<U32>}
  HMove{tab: Array<U32>, w: U32, l: U32}
  HSkip{tab: Array<U32>}

def sh_mv(tab: Array<U32>, +w: U32, +l: U32, mv: Bool) -> Sh:
  match mv:
    case True{}:
      HMove{tab, w, l}
    case False{}:
      HSkip{tab}

def sh_l(+w: U32, +mask: U32, +i: U32, +k: U32, r: Array<U32> & U32) -> Sh:
  (tab, +l) = r
  sh_mv(tab, w, l, U32.is_ge(U32.and(U32.sub(k, HS.bucket(w, mask)), mask), U32.and(U32.sub(k, i), mask)))

def sh_if(tab: Array<U32>, +mask: U32, +i: U32, +k: U32, +w: U32, e: Bool) -> Sh:
  match e:
    case True{}:
      HEnd{tab}
    case False{}:
      sh_l(w, mask, i, k, Array.get(U32, tab, U32.inc(U32.shl(k))))

def sh_w(+mask: U32, +i: U32, +k: U32, r: Array<U32> & U32) -> Sh:
  (tab, +w) = r
  sh_if(tab, mask, i, k, w, U32.is_eq(w, 0))

def sh_step(tab: Array<U32>, +mask: U32, +i: U32, +k: U32) -> Sh:
  sh_w(mask, i, k, Array.get(U32, tab, U32.shl(k)))

def shift(fuel: Nat, s: Sh, +mask: U32, +i: U32, +k: U32) -> Array<U32>:
  match fuel s:
    case 0n HEnd{tab}:
      clear_bucket(tab, i)
    case 0n HMove{tab, w, l}:
      clear_bucket(tab, i)
    case 0n HSkip{tab}:
      clear_bucket(tab, i)
    case 1n+p HEnd{tab}:
      clear_bucket(tab, i)
    case 1n+p HMove{tab, +w, +l}:
      +k2 = bnext(k, mask)
      shift(p, sh_step(put_bucket(tab, i, w, l), mask, k, k2), mask, k, k2)
    case 1n+p HSkip{tab}:
      +k2 = bnext(k, mask)
      shift(p, sh_step(tab, mask, i, k2), mask, i, k2)

# Empty bucket i, closing the gap behind it.
def del_at(tab: Array<U32>, +mask: U32, +i: U32) -> Array<U32>:
  shift(U32.to_nat(U32.inc(mask)), sh_step(tab, mask, i, bnext(i, mask)), mask, i, bnext(i, mask))

# ---- the slot arena ----

# A value array of 2^d vacant cells (Array.new needs Data values).
def vac(a, -V: Kind(a), d: Nat) -> Array<Maybe<a, V>>:
  match d:
    case 0n:
      ALeaf{None{}}
    case 1n+ +p:
      ANode{vac(a, V, p), vac(a, V, p)}

def new(a, -V: Kind(a)) -> HashMap<a, V>:
  HM{0, 1, 2, 0, 1, 0, 0, Array.new(U32, 2n, 0), Array.new(String, 0n, ""), ALeaf{None{}}, Array.new(U32, 0n, 0)}

# ---- set ----

# Twice the buckets, every (word, link) pair re-placed.
def grow_tab(+mask: U32, +td: U32, tab: Array<U32>) -> Array<U32>:
  mv_fin(mv_go(U32.to_nat(U32.inc(mask)), 0, U32.inc(U32.shl(mask)), MV{tab, Array.new(U32, U32.to_nat(U32.inc(td)), 0)}))

type Arena<a, -V: Kind(a)> is Type:
  AR{ks: Array<String>, vs: Array<Maybe<a, V>>}

def store(a, -V: Kind(a), ks: Array<String>, vs: Array<Maybe<a, V>>, +s: U32, key: String, x: V) -> Arena<a, V>:
  AR{Array.set(String, ks, s, key), Array.set(Maybe<a, V>, vs, s, Some{x})}

def ins_fin(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, nx: Array<U32>, r: Arena<a, V>) -> HashMap<a, V>:
  AR{ks, vs} = r
  HM{U32.inc(n), mask, td, fresh, sz, sd, free, tab, ks, vs, nx}

# The new entry's slot s is chosen; its bucket is at (or, after growth, found anew).
def ins_slot(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>, +s: U32, +at: U32, +w: U32, key: String, x: V, over: Bool) -> HashMap<a, V>:
  match over:
    case False{}:
      ins_fin(a, V, n, mask, td, fresh, sz, sd, free, put_bucket(tab, at, w, link(s)), nx, store(a, V, ks, vs, s, key, x))
    case True{}:
      ins_fin(a, V, n, U32.inc(U32.shl(mask)), U32.inc(td), fresh, sz, sd, free, ins_raw(grow_tab(mask, td, tab), U32.inc(U32.shl(mask)), w, link(s)), nx, store(a, V, ks, vs, s, key, x))

def ins_free(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, +s: U32, +at: U32, +w: U32, key: String, x: V, r: Array<U32> & U32) -> HashMap<a, V>:
  (nx, +nf) = r
  ins_slot(a, V, n, mask, td, fresh, sz, sd, nf, tab, ks, vs, nx, s, at, w, key, x, U32.is_gt(U32.shl(U32.inc(n)), U32.inc(mask)))

def ins_fresh(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>, +at: U32, +w: U32, key: String, x: V, room: Bool) -> HashMap<a, V>:
  match room:
    case True{}:
      ins_slot(a, V, n, mask, td, U32.inc(fresh), sz, sd, 0, tab, ks, vs, nx, fresh, at, w, key, x, U32.is_gt(U32.shl(U32.inc(n)), U32.inc(mask)))
    case False{}:
      ins_slot(a, V, n, mask, td, U32.inc(fresh), U32.shl(sz), U32.inc(sd), 0, tab, ANode{ks, Array.new(String, U32.to_nat(sd), "")}, ANode{vs, vac(a, V, U32.to_nat(sd))}, ANode{nx, Array.new(U32, U32.to_nat(sd), 0)}, fresh, at, w, key, x, U32.is_gt(U32.shl(U32.inc(n)), U32.inc(mask)))

def ins_new(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>, +at: U32, +w: U32, key: String, x: V, none: Bool) -> HashMap<a, V>:
  match none:
    case True{}:
      ins_fresh(a, V, n, mask, td, fresh, sz, sd, tab, ks, vs, nx, at, w, key, x, U32.is_lt(fresh, sz))
    case False{}:
      ins_free(a, V, n, mask, td, fresh, sz, sd, tab, ks, vs, slot(free), at, w, key, x, Array.get(U32, nx, slot(free)))

def set_hit(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>, +at: U32, +l: U32, +w: U32, key: String, x: V, absent: Bool) -> HashMap<a, V>:
  match absent:
    case False{}:
      HM{n, mask, td, fresh, sz, sd, free, tab, ks, Array.set(Maybe<a, V>, vs, slot(l), Some{x}), nx}
    case True{}:
      ins_new(a, V, n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx, at, w, key, x, U32.is_eq(free, 0))

def set_f(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, vs: Array<Maybe<a, V>>, nx: Array<U32>, x: V, r: Found & U32) -> HashMap<a, V>:
  (fd, +w) = r
  FD{tab, ks, key, +at, +l} = fd
  set_hit(a, V, n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx, at, l, w, key, x, U32.is_eq(l, 0))

# Insert key -> x, replacing any value already stored under key.
def set(a, -V: Kind(a), m: HashMap<a, V>, key: String, x: V) -> HashMap<a, V>:
  HM{+n, +mask, +td, +fresh, +sz, +sd, +free, tab, ks, vs, nx} = m
  set_f(a, V, n, mask, td, fresh, sz, sd, free, vs, nx, x, probe(tab, ks, mask, key))

# ---- get / has ----

def get_v(-V: Data, dflt: V, r: Array<Maybe<&2, V>> & Maybe<&2, V>) -> Array<Maybe<&2, V>> & V:
  (vs, mv) = r
  match mv:
    case None{}:
      (vs, dflt)
    case Some{v}:
      (vs, v)

def get_fin(-V: Data, +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, nx: Array<U32>, r: Array<Maybe<&2, V>> & V) -> HashMap<&2, V> & V:
  (vs, v) = r
  (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, v)

def get_hit(-V: Data, +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<&2, V>>, nx: Array<U32>, dflt: V, +l: U32, absent: Bool) -> HashMap<&2, V> & V:
  match absent:
    case True{}:
      (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, dflt)
    case False{}:
      get_fin(V, n, mask, td, fresh, sz, sd, free, tab, ks, nx, get_v(V, dflt, Array.get(Maybe<&2, V>, vs, slot(l))))

def get_f(-V: Data, +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, vs: Array<Maybe<&2, V>>, nx: Array<U32>, dflt: V, r: Found & U32) -> HashMap<&2, V> & V:
  (fd, w) = r
  FD{tab, ks, key, at, +l} = fd
  get_hit(V, n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx, dflt, l, U32.is_eq(l, 0))

# The value stored under key, or dflt (values are copied out, so V: Data).
def get(-V: Data, dflt: V, m: HashMap<&2, V>, key: String) -> HashMap<&2, V> & V:
  HM{+n, +mask, +td, +fresh, +sz, +sd, +free, tab, ks, vs, nx} = m
  get_f(V, n, mask, td, fresh, sz, sd, free, vs, nx, dflt, probe(tab, ks, mask, key))

def has_f(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, vs: Array<Maybe<a, V>>, nx: Array<U32>, r: Found & U32) -> HashMap<a, V> & Bool:
  (fd, w) = r
  FD{tab, ks, key, at, +l} = fd
  (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, U32.is_ne(l, 0))

def has(a, -V: Kind(a), m: HashMap<a, V>, key: String) -> HashMap<a, V> & Bool:
  HM{+n, +mask, +td, +fresh, +sz, +sd, +free, tab, ks, vs, nx} = m
  has_f(a, V, n, mask, td, fresh, sz, sd, free, vs, nx, probe(tab, ks, mask, key))

# ---- pop / del ----

def drop_key(ks: Array<String>, +s: U32, short: Bool) -> Array<String>:
  match short:
    case True{}:
      ks
    case False{}:
      Array.set(String, ks, s, "")

def pop_v(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, nx: Array<U32>, +at: U32, +s: U32, +w: U32, r: Array<Maybe<a, V>> & Maybe<a, V>) -> HashMap<a, V> & Maybe<a, V>:
  (vs, v) = r
  (HM{U32.sub(n, 1), mask, td, fresh, sz, sd, link(s), del_at(tab, mask, at), drop_key(ks, s, is_short(w)), vs, Array.set(U32, nx, s, free)}, v)

def pop_hit(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, tab: Array<U32>, ks: Array<String>, vs: Array<Maybe<a, V>>, nx: Array<U32>, +at: U32, +l: U32, +w: U32, absent: Bool) -> HashMap<a, V> & Maybe<a, V>:
  match absent:
    case True{}:
      (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, None{})
    case False{}:
      pop_v(a, V, n, mask, td, fresh, sz, sd, free, tab, ks, nx, at, slot(l), w, Array.swap(Maybe<a, V>, vs, slot(l), None{}))

def pop_f(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, vs: Array<Maybe<a, V>>, nx: Array<U32>, r: Found & U32) -> HashMap<a, V> & Maybe<a, V>:
  (fd, +w) = r
  FD{tab, ks, key, +at, +l} = fd
  pop_hit(a, V, n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx, at, l, w, U32.is_eq(l, 0))

# Remove key, answering its value.
def pop(a, -V: Kind(a), m: HashMap<a, V>, key: String) -> HashMap<a, V> & Maybe<a, V>:
  HM{+n, +mask, +td, +fresh, +sz, +sd, +free, tab, ks, vs, nx} = m
  pop_f(a, V, n, mask, td, fresh, sz, sd, free, vs, nx, probe(tab, ks, mask, key))

def del_drop(a, -V: Kind(a), r: HashMap<a, V> & Maybe<a, V>) -> HashMap<a, V>:
  (m, v) = r
  m

def del(a, -V: Kind(a), m: HashMap<a, V>, key: String) -> HashMap<a, V>:
  del_drop(a, V, pop(a, V, m, key))

# ---- keys ----

type Walk is Type:
  WK{tab: Array<U32>, ks: Array<String>, acc: List<&2, String>}

def wk_long(tab: Array<U32>, +s: U32, acc: List<&2, String>, ks: Array<String>, kk: String & String) -> Walk:
  (k1, k2) = kk
  WK{tab, Array.set(String, ks, s, k1), Con{k2, acc}}

def wk_copy(tab: Array<U32>, +s: U32, acc: List<&2, String>, r: Array<String> & String) -> Walk:
  (ks, key) = r
  wk_long(tab, s, acc, ks, str_copy(key))

def wk_ll(ks: Array<String>, acc: List<&2, String>, r: Array<U32> & U32) -> Walk:
  (tab, +l) = r
  wk_copy(tab, slot(l), acc, Array.swap(String, ks, slot(l), SNil{}))

def wk_kind(tab: Array<U32>, ks: Array<String>, +k: U32, acc: List<&2, String>, +w: U32, short: Bool) -> Walk:
  match short:
    case True{}:
      WK{tab, ks, Con{SCon{Chr{U32.and(w, 2147483647)}, SNil{}}, acc}}
    case False{}:
      wk_ll(ks, acc, Array.get(U32, tab, U32.inc(U32.shl(k))))

def wk_if(tab: Array<U32>, ks: Array<String>, +k: U32, acc: List<&2, String>, +w: U32, e: Bool) -> Walk:
  match e:
    case True{}:
      WK{tab, ks, acc}
    case False{}:
      wk_kind(tab, ks, k, acc, w, is_short(w))

def wk_w(ks: Array<String>, +k: U32, acc: List<&2, String>, r: Array<U32> & U32) -> Walk:
  (tab, +w) = r
  wk_if(tab, ks, k, acc, w, U32.is_eq(w, 0))

def wk_step(+k: U32, w: Walk) -> Walk:
  WK{tab, ks, acc} = w
  wk_w(ks, k, acc, Array.get(U32, tab, U32.shl(k)))

def wk_go(fuel: Nat, +k: U32, w: Walk) -> Walk:
  match fuel:
    case 0n:
      w
    case 1n+p:
      wk_go(p, U32.sub(k, 1), wk_step(k, w))

def keys_fin(a, -V: Kind(a), +n: U32, +mask: U32, +td: U32, +fresh: U32, +sz: U32, +sd: U32, +free: U32, vs: Array<Maybe<a, V>>, nx: Array<U32>, w: Walk) -> HashMap<a, V> & List<&2, String>:
  WK{tab, ks, acc} = w
  (HM{n, mask, td, fresh, sz, sd, free, tab, ks, vs, nx}, acc)

# Every key, in bucket order.
def keys(a, -V: Kind(a), m: HashMap<a, V>) -> HashMap<a, V> & List<&2, String>:
  HM{+n, +mask, +td, +fresh, +sz, +sd, +free, tab, ks, vs, nx} = m
  keys_fin(a, V, n, mask, td, fresh, sz, sd, free, vs, nx, wk_go(U32.to_nat(U32.inc(mask)), mask, WK{tab, ks, Nil{}}))
