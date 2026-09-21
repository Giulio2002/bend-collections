import Base
import ../types/segment_tree.bend as E

# Segment tree over n U32 values with lazy range addition; all arithmetic
# wraps modulo 2^32.
#
# Representation: TWO flat native `Base.Array`s in the standard flat layout
# of an array-based segment tree, with the block [o, o + 2^p) of value
# indices identified by its split point:
#
#   * `cells` (2^(depth+1) slots) holds the value of index t at 2^depth + t,
#     and the SUM of the block [o, o + 2^p) (p >= 1, including that block's
#     own tag but not its ancestors') at the split point o + 2^(p-1);
#   * `tags` (2^depth slots) holds that block's pending addition (its lazy
#     tag) at the same split point o + 2^(p-1).
#
# The value at index t is the stored cell plus every tag on the path to it.
# Two sibling blocks never share a cell (their split points lie strictly
# inside their own ranges), which is what makes the walks independent.
#
# Every step of every operation is one `Array.get`/`Array.set` at a computed
# index plus index arithmetic; no walk ever recomputes a power of two,
# because the walks carry the current block's half size `h` (2^(p-1)) and
# the next one `hh` (h/2, one machine division per level), exactly as the C
# reference carries `1u << (p-1)`. `base` (2^depth) is cached in the
# structure for the same reason.
#
#   get(i) / set(i, v)      walk the path, accumulating tags; set stores
#                           v minus the accumulated tags at the leaf and
#                           recomputes the sums on the way back up
#   range_query(l, r)       prefix(r) - prefix(l); a prefix walk adds the
#                           sum of a fully covered left block plus the
#                           ancestors' tags over it
#   range_add(l, r, v)      lazy: add v to the first r values, then -v to
#                           the first l values; a fully covered block only
#                           receives a tag and a sum bump (O(1)), never a
#                           walk
#
# `Base.Array` is linear, so every operation takes the tree and gives it
# back, and a tree that is no longer needed is released with `dispose`;
# `clone` makes two independent copies.
#
# Errors never change the state: get/set with index >= n fail with
# IndexOutOfRange; range_query/range_add unless l <= r <= n fail with
# InvalidRange.
#
# Capacity: `depth_for` stops at depth 30, so the cell array's own depth is
# at most 31 and every index is a representable U32.
#
# Cost: every operation visits O(log n) blocks with a constant number of
# indexed accesses each, plus one U32 shift per level (the tag scaling), so
# get/set/range_query/range_add are O(log n) accesses and O(log n) shifts.
# new O(2^depth) (Base's array fill); from_list O(n log n); length O(1).

type Cel is Data:
  CV{value: U32}

type SegTree is Type:
  ST{n: Nat, depth: Nat, base: Nat, cells: Array<Cel>, tags: Array<Cel>}

def cval(c: Cel) -> U32:
  match c:
    case CV{v}:
      v

def pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

def max_depth() -> Nat:
  30n

def depth_go(fuel: Nat, +n: Nat, d: Nat, +cap: Nat, done: Bool) -> Nat:
  match fuel done:
    case 0n _:
      d
    case 1n+f True{}:
      d
    case 1n+f False{}:
      depth_go(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.double(cap)))

def depth_for(+n: Nat) -> Nat:
  depth_go(max_depth(), n, 0n, 1n, Nat.is_le(n, 1n))

# ---- cell access ----

def read_fin(p: Array<Cel> & Cel) -> Array<Cel> & U32:
  (a, x) = p
  (a, cval(x))

def read(a: Array<Cel>, +k: Nat) -> Array<Cel> & U32:
  read_fin(Array.get(Cel, a, U32.from_nat(k)))

def write(a: Array<Cel>, +k: Nat, +v: U32) -> Array<Cel>:
  Array.set(Cel, a, U32.from_nat(k), CV{v})

def bump_fin(p: Array<Cel> & U32, +k: Nat, +v: U32) -> Array<Cel>:
  (a, x) = p
  write(a, k, U32.add(x, v))

def bump(a: Array<Cel>, +k: Nat, +v: U32) -> Array<Cel>:
  bump_fin(read(a, k), k, v)

# The cell that holds the total of the block at remaining depth q, offset o.
def cell_of(q: Nat, +base: Nat, +hq: Nat, +o: Nat) -> Nat:
  match q:
    case 0n:
      Nat.add(base, o)
    case 1n+r:
      Nat.add(o, hq)

def mk_c(p: Array<Cel> & Cel, g: Array<Cel>) -> Array<Cel> & Array<Cel> & Cel:
  (c, x) = p
  (c, (g, x))

def mk_g(p: Array<Cel> & Cel, c: Array<Cel>) -> Array<Cel> & Array<Cel> & Cel:
  (g, x) = p
  (c, (g, x))

# The cell a downward walk needs at remaining depth q: the block's tag, or
# the value itself at a leaf.
def pre_t(q: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +hq: Nat, +o: Nat) -> Array<Cel> & Array<Cel> & Cel:
  match q:
    case 0n:
      mk_c(Array.get(Cel, c, U32.from_nat(Nat.add(base, o))), g)
    case 1n+r:
      mk_g(Array.get(Cel, g, U32.from_nat(Nat.add(o, hq))), c)

# ---- public API ----

def new_at(+n: Nat, +d: Nat) -> SegTree:
  ST{n, d, pow2(d), Array.new(Cel, 1n+d, CV{0}), Array.new(Cel, d, CV{0})}

# n zero values.
def new(+n: Nat) -> SegTree:
  new_at(n, depth_for(n))

def length(s: SegTree) -> SegTree & Nat:
  match s:
    case ST{+n, d, b, c, g}:
      (ST{n, d, b, c, g}, n)

# ---- get ----

# h when the walk goes right (h <= i), 0 when it goes left. Choosing the
# step ARITHMETICALLY instead of branching on the side is what keeps the
# native loop branch-free: the index of a get is data, so a per-level
# conditional jump mispredicts about half the time (measured: segment_tree
# get small 22.8 ns branching against 8.0 ns branch-free, C 3.1 ns).
def step_of(right: Bool, +h: Nat) -> Nat:
  match right:
    case True{}:
      h
    case False{}:
      0n

def get_go(p: Nat, tr: Array<Cel> & Array<Cel> & Cel, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat) -> Array<Cel> & Array<Cel> & U32:
  match p tr:
    case 0n Tuple{c, Tuple{g, x}}:
      (c, (g, U32.add(cval(x), acc)))
    case 1n+ +q Tuple{c, Tuple{g, x}}:
      +m = step_of(Nat.is_le(h, i), h)
      get_go(q, pre_t(q, c, g, base, hh, Nat.add(o, m)), base, hh, Nat.div(hh, 2n), U32.add(acc, cval(x)), Nat.add(o, m), Nat.sub(i, m))

def get_walk(+d: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +i: Nat) -> Array<Cel> & Array<Cel> & U32:
  get_go(d, pre_t(d, c, g, base, Nat.div(base, 2n), 0n), base, Nat.div(base, 2n), Nat.div(Nat.div(base, 2n), 2n), 0, 0n, i)

def get_fin(c: Array<Cel>, p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  (g, x) = p
  (ST{n, d, b, c, g}, Done{x})

def get_done(t: Array<Cel> & Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  (c, gx) = t
  get_fin(c, gx, n, d, b)

def get_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, c: Array<Cel>, g: Array<Cel>, +i: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      get_done(get_walk(d, c, g, b, i), n, d, b)
    case False{}:
      (ST{n, d, b, c, g}, Fail{E.IndexOutOfRange{}})

# Value at index i.
def get(s: SegTree, +i: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  match s:
    case ST{+n, +d, +b, c, g}:
      get_if(Nat.is_lt(i, n), n, d, b, c, g, i)

# ---- recomputing a block's sum from its children ----

def fix3(p: Array<Cel> & Cel, c: Array<Cel>, +k: Nat, +q: Nat, +l: U32, +r: U32) -> Array<Cel> & Array<Cel>:
  (g, z) = p
  (write(c, k, U32.add(U32.add(l, r), U32.shln(cval(z), 1n+q))), g)

def fix2(p: Array<Cel> & Cel, g: Array<Cel>, +k: Nat, +q: Nat, +l: U32) -> Array<Cel> & Array<Cel>:
  (c, rr) = p
  fix3(Array.get(Cel, g, U32.from_nat(k)), c, k, q, l, cval(rr))

def fix1(p: Array<Cel> & Cel, g: Array<Cel>, +base: Nat, +hh: Nat, +orr: Nat, +k: Nat, +q: Nat) -> Array<Cel> & Array<Cel>:
  (c, ll) = p
  fix2(Array.get(Cel, c, U32.from_nat(cell_of(q, base, hh, orr))), g, k, q, cval(ll))

# cells[o + h] = total(left child) + total(right child) + tag << (q+1)
def fix(pr: Array<Cel> & Array<Cel>, +base: Nat, +h: Nat, +hh: Nat, +o: Nat, +q: Nat) -> Array<Cel> & Array<Cel>:
  (c, g) = pr
  fix1(Array.get(Cel, c, U32.from_nat(cell_of(q, base, hh, o))), g, base, hh, Nat.add(o, h), Nat.add(o, h), q)

# ---- set ----

def set_go(p: Nat, tr: Array<Cel> & Array<Cel> & Cel, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32) -> Array<Cel> & Array<Cel>:
  match p tr:
    case 0n Tuple{c, Tuple{g, x}}:
      (write(c, Nat.add(base, o), U32.sub(v, acc)), g)
    case 1n+ +q Tuple{c, Tuple{g, x}}:
      +m = step_of(Nat.is_le(h, i), h)
      fix(set_go(q, pre_t(q, c, g, base, hh, Nat.add(o, m)), base, hh, Nat.div(hh, 2n), U32.add(acc, cval(x)), Nat.add(o, m), Nat.sub(i, m), v), base, h, hh, o, q)

def set_walk(+d: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +i: Nat, +v: U32) -> Array<Cel> & Array<Cel>:
  set_go(d, pre_t(d, c, g, base, Nat.div(base, 2n), 0n), base, Nat.div(base, 2n), Nat.div(Nat.div(base, 2n), 2n), 0, 0n, i, v)

def set_done(pr: Array<Cel> & Array<Cel>, +n: Nat, +d: Nat, +b: Nat) -> SegTree & Result<&2, &2, E.Error, Unit>:
  (c, g) = pr
  (ST{n, d, b, c, g}, Done{Unit{}})

def set_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, c: Array<Cel>, g: Array<Cel>, +i: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      set_done(set_walk(d, c, g, b, i, v), n, d, b)
    case False{}:
      (ST{n, d, b, c, g}, Fail{E.IndexOutOfRange{}})

# Assign v at index i.
def set(s: SegTree, +i: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>:
  match s:
    case ST{+n, +d, +b, c, g}:
      set_if(Nat.is_lt(i, n), n, d, b, c, g, i, v)

# ---- prefix sums ----

def leaf_prefix(x: U32, i: Nat) -> U32:
  match i:
    case 0n:
      0
    case 1n+j:
      x

def p4both(p: Array<Cel> & Cel, g: Array<Cel>, +z: Cel) -> Array<Cel> & Array<Cel> & Cel & Cel:
  (c, tot) = p
  (c, (g, (z, tot)))

def p4g(p: Array<Cel> & Cel, c: Array<Cel>, +base: Nat, +hq2: Nat, +o: Nat, +r: Nat) -> Array<Cel> & Array<Cel> & Cel & Cel:
  (g, z) = p
  p4both(Array.get(Cel, c, U32.from_nat(cell_of(r, base, hq2, o))), g, z)

def p4c(p: Array<Cel> & Cel, g: Array<Cel>) -> Array<Cel> & Array<Cel> & Cel & Cel:
  (c, +x) = p
  (c, (g, (x, x)))

# A prefix walk needs the block's tag and, when it turns right, the total of
# the left child it skips over.
def pre_p(q: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +hq: Nat, +o: Nat) -> Array<Cel> & Array<Cel> & Cel & Cel:
  match q:
    case 0n:
      p4c(Array.get(Cel, c, U32.from_nat(Nat.add(base, o))), g)
    case 1n+r:
      p4g(Array.get(Cel, g, U32.from_nat(Nat.add(o, hq))), c, base, Nat.div(hq, 2n), o, r)

def prefix_go(p: Nat, tr: Array<Cel> & Array<Cel> & Cel & Cel, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +sum: U32, +o: Nat, +i: Nat, left: Bool) -> Array<Cel> & Array<Cel> & U32:
  match p tr left:
    case 0n Tuple{c, Tuple{g, Tuple{x, tot}}} _:
      (c, (g, U32.add(sum, leaf_prefix(U32.add(cval(x), acc), i))))
    case 1n+ +q Tuple{c, Tuple{g, Tuple{+z, tot}}} True{}:
      prefix_go(q, pre_p(q, c, g, base, hh, o), base, hh, Nat.div(hh, 2n), U32.add(acc, cval(z)), sum, o, i, Nat.is_lt(i, hh))
    case 1n+ +q Tuple{c, Tuple{g, Tuple{+z, tot}}} False{}:
      prefix_go(q, pre_p(q, c, g, base, hh, Nat.add(o, h)), base, hh, Nat.div(hh, 2n), U32.add(acc, cval(z)), U32.add(sum, U32.add(cval(tot), U32.shln(U32.add(acc, cval(z)), q))), Nat.add(o, h), Nat.sub(i, h), Nat.is_lt(Nat.sub(i, h), hh))

def prefix(+d: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +i: Nat) -> Array<Cel> & Array<Cel> & U32:
  prefix_go(d, pre_p(d, c, g, base, Nat.div(base, 2n), 0n), base, Nat.div(base, 2n), Nat.div(Nat.div(base, 2n), 2n), 0, 0, 0n, i, Nat.is_lt(i, Nat.div(base, 2n)))

# ---- range query ----

def query_fin(c: Array<Cel>, p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +hi: U32) -> SegTree & Result<&2, &2, E.Error, U32>:
  (g, lo) = p
  (ST{n, d, b, c, g}, Done{U32.sub(hi, lo)})

def query_sub(t: Array<Cel> & Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +hi: U32) -> SegTree & Result<&2, &2, E.Error, U32>:
  (c, gx) = t
  query_fin(c, gx, n, d, b, hi)

def query_mid(c: Array<Cel>, p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +l: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  (g, hi) = p
  query_sub(prefix(d, c, g, b, l), n, d, b, hi)

def query_lo(t: Array<Cel> & Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +l: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  (c, gx) = t
  query_mid(c, gx, n, d, b, l)

def query_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, c: Array<Cel>, g: Array<Cel>, +l: Nat, +r: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      query_lo(prefix(d, c, g, b, r), n, d, b, l)
    case False{}:
      (ST{n, d, b, c, g}, Fail{E.InvalidRange{}})

# Sum of the values with index in [l, r).
def range_query(s: SegTree, +l: Nat, +r: Nat) -> SegTree & Result<&2, &2, E.Error, U32>:
  match s:
    case ST{+n, +d, +b, c, g}:
      query_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), n, d, b, c, g, l, r)

# ---- lazy range addition ----

def leaf_padd(a: Array<Cel>, +k: Nat, i: Nat, +v: U32) -> Array<Cel>:
  match i:
    case 0n:
      a
    case 1n+j:
      bump(a, k, v)

# Add v to every value of the block at remaining depth q, offset o: one sum
# bump and one tag bump, never a walk.
def tag_c(q: Nat, c: Array<Cel>, +base: Nat, +hq: Nat, +o: Nat, +v: U32) -> Array<Cel>:
  match q:
    case 0n:
      bump(c, Nat.add(base, o), v)
    case 1n+r:
      bump(c, Nat.add(o, hq), U32.shln(v, 1n+r))

def tag_g(q: Nat, g: Array<Cel>, +hq: Nat, +o: Nat, +v: U32) -> Array<Cel>:
  match q:
    case 0n:
      g
    case 1n+r:
      bump(g, Nat.add(o, hq), v)

# Add v to the first i values of the block at remaining depth p, offset o.
def padd_go(p: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +h: Nat, +hh: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> Array<Cel> & Array<Cel>:
  match p left:
    case 0n _:
      (leaf_padd(c, Nat.add(base, o), i, v), g)
    case 1n+ +q True{}:
      fix(padd_go(q, c, g, base, hh, Nat.div(hh, 2n), o, i, v, Nat.is_lt(i, hh)), base, h, hh, o, q)
    case 1n+ +q False{}:
      fix(padd_go(q, tag_c(q, c, base, hh, o, v), tag_g(q, g, hh, o, v), base, hh, Nat.div(hh, 2n), Nat.add(o, h), Nat.sub(i, h), v, Nat.is_lt(Nat.sub(i, h), hh)), base, h, hh, o, q)

def padd(+d: Nat, c: Array<Cel>, g: Array<Cel>, +base: Nat, +i: Nat, +v: U32) -> Array<Cel> & Array<Cel>:
  padd_go(d, c, g, base, Nat.div(base, 2n), Nat.div(Nat.div(base, 2n), 2n), 0n, i, v, Nat.is_lt(i, Nat.div(base, 2n)))

def add_lo(pr: Array<Cel> & Array<Cel>, +n: Nat, +d: Nat, +b: Nat, +l: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>:
  (c, g) = pr
  set_done(padd(d, c, g, b, l, U32.sub(0, v)), n, d, b)

def add_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, c: Array<Cel>, g: Array<Cel>, +l: Nat, +r: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      add_lo(padd(d, c, g, b, r, v), n, d, b, l, v)
    case False{}:
      (ST{n, d, b, c, g}, Fail{E.InvalidRange{}})

# Add v to every value with index in [l, r).
def range_add(s: SegTree, +l: Nat, +r: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>:
  match s:
    case ST{+n, +d, +b, c, g}:
      add_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), n, d, b, c, g, l, r, v)

# ---- from_list ----

def fill(xs: List<&2, U32>, +i: Nat, s: SegTree) -> SegTree:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      fill(rest, 1n+i, Pair.fst(SegTree, Result<&2, &2, E.Error, Unit>, set(s, i, x)))

def count(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      1n+count(rest)

# Segment tree holding exactly the given values.
def from_list(+xs: List<&2, U32>) -> SegTree:
  fill(xs, 0n, new(count(xs)))

# ---- linear housekeeping ----

def burn_list(xs: List<Cel>) -> Unit:
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      burn_list(t)

# Releasing a cell array is dropping it: `Base.Array` is linear, so the
# runtime frees the block when the last reference is erased.
def burn(a: Array<Cel>) -> Unit:
  Unit{}

def burn2(u: Unit, v: Unit) -> Unit:
  match u v:
    case Unit{} Unit{}:
      Unit{}

def dispose(s: SegTree) -> Unit:
  match s:
    case ST{n, d, b, c, g}:
      burn2(burn(c), burn(g))

def clone_g(pc: Array<Cel> & Array<Cel>, pg: Array<Cel> & Array<Cel>, +n: Nat, +d: Nat, +b: Nat) -> SegTree & SegTree:
  (c1, c2) = pc
  (g1, g2) = pg
  (ST{n, d, b, c1, g1}, ST{n, d, b, c2, g2})

# Two independent trees with the same contents (the linear form of sharing).
def clone(s: SegTree) -> SegTree & SegTree:
  match s:
    case ST{+n, +d, +b, c, g}:
      clone_g(Array.clone(Cel, c), Array.clone(Cel, g), n, d, b)

# ---- trace runner ----

def obs_unit(r: SegTree & Result<&2, &2, E.Error, Unit>) -> SegTree & E.Obs:
  (s, x) = r
  (s, E.OUnit{x})

def obs_item(r: SegTree & Result<&2, &2, E.Error, U32>) -> SegTree & E.Obs:
  (s, x) = r
  (s, E.OItem{x})

def obs_nat(r: SegTree & Nat) -> SegTree & E.Obs:
  (s, x) = r
  (s, E.ONat{x})

def step(s: SegTree, op: E.Op) -> SegTree & E.Obs:
  match op:
    case E.Length{}:
      obs_nat(length(s))
    case E.Get{i}:
      obs_item(get(s, i))
    case E.Set{i, v}:
      obs_unit(set(s, i, v))
    case E.RangeQuery{l, r}:
      obs_item(range_query(s, l, r))
    case E.RangeAdd{l, r, v}:
      obs_unit(range_add(s, l, r, v))

def record(acc: List<&2, E.Obs>, r: SegTree & E.Obs) -> SegTree & List<&2, E.Obs>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(op: E.Op, st: SegTree & List<&2, E.Obs>) -> SegTree & List<&2, E.Obs>:
  (s, acc) = st
  record(acc, step(s, op))

def run_acc(ops: List<&2, E.Op>, st: SegTree & List<&2, E.Obs>) -> SegTree & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: SegTree & List<&2, E.Obs>) -> SegTree & List<&2, E.Obs>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, s: SegTree) -> SegTree & List<&2, E.Obs>:
  finish(run_acc(ops, (s, Nil{})))
