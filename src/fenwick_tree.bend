import Base
import ../types/fenwick_tree.bend as E

# Fenwick (binary indexed) tree over n U32 values; all sums wrap modulo 2^32
# (U32.add / U32.sub).
#
# Representation: ONE flat native `Base.Array` of 2^(depth+1) U32 cells, in
# the standard flat layout of an array-based Fenwick tree:
#
#   * the 2^depth VALUES are the cells 2^depth + j, j in [0, 2^depth);
#   * the internal node covering the half-open block [o, o + 2^p) of value
#     indices (p >= 1) stores the sum of that block's LEFT half -- exactly
#     the partial sum an array-based Fenwick tree keeps -- in the cell at the
#     block's split point, o + 2^(p-1), which is in [1, 2^depth) and is
#     distinct for every internal node;
#   * cell 0 is unused.
#
# Every step of every operation is therefore one `Array.get`/`Array.set` at a
# computed index plus index arithmetic (o -> o, o + 2^(p-1)), never a
# structural walk of a persistent node tree. `Base.Array` is a *linear* fixed-capacity
# array, so every operation takes the tree and gives it back, and a tree that
# is no longer needed is released with `dispose` (`clone` makes two
# independent copies), exactly as in src/bitset.bend and src/union_find.bend.
#
# Point addition walks the root-to-leaf path of index i, adding the delta to
# every cell whose left subtree contains i and to the leaf itself. A prefix
# sum walks the same path and adds the stored left-sum wherever the path
# turns right. Range sums are prefix differences (mod 2^32).
#
# Errors never change the state: add with index >= n fails with
# IndexOutOfRange; prefix_sum(e) with e > n and range_sum(l, r) unless
# l <= r <= n fail with InvalidRange.
#
# Capacity: `depth_for` stops at depth 30, so the cell array's own depth is
# at most 31 and every cell index is a representable U32 (Base's index
# masking over the array is then the identity). The laws about `new(n)`
# carry the explicit premise that n fits that capacity; every other law holds
# at every state satisfying the invariant, and the invariant implies the
# premise. `benchmarks/native/fenwick_tree.c` has the same bound.
#
# Cost: add / prefix_sum O(depth) indexed cell accesses; range_sum two such
# walks; new O(2^depth) (Base's array fill); from_list O(n log n); length
# O(1); dispose/clone O(2^depth).

type Cel is Data:
  CV{value: U32}

# `base` is 2^depth, cached so that no walk ever recomputes a power of two:
# the walks carry the current block's split offset `h` (2^(p-1)) and the
# next one `hh` (h/2, one machine division per level), exactly as the C
# reference carries `1u << (p-1)`.
type Fenwick is Type:
  FT{n: Nat, depth: Nat, base: Nat, cells: Array<Cel>}

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

# Branch decision for a node whose children have depth d and whose block
# starts at index 0: True = the left (lower) child holds index j.
def dec(d: Nat, +j: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+q:
      Nat.is_lt(j, pow2(q))

# 2^30 values: the capacity of the flat representation. The cell array then
# has depth 31, so every cell index is a representable U32.
def max_depth() -> Nat:
  30n

# The smallest depth whose 2^depth leaves hold n values, capped at
# max_depth. `fuel` bounds the search structurally, `cap` is 2^d and `done`
# is the exit test `n <= cap`.
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

# Cell k of the array (k < 2^(depth+1)).
def read(a: Array<Cel>, +k: Nat) -> Array<Cel> & U32:
  read_fin(Array.get(Cel, a, U32.from_nat(k)))

def write(a: Array<Cel>, +k: Nat, +v: U32) -> Array<Cel>:
  Array.set(Cel, a, U32.from_nat(k), CV{v})

def bump_fin(p: Array<Cel> & U32, +k: Nat, +v: U32) -> Array<Cel>:
  (a, x) = p
  write(a, k, U32.add(x, v))

# cells[k] += v
def bump(a: Array<Cel>, +k: Nat, +v: U32) -> Array<Cel>:
  bump_fin(read(a, k), k, v)

# The cell a walk reads at remaining depth q over the block starting at o:
# the value cell for a leaf, the split-point cell of the block otherwise.
# `hq` is 2^(q-1); it is unused when q is 0.
def pre(q: Nat, a: Array<Cel>, +base: Nat, +hq: Nat, +o: Nat) -> Array<Cel> & Cel:
  match q:
    case 0n:
      Array.get(Cel, a, U32.from_nat(Nat.add(base, o)))
    case 1n+r:
      Array.get(Cel, a, U32.from_nat(Nat.add(o, hq)))

# ---- public API ----

def new_at(+n: Nat, +d: Nat) -> Fenwick:
  FT{n, d, pow2(d), Array.new(Cel, 1n+d, CV{0})}

# n zero values.
def new(+n: Nat) -> Fenwick:
  new_at(n, depth_for(n))

def length(t: Fenwick) -> Fenwick & Nat:
  match t:
    case FT{+n, d, b, a}:
      (FT{n, d, b, a}, n)

# ---- point addition ----

# Add v to the value at index i of the block [o, o + 2^p), and to the split
# cell of every block on the way down whose LEFT half contains i. `h` is the
# current block's half size 2^(p-1) and `hh` is the next one.
def add_go(p: Nat, a: Array<Cel>, +base: Nat, +h: Nat, +hh: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> Array<Cel>:
  match p left:
    case 0n _:
      bump(a, Nat.add(base, o), v)
    case 1n+ +q True{}:
      add_go(q, bump(a, Nat.add(o, h), v), base, hh, Nat.div(hh, 2n), o, i, v, Nat.is_lt(i, hh))
    case 1n+ +q False{}:
      add_go(q, a, base, hh, Nat.div(hh, 2n), Nat.add(o, h), Nat.sub(i, h), v, Nat.is_lt(Nat.sub(i, h), hh))

def add_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, a: Array<Cel>, +i: Nat, +v: U32) -> Fenwick & Result<&2, &2, E.Error, Unit>:
  match ok:
    case True{}:
      (FT{n, d, b, add_go(d, a, b, Nat.div(b, 2n), Nat.div(Nat.div(b, 2n), 2n), 0n, i, v, Nat.is_lt(i, Nat.div(b, 2n)))}, Done{Unit{}})
    case False{}:
      (FT{n, d, b, a}, Fail{E.IndexOutOfRange{}})

# Add delta to the value at index i.
def add(f: Fenwick, +i: Nat, +v: U32) -> Fenwick & Result<&2, &2, E.Error, Unit>:
  match f:
    case FT{+n, +d, +b, a}:
      add_if(Nat.is_lt(i, n), n, d, b, a, i, v)

# ---- prefix sums ----

def leaf_prefix(x: U32, i: Nat) -> U32:
  match i:
    case 0n:
      0
    case 1n+j:
      x

# Sum of the first i values of the block [o, o + 2^p), added to the
# accumulator. The cell of the current level is read by the CALLER and
# arrives as `pr`: Bend has no mutual recursion, so the classical "stored
# left sum plus the rest" is accumulated on the way down instead of added on
# the way back up, and the read of the next level's cell happens in the
# branch that recurses. One indexed read per level, like the C reference.
def prefix_go(p: Nat, pr: Array<Cel> & Cel, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat, left: Bool) -> Array<Cel> & U32:
  match p pr left:
    case 0n Tuple{a, x} _:
      (a, U32.add(acc, leaf_prefix(cval(x), i)))
    case 1n+ +q Tuple{a, x} True{}:
      prefix_go(q, pre(q, a, base, hh, o), base, hh, Nat.div(hh, 2n), acc, o, i, Nat.is_lt(i, hh))
    case 1n+ +q Tuple{a, x} False{}:
      prefix_go(q, pre(q, a, base, hh, Nat.add(o, h)), base, hh, Nat.div(hh, 2n), U32.add(acc, cval(x)), Nat.add(o, h), Nat.sub(i, h), Nat.is_lt(Nat.sub(i, h), hh))

def prefix(+d: Nat, a: Array<Cel>, +b: Nat, +e: Nat) -> Array<Cel> & U32:
  prefix_go(d, pre(d, a, b, Nat.div(b, 2n), 0n), b, Nat.div(b, 2n), Nat.div(Nat.div(b, 2n), 2n), 0, 0n, e, Nat.is_lt(e, Nat.div(b, 2n)))

def prefix_done(p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  (a, s) = p
  (FT{n, d, b, a}, Done{s})

def prefix_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, a: Array<Cel>, +e: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      prefix_done(prefix(d, a, b, e), n, d, b)
    case False{}:
      (FT{n, d, b, a}, Fail{E.InvalidRange{}})

# Sum of the values with index in [0, e).
def prefix_sum(f: Fenwick, +e: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  match f:
    case FT{+n, +d, +b, a}:
      prefix_if(Nat.is_le(e, n), n, d, b, a, e)

# ---- range sums ----

def range_fin(p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +hi: U32) -> Fenwick & Result<&2, &2, E.Error, U32>:
  (a, lo) = p
  (FT{n, d, b, a}, Done{U32.sub(hi, lo)})

def range_lo(p: Array<Cel> & U32, +n: Nat, +d: Nat, +b: Nat, +l: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  (a, hi) = p
  range_fin(prefix(d, a, b, l), n, d, b, hi)

def range_if(ok: Bool, +n: Nat, +d: Nat, +b: Nat, a: Array<Cel>, +l: Nat, +r: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  match ok:
    case True{}:
      range_lo(prefix(d, a, b, r), n, d, b, l)
    case False{}:
      (FT{n, d, b, a}, Fail{E.InvalidRange{}})

# Sum of the values with index in [l, r).
def range_sum(f: Fenwick, +l: Nat, +r: Nat) -> Fenwick & Result<&2, &2, E.Error, U32>:
  match f:
    case FT{+n, +d, +b, a}:
      range_if(Bool.and(Nat.is_le(l, r), Nat.is_le(r, n)), n, d, b, a, l, r)

# ---- from_list ----

def fill(xs: List<&2, U32>, +i: Nat, f: Fenwick) -> Fenwick:
  match xs:
    case Nil{}:
      f
    case Con{x, rest}:
      fill(rest, 1n+i, Pair.fst(Fenwick, Result<&2, &2, E.Error, Unit>, add(f, i, x)))

def count(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      1n+count(rest)

# Fenwick tree holding exactly the given values.
def from_list(+xs: List<&2, U32>) -> Fenwick:
  fill(xs, 0n, new(count(xs)))

# ---- linear housekeeping ----

def burn_list(xs: List<Cel>) -> Unit:
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      burn_list(t)

# Releasing the cell array is dropping it: `Base.Array` is linear, so the
# runtime frees the block when the last reference is erased. (The earlier
# `burn` walked Array.to_list, which is O(capacity) and built a cons cell per
# cell of the array; `burn_list` is kept because proofs/fenwick_tree/state.bend
# states the disposal law about it.)
def burn(a: Array<Cel>) -> Unit:
  Unit{}

# Release a tree. `Base.Array` is linear, so a caller that stops using a tree
# has to say so; every operation above gives the tree back instead.
def dispose(t: Fenwick) -> Unit:
  match t:
    case FT{n, d, b, a}:
      burn(a)

def clone_fin(p: Array<Cel> & Array<Cel>, +n: Nat, +d: Nat, +b: Nat) -> Fenwick & Fenwick:
  (x, y) = p
  (FT{n, d, b, x}, FT{n, d, b, y})

# Two independent trees with the same contents (the linear form of sharing).
def clone(t: Fenwick) -> Fenwick & Fenwick:
  match t:
    case FT{+n, +d, +b, a}:
      clone_fin(Array.clone(Cel, a), n, d, b)

# ---- trace runner ----

def obs_unit(r: Fenwick & Result<&2, &2, E.Error, Unit>) -> Fenwick & E.Obs:
  (f, x) = r
  (f, E.OUnit{x})

def obs_sum(r: Fenwick & Result<&2, &2, E.Error, U32>) -> Fenwick & E.Obs:
  (f, x) = r
  (f, E.OSum{x})

def obs_nat(r: Fenwick & Nat) -> Fenwick & E.Obs:
  (f, x) = r
  (f, E.ONat{x})

def step(f: Fenwick, op: E.Op) -> Fenwick & E.Obs:
  match op:
    case E.Length{}:
      obs_nat(length(f))
    case E.Add{i, v}:
      obs_unit(add(f, i, v))
    case E.PrefixSum{e}:
      obs_sum(prefix_sum(f, e))
    case E.RangeSum{l, r}:
      obs_sum(range_sum(f, l, r))

def record(acc: List<&2, E.Obs>, r: Fenwick & E.Obs) -> Fenwick & List<&2, E.Obs>:
  (f, o) = r
  (f, Con{o, acc})

def step_acc(op: E.Op, st: Fenwick & List<&2, E.Obs>) -> Fenwick & List<&2, E.Obs>:
  (f, acc) = st
  record(acc, step(f, op))

def run_acc(ops: List<&2, E.Op>, st: Fenwick & List<&2, E.Obs>) -> Fenwick & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: Fenwick & List<&2, E.Obs>) -> Fenwick & List<&2, E.Obs>:
  (f, acc) = st
  (f, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, f: Fenwick) -> Fenwick & List<&2, E.Obs>:
  finish(run_acc(ops, (f, Nil{})))
