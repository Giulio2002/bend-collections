import Base
import ../types/union_find.bend as E
import ./pow2.bend as P2

# Disjoint-set union over the elements 0 .. n-1, stored in a native
# Base.Array arena.
#
# Representation: UF{n, depth, roots, sizes, members, count}. The last three
# are three PARALLEL Base.Arrays of 2^depth slots each, with 2^depth >= n,
# all indexed by element. `roots[x]` is x's class representative;
# `sizes[r]` and `members[r]` are meaningful at a representative r and hold
# its exact class size and the list of its members.
#
# The arenas are deliberately narrow (one field each) rather than one array
# of three-field records: reading a wide record out of a Base.Array costs per
# field (a measured 6.5 ns for a 3-field cell against 1.5 ns for a 1-field
# one), so `find` -- one read of `roots` -- must not have to touch the other
# two.
#
# `Base.Array` is a *linear* fixed-capacity array with O(1) indexed read and
# write, so every operation takes the structure and gives it back, exactly
# like src/dynamic_array.bend and src/bitset.bend, and a structure that is no
# longer needed is released with `dispose`.
#
# Union by size with eager full compression: the representative of the larger
# class survives (ties: the class of the first argument) and every member of
# the smaller class is repointed at it immediately. Because every element
# points straight at its representative, `find` is a single indexed read and
# never has to walk or rewrite a path. This is the "documented
# Bend-appropriate equivalent" of union-by-size with path compression that
# the objective allows: it performs the compression eagerly at union time
# instead of lazily at find time, so find needs no state change at all --
# which matters in Bend, where a find that rewrote the structure would have
# to thread a new state through every read. benchmarks/native/union_find.c
# implements exactly this algorithm, so the comparison is same-algorithm.
#
# What is proved about the cost: nothing. The source-level cost statement is
# that `find`, `connected`, `component_size` and `component_count` are a
# constant number of indexed cell reads, and `union` performs one indexed
# write per member of the smaller class plus a constant number of reads. The
# usual amortised bound for repointing the smaller class (each element is
# repointed at most log2 n times because its class at least doubles) is a
# classical argument that is NOT machine-checked here, so it is stated as
# documentation, not as a theorem.
#
# Capacity: `depth_for` stops at depth 31, so every slot index is a
# representable U32 and Base's index masking over the arena is the identity.
# The laws about `new(n)` carry the explicit premise that n fits that
# capacity (proofs/union_find.bend `capacity`); every other law holds at
# every state satisfying the invariant, and the invariant implies the
# premise.
#
# Errors never change the state: any index >= n yields OutOfRange.

# Three parallel arenas rather than one array of records: a read of a
# one-field slot costs a fraction of a read of a three-field slot in the
# native backend (measured: 1.5 ns against 6.5 ns), and `find`, `connected`
# and `component_size` only ever need the representative. This is also the
# layout benchmarks/native/union_find.c uses.

type Nt is Data:
  N{v: Nat}

type Ms is Data:
  M{v: List<&2, Nat>}

type UnionFind is Type:
  UF{n: Nat, depth: Nat, roots: Array<Nt>, sizes: Array<Nt>, mems: Array<Ms>, count: Nat}

def nval(x: Nt) -> Nat:
  match x:
    case N{v}:
      v

def mval(x: Ms) -> List<&2, Nat>:
  match x:
    case M{v}:
      v

# ---- capacity ----

# 2^31 slots: see the capacity note above. The constant is never materialised
# as a value; `depth_for` simply stops at this depth.
def max_depth() -> Nat:
  31n

# The smallest depth whose 2^depth slots hold n elements, capped at
# max_depth. `fuel` bounds the search structurally, `cap` is 2^d and `done`
# is the exit test `n <= cap`, so a depth that comes out of the loop below
# the cap always satisfies it (proofs/union_find/depth.bend).
def depth_go(fuel: Nat, +n: Nat, d: Nat, +cap: Nat, done: Bool) -> Nat:
  match fuel done:
    case 0n _:
      d
    case 1n+ +f True{}:
      d
    case 1n+ +f False{}:
      depth_go(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.double(cap)))

def depth_for(+n: Nat) -> Nat:
  depth_go(max_depth(), n, 0n, 1n, Nat.is_le(n, 1n))

# ---- arena access ----

def read_nat_fin(p: Array<Nt> & Nt) -> Array<Nt> & Nat:
  (a, x) = p
  (a, nval(x))

# Slot x of a Nat arena (x < 2^depth).
def read_nat(a: Array<Nt>, +d: Nat, +x: Nat) -> Array<Nt> & Nat:
  read_nat_fin(Array.get(Nt, a, U32.from_nat(x)))

def write_nat(a: Array<Nt>, +d: Nat, +x: Nat, +v: Nat) -> Array<Nt>:
  Array.set(Nt, a, U32.from_nat(x), N{v})

def read_ms_fin(p: Array<Ms> & Ms) -> Array<Ms> & List<&2, Nat>:
  (a, x) = p
  (a, mval(x))

def read_ms(a: Array<Ms>, +d: Nat, +x: Nat) -> Array<Ms> & List<&2, Nat>:
  read_ms_fin(Array.get(Ms, a, U32.from_nat(x)))

def write_ms(a: Array<Ms>, +d: Nat, +x: Nat, +v: List<&2, Nat>) -> Array<Ms>:
  Array.set(Ms, a, U32.from_nat(x), M{v})

# ---- release and copy ----

# Releasing the arenas is dropping them: `Base.Array` is linear, so the
# runtime frees each block when its last reference is erased (as in
# src/bitset.bend).
def dispose(s: UnionFind) -> Unit:
  match s:
    case UF{n, d, r, z, m, c}:
      Unit{}

def clone_m(pr: Array<Nt> & Array<Nt>, pz: Array<Nt> & Array<Nt>, pm: Array<Ms> & Array<Ms>, +n: Nat, +d: Nat, +c: Nat) -> UnionFind & UnionFind:
  (r1, r2) = pr
  (z1, z2) = pz
  (m1, m2) = pm
  (UF{n, d, r1, z1, m1, c}, UF{n, d, r2, z2, m2, c})

# Two independent structures with the same contents (the linear form of
# sharing).
def clone(s: UnionFind) -> UnionFind & UnionFind:
  match s:
    case UF{+n, +d, r, z, m, +c}:
      clone_m(Array.clone(Nt, r), Array.clone(Nt, z), Array.clone(Ms, m), n, d, c)

# ---- the constructor ----

# `new` allocates and initialises all three arenas immediately. Slot j of
# the roots arena holds j and slot j of the member arena holds [j]; the size
# arena is uniformly 1. The first two are filled by flat loops over a
# uniform block (slot j := value for j = k-1 .. 0), so the constructor
# compiles to native loops over blocks rather than a segmented continuation
# (proofs/union_find/flat.bend proves what the loops build).
def iota_go(k: Nat, a: Array<Nt>) -> Array<Nt>:
  match k:
    case 0n:
      a
    case 1n+ +j:
      iota_go(j, Array.set(Nt, a, U32.from_nat(j), N{j}))

def solo_go(k: Nat, a: Array<Ms>) -> Array<Ms>:
  match k:
    case 0n:
      a
    case 1n+ +j:
      solo_go(j, Array.set(Ms, a, U32.from_nat(j), M{Con{j, Nil{}}}))

# Every element of 0 .. n-1 in its own class, arenas allocated.
def roots0(+d: Nat) -> Array<Nt>:
  iota_go(P2.pow2t(d), Array.new(Nt, d, N{0n}))

def sizes0(+d: Nat) -> Array<Nt>:
  Array.new(Nt, d, N{1n})

def mems0(+d: Nat) -> Array<Ms>:
  solo_go(P2.pow2t(d), Array.new(Ms, d, M{Nil{}}))

def new_at(+n: Nat, +d: Nat) -> UnionFind:
  UF{n, d, roots0(d), sizes0(d), mems0(d), n}

def new(+n: Nat) -> UnionFind:
  new_at(n, depth_for(n))

# ---- find ----

def find_read(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  (r, v) = p
  (UF{n, d, r, z, m, c}, Done{v})

def find_if(ok: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +x: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  match ok:
    case True{}:
      find_read(read_nat(r, d, x), n, d, z, m, c)
    case False{}:
      (UF{n, d, r, z, m, c}, Fail{E.OutOfRange{}})

# Representative of x's class.
def find(s: UnionFind, +x: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  match s:
    case UF{+n, +d, r, z, m, +c}:
      find_if(Nat.is_lt(x, n), n, d, r, z, m, c, x)

# ---- connected ----

def both(+n: Nat, +a: Nat, +b: Nat) -> Bool:
  Bool.and(Nat.is_lt(a, n), Nat.is_lt(b, n))

def conn_b(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (r, +v) = p
  (UF{n, d, r, z, m, c}, Done{Nat.is_eq(ra, v)})

def conn_a(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (r, v) = p
  conn_b(read_nat(r, d, y), n, d, z, m, c, v)

def connected_if(ok: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +x: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match ok:
    case True{}:
      conn_a(read_nat(r, d, x), n, d, z, m, c, y)
    case False{}:
      (UF{n, d, r, z, m, c}, Fail{E.OutOfRange{}})

def connected(s: UnionFind, +x: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match s:
    case UF{+n, +d, r, z, m, +c}:
      connected_if(both(n, x, y), n, d, r, z, m, c, x, y)

# ---- component_size ----

def size_root(p: Array<Nt> & Nat, +n: Nat, +d: Nat, r: Array<Nt>, m: Array<Ms>, +c: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  (z, v) = p
  (UF{n, d, r, z, m, c}, Done{v})

def size_at(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  (r, v) = p
  size_root(read_nat(z, d, v), n, d, r, m, c)

def size_if(ok: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +x: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  match ok:
    case True{}:
      size_at(read_nat(r, d, x), n, d, z, m, c)
    case False{}:
      (UF{n, d, r, z, m, c}, Fail{E.OutOfRange{}})

# Number of elements in x's class.
def component_size(s: UnionFind, +x: Nat) -> UnionFind & Result<&2, &2, E.Error, Nat>:
  match s:
    case UF{+n, +d, r, z, m, +c}:
      size_if(Nat.is_lt(x, n), n, d, r, z, m, c, x)

# ---- component_count ----

def component_count(s: UnionFind) -> UnionFind & Nat:
  match s:
    case UF{n, d, r, z, m, +c}:
      (UF{n, d, r, z, m, c}, c)

# ---- union ----

# Point every listed member at `big`.
def relink(ms: List<&2, Nat>, r: Array<Nt>, +d: Nat, +big: Nat) -> Array<Nt>:
  match ms:
    case Nil{}:
      r
    case Con{+q, rest}:
      relink(rest, write_nat(r, d, q, big), d, big)

# The two roots and their sizes are known; `msb` and `mss` are the member
# lists of the big and small classes.
def union_write(+n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +big: Nat, +tot: Nat, +msb: List<&2, Nat>, +mss: List<&2, Nat>) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (UF{n, d, relink(mss, r, d, big), write_nat(z, d, big, tot), write_ms(m, d, big, List.reverse.go(&2, Nat, List.reverse.go(&2, Nat, mss, Nil{}), msb)), Nat.sub(c, 1n)}, Done{True{}})

def union_msb(p: Array<Ms> & List<&2, Nat>, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, +c: Nat, +big: Nat, +tot: Nat, +mss: List<&2, Nat>) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (m, msb) = p
  union_write(n, d, r, z, m, c, big, tot, msb, mss)

def union_mss(p: Array<Ms> & List<&2, Nat>, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, +c: Nat, +big: Nat, +small: Nat, +tot: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (m, mss) = p
  union_msb(read_ms(m, d, big), n, d, r, z, c, big, tot, mss)

def union_pick(keep_a: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat, +rb: Nat, +tot: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match keep_a:
    case True{}:
      union_mss(read_ms(m, d, rb), n, d, r, z, c, ra, rb, tot)
    case False{}:
      union_mss(read_ms(m, d, ra), n, d, r, z, c, rb, ra, tot)

def union_zb(p: Array<Nt> & Nat, +n: Nat, +d: Nat, r: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat, +rb: Nat, +za: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (z, +zb) = p
  union_pick(Nat.is_le(zb, za), n, d, r, z, m, c, ra, rb, Nat.add(za, zb))

def union_za(p: Array<Nt> & Nat, +n: Nat, +d: Nat, r: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat, +rb: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (z, za) = p
  union_zb(read_nat(z, d, rb), n, d, r, m, c, ra, rb, za)

def union_roots(same: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat, +rb: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match same:
    case True{}:
      (UF{n, d, r, z, m, c}, Done{False{}})
    case False{}:
      union_za(read_nat(z, d, ra), n, d, r, m, c, ra, rb)

def union_b(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat, +ra: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (r, +rb) = p
  union_roots(Nat.is_eq(ra, rb), n, d, r, z, m, c, ra, rb)

def union_a(p: Array<Nt> & Nat, +n: Nat, +d: Nat, z: Array<Nt>, m: Array<Ms>, +c: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  (r, ra) = p
  union_b(read_nat(r, d, y), n, d, z, m, c, ra)

def union_if(ok: Bool, +n: Nat, +d: Nat, r: Array<Nt>, z: Array<Nt>, m: Array<Ms>, +c: Nat, +x: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match ok:
    case True{}:
      union_a(read_nat(r, d, x), n, d, z, m, c, y)
    case False{}:
      (UF{n, d, r, z, m, c}, Fail{E.OutOfRange{}})

# Join the classes of a and b; Done{True} if they were distinct.
def union(s: UnionFind, +x: Nat, +y: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>:
  match s:
    case UF{+n, +d, r, z, m, +c}:
      union_if(both(n, x, y), n, d, r, z, m, c, x, y)

# ---- trace runner ----

def obs_bool(r: UnionFind & Result<&2, &2, E.Error, Bool>) -> UnionFind & E.Obs:
  (s, x) = r
  (s, E.OBool{x})

def obs_item(r: UnionFind & Result<&2, &2, E.Error, Nat>) -> UnionFind & E.Obs:
  (s, x) = r
  (s, E.OItem{x})

def obs_nat(r: UnionFind & Nat) -> UnionFind & E.Obs:
  (s, x) = r
  (s, E.ONat{x})

def step(s: UnionFind, op: E.Op) -> UnionFind & E.Obs:
  match op:
    case E.Find{x}:
      obs_item(find(s, x))
    case E.Union{a, b}:
      obs_bool(union(s, a, b))
    case E.Connected{a, b}:
      obs_bool(connected(s, a, b))
    case E.ComponentSize{x}:
      obs_item(component_size(s, x))
    case E.ComponentCount{}:
      obs_nat(component_count(s))

def record(acc: List<&2, E.Obs>, r: UnionFind & E.Obs) -> UnionFind & List<&2, E.Obs>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(op: E.Op, st: UnionFind & List<&2, E.Obs>) -> UnionFind & List<&2, E.Obs>:
  (s, acc) = st
  record(acc, step(s, op))

def run_acc(ops: List<&2, E.Op>, st: UnionFind & List<&2, E.Obs>) -> UnionFind & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: UnionFind & List<&2, E.Obs>) -> UnionFind & List<&2, E.Obs>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, s: UnionFind) -> UnionFind & List<&2, E.Obs>:
  finish(run_acc(ops, (s, Nil{})))
