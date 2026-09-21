import Base
import ../types/graph.bend as E

# Finite simple graph over U32 vertex ids, directed or undirected (fixed at
# construction).
#
# Representation: INDEXED VERTEX SLOTS plus ADJACENCY BLOCKS, the layout an
# optimized C implementation would use for a sorted adjacency structure.
#
#   ids : Array<U32>          the vertex ids, ASCENDING, in slots [lo, hi)
#   adj : Array<Array<U32>>   slot i holds the adjacency block of ids[i]
#
# Both are native `Base.Array`s. Bend 2.0.16 lowers a `Base.Array` to an
# indexed memory block: `Array.get`/`Array.set`/`Array.swap` compile to one
# `blk_at` index computation plus a direct `blk_read`/`blk_write`; the
# ALeaf/ANode tree in Base is the logical model the checker reasons about,
# not the native layout (see docs/C_EQUIVALENCE.md). `Array<Array<U32>>` is
# a block of element terms, each pointing at its own U32 block, so reading a
# vertex's adjacency block is one indexed load, like a C `uint32_t **`.
#
# An adjacency block is a single power-of-two U32 block with a 3 word header:
#   b[0] = deg    the number of neighbours stored
#   b[1] = size   the block's total word count (a power of two)
#   b[2] = lcap   log2(size), the fuel bound for a binary search in it
#   b[3 .. 3+deg) the neighbour ids, ASCENDING
# so one indexed load of `adj[i]` yields the degree, the capacity and the
# neighbours together (array of structs, not parallel arrays: the header and
# the entries are read together on every edge operation).
#
# The vertex id is EXTERNAL and arbitrary in U32; the slot index is internal.
# The id-to-slot map is the sorted `ids` block searched by binary search, so
# no id is reserved, no density is assumed, and enumeration is already
# sorted. Neighbour entries are external ids too, so inserting or deleting a
# vertex slot never renumbers any edge.
#
# Policies (unchanged): isolated vertices are allowed; add_vertex of an
# existing vertex fails with VertexExists; edge operations fail with
# VertexNotFound when an endpoint is missing; self-loops fail with SelfLoop;
# adding an existing edge succeeds and changes nothing; removing a missing
# edge fails with EdgeNotFound; remove_vertex deletes all incident edges.
# Every failure returns the state unchanged.
#
# Cost (V vertices, D = degree of the vertex touched):
#   has_vertex, and the lookup part of every other operation  O(log V) loads
#   has_edge                                                  O(log V + log D)
#   add_edge / remove_edge   O(log V + log D) plus O(D) words moved inside
#                            the one adjacency block that changes
#   add_vertex insert / remove_vertex slot removal            O(V) words moved
#   neighbors O(D), vertices O(V), edges O(V + E)
#   remove_vertex strip O(V log D) - v is removed from EVERY block, in both
#     directions, exactly as the C reference's `strip` walks every vertex's
#     set (benchmarks/native/graph.c); in-edges are not indexed
#     (docs/C_EQUIVALENCE.md explains why a reverse adjacency index is not
#     maintained: it doubles every edge update to speed up only vertex
#     deletion).
# The sorted-block choice trades O(log V) tree insertion for O(V) contiguous
# moves, the same trade a C flat_map / CSR adjacency makes; every lookup,
# every traversal and every edge update is a contiguous indexed access.
#
# Capacity: a block's word count is a power of two and at most 2^31, so every
# index handed to Base is below 2^31 and Base's index masking is the
# identity; lo + hi inside a binary search stays below 2^32 and never wraps.

type Graph is Type:
  G{dir: Bool, lo: U32, hi: U32, cap: U32, depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>}

def zeros(+d: Nat) -> Array<U32>:
  Array.new(U32, d, 0)

# A fresh adjacency block: four words, deg = 0, size = 4, lcap = 2, so it has
# room for one neighbour before it has to grow.
def empty_blk() -> Array<U32>:
  Array.set(U32, Array.set(U32, zeros(2n), 1, 4), 2, 2)

# 2^d unused slots: each holds a one word placeholder block, which costs one
# allocation and is overwritten by a real block when a vertex takes the slot.
def spare_blks(+d: Nat) -> Array<Array<U32>>:
  match d:
    case 0n:
      ALeaf{zeros(0n)}
    case 1n+p:
      ANode{spare_blks(p), spare_blks(p)}

def new(dir: Bool) -> Graph:
  G{dir, 0, 0, 1, 0n, zeros(0n), spare_blks(0n)}

# ---- binary search over a sorted U32 region [lo, hi) of one block ----

type Fnd is Type:
  FD{a: Array<U32>, lo: U32, hi: U32}

def fnd_side(+lo: U32, +hi: U32, +mid: U32, a: Array<U32>, less: Bool) -> Fnd:
  match less:
    case True{}:
      FD{a, U32.inc(mid), hi}
    case False{}:
      FD{a, lo, mid}

def fnd_at(+v: U32, +lo: U32, +hi: U32, +mid: U32, r: Array<U32> & U32) -> Fnd:
  (a, +x) = r
  fnd_side(lo, hi, mid, a, U32.is_lt(x, v))

def fnd_mid(+v: U32, +lo: U32, +hi: U32, a: Array<U32>, +mid: U32) -> Fnd:
  fnd_at(v, lo, hi, mid, Array.get(U32, a, mid))

# The midpoint of [lo, hi), written without U32.add: with d = hi - lo,
#   mid = hi - (d - d/2) = lo + d/2,
# so lo <= mid < hi whenever lo < hi. (Addition is avoided throughout: its
# Nat meaning would need a 2^32 bound, which the checker cannot expand,
# while sub/shr/inc all have bounded bridges -- see proofs/graph/.)
def mid_sub(+hi: U32, +d: U32) -> U32:
  U32.sub(hi, U32.sub(d, U32.shr(d)))

def mid_of(+lo: U32, +hi: U32) -> U32:
  mid_sub(hi, U32.sub(hi, lo))

def fnd_live(+v: U32, +lo: U32, +hi: U32, a: Array<U32>, live: Bool) -> Fnd:
  match live:
    case False{}:
      FD{a, lo, hi}
    case True{}:
      fnd_mid(v, lo, hi, a, mid_of(lo, hi))

def fnd_one(+v: U32, s: Fnd) -> Fnd:
  FD{a, +lo, +hi} = s
  fnd_live(v, lo, hi, a, U32.is_lt(lo, hi))

# `fuel` bounds the number of halvings: the region has at most 2^(fuel-1)
# entries. Once lo = hi every further step is the identity.
def fnd_go(fuel: Nat, +v: U32, s: Fnd) -> Fnd:
  match fuel:
    case 0n:
      s
    case 1n+f:
      fnd_go(f, v, fnd_one(v, s))

# The lower bound, plus whether the entry there is v.
type Loc is Type:
  LC{a: Array<U32>, i: U32, found: Bool}

def loc_chk(+i: U32, +v: U32, r: Array<U32> & U32) -> Loc:
  (a, +x) = r
  LC{a, i, U32.is_eq(x, v)}

def loc_in(+v: U32, a: Array<U32>, +i: U32, ok: Bool) -> Loc:
  match ok:
    case False{}:
      LC{a, i, False{}}
    case True{}:
      loc_chk(i, v, Array.get(U32, a, i))

def loc_end(+v: U32, +hi: U32, s: Fnd) -> Loc:
  FD{a, +i, h} = s
  loc_in(v, a, i, U32.is_lt(i, hi))

# Locate vertex v among the n sorted ids (2^depth >= n bounds the search).
def locate(+depth: Nat, +v: U32, +lo: U32, +hi: U32, ids: Array<U32>) -> Loc:
  loc_end(v, hi, fnd_go(1n+depth, v, FD{ids, lo, hi}))

# ---- adjacency block header ----

type Hdr is Type:
  HD{b: Array<U32>, deg: U32, size: U32, lcap: U32}

def hdr3(+deg: U32, +size: U32, r: Array<U32> & U32) -> Hdr:
  (b, +l) = r
  HD{b, deg, size, l}

def hdr2(+deg: U32, r: Array<U32> & U32) -> Hdr:
  (b, +s) = r
  hdr3(deg, s, Array.get(U32, b, 2))

def hdr1(r: Array<U32> & U32) -> Hdr:
  (b, +d) = r
  hdr2(d, Array.get(U32, b, 1))

def header(b: Array<U32>) -> Hdr:
  hdr1(Array.get(U32, b, 0))

# One past the last entry (3 + deg) and the last entry (2 + deg), written
# with inc so that the Nat bridge is definitional.
def ent_end(+deg: U32) -> U32:
  U32.inc(U32.inc(U32.inc(deg)))

def ent_last(+deg: U32) -> U32:
  U32.inc(U32.inc(deg))

# Locate neighbour w in a block whose header has already been read.
def blk_find(b: Array<U32>, +deg: U32, +lcap: U32, +w: U32) -> Loc:
  loc_end(w, ent_end(deg), fnd_go(1n+U32.to_nat(lcap), w, FD{b, 3, ent_end(deg)}))

# ---- moving words ----

def shr_put(+j: U32, r: Array<U32> & U32) -> Array<U32>:
  (a, x) = r
  Array.set(U32, a, j, x)

# a[j] <- a[j-1] for `fuel` descending js.
def shr_go(fuel: Nat, +j: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      shr_go(f, U32.sub(j, 1), shr_put(j, Array.get(U32, a, U32.sub(j, 1))))

def shl_put(+j: U32, r: Array<U32> & U32) -> Array<U32>:
  (a, x) = r
  Array.set(U32, a, j, x)

# a[j] <- a[j+1] for `fuel` ascending js.
def shl_go(fuel: Nat, +j: U32, a: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      shl_go(f, U32.inc(j), shl_put(j, Array.get(U32, a, U32.inc(j))))

def shra_put(+j: U32, r: Array<Array<U32>> & Array<U32>) -> Array<Array<U32>>:
  (a, b) = r
  Array.set(Array<U32>, a, j, b)

# adj[j] <- adj[j-1]; the vacated slot keeps a one word placeholder block
# which the next move (or the final store) overwrites.
def shra_go(fuel: Nat, +j: U32, a: Array<Array<U32>>) -> Array<Array<U32>>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      shra_go(f, U32.sub(j, 1), shra_put(j, Array.swap(Array<U32>, a, U32.sub(j, 1), zeros(0n))))

def shla_put(+j: U32, r: Array<Array<U32>> & Array<U32>) -> Array<Array<U32>>:
  (a, b) = r
  Array.set(Array<U32>, a, j, b)

def shla_go(fuel: Nat, +j: U32, a: Array<Array<U32>>) -> Array<Array<U32>>:
  match fuel:
    case 0n:
      a
    case 1n+f:
      shla_go(f, U32.inc(j), shla_put(j, Array.swap(Array<U32>, a, U32.inc(j), zeros(0n))))

# ---- inserting and deleting one neighbour entry ----

# Double the block: the old block is the lower half, so every entry keeps its
# index; the header records the new size.
def blk_grow(b: Array<U32>, +size: U32, +lcap: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, ANode{b, zeros(U32.to_nat(lcap))}, 1, U32.shl(size)), 2, U32.inc(lcap))

# Insert w at entry index q of a block that has room.
def blk_put(b: Array<U32>, +deg: U32, +q: U32, +w: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, shr_go(U32.to_nat(U32.sub(ent_end(deg), q)), ent_end(deg), b), q, w), 0, U32.inc(deg))

def blk_add(b: Array<U32>, +deg: U32, +size: U32, +lcap: U32, +q: U32, +w: U32, room: Bool) -> Array<U32>:
  match room:
    case True{}:
      blk_put(b, deg, q, w)
    case False{}:
      blk_put(blk_grow(b, size, lcap), deg, q, w)

# Delete the entry at index q.
def blk_del(b: Array<U32>, +deg: U32, +q: U32) -> Array<U32>:
  Array.set(U32, shl_go(U32.to_nat(U32.sub(ent_last(deg), q)), q, b), 0, U32.sub(deg, 1))

# ---- adjacency updates at a slot ----

def upd_put(adj: Array<Array<U32>>, +i: U32, b: Array<U32>) -> Array<Array<U32>>:
  Array.set(Array<U32>, adj, i, b)

def add_in5(b: Array<U32>, +deg: U32, +size: U32, +lcap: U32, +q: U32, +w: U32, found: Bool) -> Array<U32>:
  match found:
    case True{}:
      b
    case False{}:
      blk_add(b, deg, size, lcap, q, w, U32.is_lt(ent_end(deg), size))

def add_in4(adj: Array<Array<U32>>, +i: U32, +deg: U32, +size: U32, +lcap: U32, +w: U32, s: Loc) -> Array<Array<U32>>:
  LC{b, +q, found} = s
  upd_put(adj, i, add_in5(b, deg, size, lcap, q, w, found))

def add_in3(adj: Array<Array<U32>>, +i: U32, +w: U32, h: Hdr) -> Array<Array<U32>>:
  HD{b, +deg, +size, +lcap} = h
  add_in4(adj, i, deg, size, lcap, w, blk_find(b, deg, lcap, w))

def add_in2(+i: U32, +w: U32, r: Array<Array<U32>> & Array<U32>) -> Array<Array<U32>>:
  (adj, b) = r
  add_in3(adj, i, w, header(b))

# Idempotently add w to the adjacency block of slot i.
def add_nbr(adj: Array<Array<U32>>, +i: U32, +w: U32) -> Array<Array<U32>>:
  add_in2(i, w, Array.swap(Array<U32>, adj, i, zeros(0n)))

type Upd is Type:
  UP{adj: Array<Array<U32>>, ok: Bool}

def del_in5(adj: Array<Array<U32>>, +i: U32, b: Array<U32>, +deg: U32, +q: U32, found: Bool) -> Upd:
  match found:
    case True{}:
      UP{upd_put(adj, i, blk_del(b, deg, q)), True{}}
    case False{}:
      UP{upd_put(adj, i, b), False{}}

def del_in4(adj: Array<Array<U32>>, +i: U32, +deg: U32, s: Loc) -> Upd:
  LC{b, +q, found} = s
  del_in5(adj, i, b, deg, q, found)

def del_in3(adj: Array<Array<U32>>, +i: U32, +w: U32, h: Hdr) -> Upd:
  HD{b, +deg, size, +lcap} = h
  del_in4(adj, i, deg, blk_find(b, deg, lcap, w))

def del_in2(+i: U32, +w: U32, r: Array<Array<U32>> & Array<U32>) -> Upd:
  (adj, b) = r
  del_in3(adj, i, w, header(b))

# Remove w from the adjacency block of slot i; `ok` says whether it was there.
def del_nbr(adj: Array<Array<U32>>, +i: U32, +w: U32) -> Upd:
  del_in2(i, w, Array.swap(Array<U32>, adj, i, zeros(0n)))

def del_nbr_fin(u: Upd) -> Array<Array<U32>>:
  UP{adj, ok} = u
  adj

# Test membership of w in the block of slot i, leaving the block in place.
def mem_loc(adj: Array<Array<U32>>, +i: U32, s: Loc) -> Upd:
  LC{b, q, found} = s
  UP{upd_put(adj, i, b), found}

def mem_hdr(adj: Array<Array<U32>>, +i: U32, +w: U32, h: Hdr) -> Upd:
  HD{b, +deg, size, +lcap} = h
  mem_loc(adj, i, blk_find(b, deg, lcap, w))

def mem_read(+i: U32, +w: U32, r: Array<Array<U32>> & Array<U32>) -> Upd:
  (adj, b) = r
  mem_hdr(adj, i, w, header(b))

def mem_nbr(adj: Array<Array<U32>>, +i: U32, +w: U32) -> Upd:
  mem_read(i, w, Array.swap(Array<U32>, adj, i, zeros(0n)))

# ---- has_vertex ----

def hv_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, s: Loc) -> Graph & Bool:
  LC{ids, i, found} = s
  (G{dir, lo, hi, cap, depth, ids, adj}, found)

def has_vertex(g: Graph, +v: U32) -> Graph & Bool:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  hv_fin(dir, lo, hi, cap, depth, adj, locate(depth, v, lo, hi, ids))

# ---- add_vertex ----

# Insert v at index i of the window [lo, hi).
#
# The window floats inside the block, so an insertion moves only the SHORTER
# side: at either end it moves nothing at all. When the chosen side has no
# room the block is doubled on that side (the old block becomes the upper
# half when the front is the one that needs room, which keeps front
# insertion O(1) amortised, as in a deque).

# Move [lo, i) down one slot and write at i - 1.
def av_left(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  (G{dir, U32.sub(lo, 1), hi, cap, depth,
     Array.set(U32, shl_go(U32.to_nat(U32.sub(i, lo)), U32.sub(lo, 1), ids), U32.sub(i, 1), v),
     Array.set(Array<U32>, shla_go(U32.to_nat(U32.sub(i, lo)), U32.sub(lo, 1), adj), U32.sub(i, 1), empty_blk())},
   Done{Unit{}})

# Move [i, hi) up one slot and write at i.
def av_right(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  (G{dir, lo, U32.inc(hi), cap, depth,
     Array.set(U32, shr_go(U32.to_nat(U32.sub(hi, i)), hi, ids), i, v),
     Array.set(Array<U32>, shra_go(U32.to_nat(U32.sub(hi, i)), hi, adj), i, empty_blk())},
   Done{Unit{}})

# x + cap, written without addition: cap - (cap - x), valid for x <= cap.
def up(+cap: U32, +x: U32) -> U32:
  U32.sub(U32.shl(cap), U32.sub(cap, x))

# Double with the old block as the UPPER half: every stored index moves up by
# the old capacity, and the whole old capacity becomes free room at the front.
def av_grow_left(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  av_left(dir, up(cap, lo), up(cap, hi), U32.shl(cap), 1n+depth,
          ANode{zeros(depth), ids}, ANode{spare_blks(depth), adj}, up(cap, i), v)

# Double with the old block as the lower half: free room at the back.
def av_grow_right(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  av_right(dir, lo, hi, U32.shl(cap), 1n+depth,
           ANode{ids, zeros(depth)}, ANode{adj, spare_blks(depth)}, i, v)

# left: the head is the shorter side; lroom/rroom: that side has a free slot.
def av_side(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32, left: Bool, lroom: Bool, rroom: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match left lroom rroom:
    case True{} True{} _:
      av_left(dir, lo, hi, cap, depth, ids, adj, i, v)
    case True{} False{} True{}:
      av_right(dir, lo, hi, cap, depth, ids, adj, i, v)
    case True{} False{} False{}:
      av_grow_left(dir, lo, hi, cap, depth, ids, adj, i, v)
    case False{} _ True{}:
      av_right(dir, lo, hi, cap, depth, ids, adj, i, v)
    case False{} True{} False{}:
      av_left(dir, lo, hi, cap, depth, ids, adj, i, v)
    case False{} False{} False{}:
      av_grow_right(dir, lo, hi, cap, depth, ids, adj, i, v)

def av_ins(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  av_side(dir, lo, hi, cap, depth, ids, adj, i, v,
          U32.is_lt(U32.sub(i, lo), U32.sub(hi, i)),
          U32.is_lt(0, lo),
          U32.is_lt(hi, cap))

def av_pick(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32, found: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match found:
    case True{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexExists{}})
    case False{}:
      av_ins(dir, lo, hi, cap, depth, ids, adj, i, v)

def av_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +i, found} = s
  av_pick(dir, lo, hi, cap, depth, ids, adj, i, v, found)

def add_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  av_fin(dir, lo, hi, cap, depth, adj, v, locate(depth, v, lo, hi, ids))

# ---- remove_vertex ----
#
# v is removed from every slot's block, in both directions, as the C
# reference's `strip` removes it from every vertex's set; v's own block is
# visited too (a no-op: no vertex is its own neighbour) and is then dropped
# when its slot is closed.

type Pair2 is Type:
  P2{ids: Array<U32>, adj: Array<Array<U32>>}

def sd_loop(k: Nat, +v: U32, +idx: U32, adj: Array<Array<U32>>) -> Array<Array<U32>>:
  match k:
    case 0n:
      adj
    case 1n+m:
      sd_loop(m, v, U32.inc(idx), del_nbr_fin(del_nbr(adj, idx, v)))

# ---- traversals that build the public lists ----

def nb_go(k: Nat, acc: List<&2, U32>, +j: U32, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match k r:
    case 0n Tuple{b, x}:
      (b, acc)
    case 1n+m Tuple{b, +x}:
      nb_go(m, Con{x, acc}, U32.sub(j, 1), Array.get(U32, b, U32.sub(j, 1)))

def keep_if(b: Bool, x: E.Edge, rest: List<&2, E.Edge>) -> List<&2, E.Edge>:
  match b:
    case True{}:
      Con{x, rest}
    case False{}:
      rest

# Strip v from every block of the window [lo, hi); the caller then closes the gap.
def strip_all(+lo: U32, +hi: U32, +v: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> Pair2:
  P2{ids, sd_loop(U32.to_nat(U32.sub(hi, lo)), v, lo, adj)}

# Close the gap by moving the TAIL down one slot (the back is the shorter side).
def rv_tail(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> Graph:
  G{dir, lo, U32.sub(hi, 1), cap, depth,
    shl_go(U32.to_nat(U32.sub(U32.sub(hi, 1), i)), i, ids),
    shla_go(U32.to_nat(U32.sub(U32.sub(hi, 1), i)), i, adj)}

# Close the gap by moving the HEAD up one slot; the window starts one later.
def rv_head(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>) -> Graph:
  G{dir, U32.inc(lo), hi, cap, depth,
    shr_go(U32.to_nat(U32.sub(i, lo)), i, ids),
    shra_go(U32.to_nat(U32.sub(i, lo)), i, adj)}

def rv_side(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, +i: U32, ids: Array<U32>, adj: Array<Array<U32>>, head: Bool) -> Graph:
  match head:
    case True{}:
      rv_head(dir, lo, hi, cap, depth, i, ids, adj)
    case False{}:
      rv_tail(dir, lo, hi, cap, depth, i, ids, adj)

def rv_drop(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, +i: U32, p: Pair2) -> Graph:
  P2{ids, adj} = p
  rv_side(dir, lo, hi, cap, depth, i, ids, adj,
          U32.is_lt(U32.sub(i, lo), U32.sub(U32.sub(hi, 1), i)))

def rv_go(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> Graph:
  rv_drop(dir, lo, hi, cap, depth, i, strip_all(lo, hi, v, ids, adj))

def rv_pick(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32, found: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match found:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      (rv_go(dir, lo, hi, cap, depth, ids, adj, i, v), Done{Unit{}})

def rv_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +i, found} = s
  rv_pick(dir, lo, hi, cap, depth, ids, adj, i, v, found)

def remove_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  rv_fin(dir, lo, hi, cap, depth, adj, v, locate(depth, v, lo, hi, ids))

# ---- add_edge ----

def ae_apply(+dir: Bool, adj: Array<Array<U32>>, +iu: U32, +iv: U32, +u: U32, +v: U32) -> Array<Array<U32>>:
  match dir:
    case True{}:
      add_nbr(adj, iu, v)
    case False{}:
      add_nbr(add_nbr(adj, iu, v), iv, u)

def ae_loop(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +iv: U32, +u: U32, +v: U32, same: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match same:
    case True{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.SelfLoop{}})
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, ae_apply(dir, adj, iu, iv, u, v)}, Done{Unit{}})

def ae_vf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +iv: U32, +u: U32, +v: U32, fv: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match fv:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      ae_loop(dir, lo, hi, cap, depth, ids, adj, iu, iv, u, v, U32.is_eq(u, v))

def ae_v(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +iu: U32, +u: U32, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +iv, fv} = s
  ae_vf(dir, lo, hi, cap, depth, ids, adj, iu, iv, u, v, fv)

def ae_uf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +u: U32, +v: U32, fu: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match fu:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      ae_v(dir, lo, hi, cap, depth, adj, iu, u, v, locate(depth, v, lo, hi, ids))

def ae_u(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +u: U32, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +iu, fu} = s
  ae_uf(dir, lo, hi, cap, depth, ids, adj, iu, u, v, fu)

def add_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  ae_u(dir, lo, hi, cap, depth, adj, u, v, locate(depth, u, lo, hi, ids))

# ---- remove_edge ----

def re_other(+dir: Bool, adj: Array<Array<U32>>, +iv: U32, +u: U32) -> Array<Array<U32>>:
  match dir:
    case True{}:
      adj
    case False{}:
      del_nbr_fin(del_nbr(adj, iv, u))

def re_ok(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iv: U32, +u: U32, ok: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match ok:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.EdgeNotFound{}})
    case True{}:
      (G{dir, lo, hi, cap, depth, ids, re_other(dir, adj, iv, u)}, Done{Unit{}})

def re_go(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, +iv: U32, +u: U32, up: Upd) -> Graph & Result<&2, &2, E.Error, Unit>:
  UP{adj, ok} = up
  re_ok(dir, lo, hi, cap, depth, ids, adj, iv, u, ok)

def re_loop(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +iv: U32, +u: U32, +v: U32, same: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match same:
    case True{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.EdgeNotFound{}})
    case False{}:
      re_go(dir, lo, hi, cap, depth, ids, iv, u, del_nbr(adj, iu, v))

def re_vf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +iv: U32, +u: U32, +v: U32, fv: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match fv:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      re_loop(dir, lo, hi, cap, depth, ids, adj, iu, iv, u, v, U32.is_eq(u, v))

def re_v(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +iu: U32, +u: U32, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +iv, fv} = s
  re_vf(dir, lo, hi, cap, depth, ids, adj, iu, iv, u, v, fv)

def re_uf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +u: U32, +v: U32, fu: Bool) -> Graph & Result<&2, &2, E.Error, Unit>:
  match fu:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      re_v(dir, lo, hi, cap, depth, adj, iu, u, v, locate(depth, v, lo, hi, ids))

def re_u(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +u: U32, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Unit>:
  LC{ids, +iu, fu} = s
  re_uf(dir, lo, hi, cap, depth, ids, adj, iu, u, v, fu)

def remove_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  re_u(dir, lo, hi, cap, depth, adj, u, v, locate(depth, u, lo, hi, ids))

# ---- has_edge ----

def he_test(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, up: Upd) -> Graph & Result<&2, &2, E.Error, Bool>:
  UP{adj, ok} = up
  (G{dir, lo, hi, cap, depth, ids, adj}, Done{ok})

def he_vf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +v: U32, fv: Bool) -> Graph & Result<&2, &2, E.Error, Bool>:
  match fv:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      he_test(dir, lo, hi, cap, depth, ids, mem_nbr(adj, iu, v))

def he_v(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +iu: U32, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Bool>:
  LC{ids, +iv, fv} = s
  he_vf(dir, lo, hi, cap, depth, ids, adj, iu, v, fv)

def he_uf(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +iu: U32, +v: U32, fu: Bool) -> Graph & Result<&2, &2, E.Error, Bool>:
  match fu:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      he_v(dir, lo, hi, cap, depth, adj, iu, v, locate(depth, v, lo, hi, ids))

def he_u(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +v: U32, s: Loc) -> Graph & Result<&2, &2, E.Error, Bool>:
  LC{ids, +iu, fu} = s
  he_uf(dir, lo, hi, cap, depth, ids, adj, iu, v, fu)

def has_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Bool>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  he_u(dir, lo, hi, cap, depth, adj, v, locate(depth, u, lo, hi, ids))

# ---- neighbors ----

type Nbr is Type:
  NBR{adj: Array<Array<U32>>, xs: List<&2, U32>}

def nb_fin(adj: Array<Array<U32>>, +i: U32, r: Array<U32> & List<&2, U32>) -> Nbr:
  (b, xs) = r
  NBR{upd_put(adj, i, b), xs}

# Entries live at [3, 3+deg); reading them from the last one backwards conses
# them into ascending order. With deg = 0 the header word read is discarded.
def nb_start(b: Array<U32>, +deg: U32) -> Array<U32> & List<&2, U32>:
  nb_go(U32.to_nat(deg), Nil{}, ent_last(deg), Array.get(U32, b, ent_last(deg)))

def nb_hdr(adj: Array<Array<U32>>, +i: U32, h: Hdr) -> Nbr:
  HD{b, +deg, size, lcap} = h
  nb_fin(adj, i, nb_start(b, deg))

def nb_take(+i: U32, r: Array<Array<U32>> & Array<U32>) -> Nbr:
  (adj, b) = r
  nb_hdr(adj, i, header(b))

def nbrs(adj: Array<Array<U32>>, +i: U32) -> Nbr:
  nb_take(i, Array.swap(Array<U32>, adj, i, zeros(0n)))

def nbr_done(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, s: Nbr) -> Graph & Result<&2, &2, E.Error, List<&2, U32>>:
  NBR{adj, xs} = s
  (G{dir, lo, hi, cap, depth, ids, adj}, Done{xs})

def nbr_pick(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, found: Bool) -> Graph & Result<&2, &2, E.Error, List<&2, U32>>:
  match found:
    case False{}:
      (G{dir, lo, hi, cap, depth, ids, adj}, Fail{E.VertexNotFound{}})
    case True{}:
      nbr_done(dir, lo, hi, cap, depth, ids, nbrs(adj, i))

def nbr_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, s: Loc) -> Graph & Result<&2, &2, E.Error, List<&2, U32>>:
  LC{ids, +i, found} = s
  nbr_pick(dir, lo, hi, cap, depth, ids, adj, i, found)

# Out-neighbours of v (all neighbours when undirected), ascending.
def neighbors(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, List<&2, U32>>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  nbr_fin(dir, lo, hi, cap, depth, adj, locate(depth, v, lo, hi, ids))

# ---- vertices ----

def vs_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, r: Array<U32> & List<&2, U32>) -> Graph & List<&2, U32>:
  (ids, xs) = r
  (G{dir, lo, hi, cap, depth, ids, adj}, xs)

def vs_start(ids: Array<U32>, +lo: U32, +hi: U32) -> Array<U32> & List<&2, U32>:
  nb_go(U32.to_nat(U32.sub(hi, lo)), Nil{}, U32.sub(hi, 1), Array.get(U32, ids, U32.sub(hi, 1)))

# The vertex ids, ascending.
def vertices(g: Graph) -> Graph & List<&2, U32>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  vs_fin(dir, lo, hi, cap, depth, adj, vs_start(ids, lo, hi))

# ---- vertices as a BLOCK (the indexed enumeration view) ----
#
# `vertices` above materialises a `List`, which costs one cons cell per
# vertex. The vertex ids are ALREADY an ascending run of a native block, so
# the enumeration does not need a cons spine at all: `vertices_block` copies
# the window `ids[lo, hi)` into a fresh `Array<U32>` of `n = hi - lo` used
# slots and hands it back with its length. The caller reads it by index.
#
# Both APIs are public, both are proved, and they denote the SAME ascending
# sequence of vertex ids (proofs/graph/vblk.bend). The block form is what the
# benchmark driver folds, because benchmarks/native/graph.c's `gr_vs` folds
# the vertex keys in order without building a list either.

type VBlk is Type:
  VB{g: Graph, blk: Array<U32>, n: U32}

# Copies backwards: with k values left to place, the value just read at ids[j]
# belongs in slot k-1 of the new block (j = lo + k - 1), so the destination is
# the remaining count and no index arithmetic on `lo` is needed in the loop.
def vb_go(k: Nat, blk: Array<U32>, +j: U32, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match k r:
    case 0n Tuple{a, x}:
      (a, blk)
    case 1n+ +m Tuple{a, +x}:
      vb_go(m, Array.set(U32, blk, U32.from_nat(m), x), U32.sub(j, 1), Array.get(U32, a, U32.sub(j, 1)))

def vb_fin(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, adj: Array<Array<U32>>, +n: U32, r: Array<U32> & Array<U32>) -> VBlk:
  (ids, blk) = r
  VB{G{dir, lo, hi, cap, depth, ids, adj}, blk, n}

# The vertex ids, ascending, in slots [0, n) of a fresh block.
def vertices_block(g: Graph) -> VBlk:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  vb_fin(dir, lo, hi, cap, depth, adj, U32.sub(hi, lo), vb_go(U32.to_nat(U32.sub(hi, lo)), zeros(depth), U32.sub(hi, 1), Array.get(U32, ids, U32.sub(hi, 1))))

# ---- edges ----

type Ed is Type:
  ED{ids: Array<U32>, adj: Array<Array<U32>>, acc: List<&2, E.Edge>, i: U32}

def ed_inner(k: Nat, +dir: Bool, +u: U32, acc: List<&2, E.Edge>, +j: U32, r: Array<U32> & U32) -> Array<U32> & List<&2, E.Edge>:
  match k r:
    case 0n Tuple{b, x}:
      (b, acc)
    case 1n+m Tuple{b, +w}:
      ed_inner(m, dir, u, keep_if(Bool.or(dir, U32.is_lt(u, w)), E.Edge{u, w}, acc), U32.sub(j, 1), Array.get(U32, b, U32.sub(j, 1)))

def ed_fin(ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, r: Array<U32> & List<&2, E.Edge>) -> Ed:
  (b, acc) = r
  ED{ids, upd_put(adj, i, b), acc, U32.sub(i, 1)}

def ed_hdr(+dir: Bool, ids: Array<U32>, adj: Array<Array<U32>>, acc: List<&2, E.Edge>, +i: U32, +u: U32, h: Hdr) -> Ed:
  HD{b, +deg, size, lcap} = h
  ed_fin(ids, adj, i, ed_inner(U32.to_nat(deg), dir, u, acc, ent_last(deg), Array.get(U32, b, ent_last(deg))))

def ed_blk(+dir: Bool, ids: Array<U32>, acc: List<&2, E.Edge>, +i: U32, +u: U32, r: Array<Array<U32>> & Array<U32>) -> Ed:
  (adj, b) = r
  ed_hdr(dir, ids, adj, acc, i, u, header(b))

def ed_read(+dir: Bool, adj: Array<Array<U32>>, acc: List<&2, E.Edge>, +i: U32, r: Array<U32> & U32) -> Ed:
  (ids, +u) = r
  ed_blk(dir, ids, acc, i, u, Array.swap(Array<U32>, adj, i, zeros(0n)))

def ed_step(+dir: Bool, s: Ed) -> Ed:
  ED{ids, adj, acc, +i} = s
  ed_read(dir, adj, acc, i, Array.get(U32, ids, i))

def ed_loop(k: Nat, +dir: Bool, s: Ed) -> Ed:
  match k:
    case 0n:
      s
    case 1n+m:
      ed_loop(m, dir, ed_step(dir, s))

def ed_done(+dir: Bool, +lo: U32, +hi: U32, +cap: U32, +depth: Nat, s: Ed) -> Graph & List<&2, E.Edge>:
  ED{ids, adj, acc, i} = s
  (G{dir, lo, hi, cap, depth, ids, adj}, acc)

# Edges in lexicographic (src, dst) order; an undirected edge appears once,
# as (smaller, larger).
def edges(g: Graph) -> Graph & List<&2, E.Edge>:
  G{+dir, +lo, +hi, +cap, +depth, ids, adj} = g
  ed_done(dir, lo, hi, cap, depth, ed_loop(U32.to_nat(U32.sub(hi, lo)), dir, ED{ids, adj, Nil{}, U32.sub(hi, 1)}))

# ---- trace runner ----

def obs_unit(r: Graph & Result<&2, &2, E.Error, Unit>) -> Graph & E.Obs:
  (g, x) = r
  (g, E.OUnit{x})

def obs_bool(r: Graph & Bool) -> Graph & E.Obs:
  (g, b) = r
  (g, E.OBool{b})

def obs_flag(r: Graph & Result<&2, &2, E.Error, Bool>) -> Graph & E.Obs:
  (g, x) = r
  (g, E.OFlag{x})

def obs_nbrs(r: Graph & Result<&2, &2, E.Error, List<&2, U32>>) -> Graph & E.Obs:
  (g, x) = r
  (g, E.ONeighbors{x})

def obs_vs(r: Graph & List<&2, U32>) -> Graph & E.Obs:
  (g, xs) = r
  (g, E.OVertices{xs})

def obs_es(r: Graph & List<&2, E.Edge>) -> Graph & E.Obs:
  (g, es) = r
  (g, E.OEdges{es})

def step(g: Graph, op: E.Op) -> Graph & E.Obs:
  match op:
    case E.AddVertex{v}:
      obs_unit(add_vertex(g, v))
    case E.RemoveVertex{v}:
      obs_unit(remove_vertex(g, v))
    case E.AddEdge{u, v}:
      obs_unit(add_edge(g, u, v))
    case E.RemoveEdge{u, v}:
      obs_unit(remove_edge(g, u, v))
    case E.HasVertex{v}:
      obs_bool(has_vertex(g, v))
    case E.HasEdge{u, v}:
      obs_flag(has_edge(g, u, v))
    case E.Neighbors{v}:
      obs_nbrs(neighbors(g, v))
    case E.Vertices{}:
      obs_vs(vertices(g))
    case E.Edges{}:
      obs_es(edges(g))

def record(acc: List<&2, E.Obs>, r: Graph & E.Obs) -> Graph & List<&2, E.Obs>:
  (g, o) = r
  (g, Con{o, acc})

def step_acc(op: E.Op, st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  (g, acc) = st
  record(acc, step(g, op))

def run_acc(ops: List<&2, E.Op>, st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(rest, step_acc(op, st))

def finish(st: Graph & List<&2, E.Obs>) -> Graph & List<&2, E.Obs>:
  (g, acc) = st
  (g, List.reverse(&2, E.Obs, acc))

def run(ops: List<&2, E.Op>, g: Graph) -> Graph & List<&2, E.Obs>:
  finish(run_acc(ops, (g, Nil{})))
