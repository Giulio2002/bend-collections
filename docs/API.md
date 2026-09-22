# API index

One public module per structure, `src/<id>.bend`. Every operation below is the
one named in `inventory/structures.json`; the exact error semantics and the
cost of each operation are documented in the header comment of the source file
(and repeated by the specification in `spec/<id>.bend`).

Some structures are **persistent**: an update returns a new value and shares
everything it did not have to rebuild. The array-backed ones (`dynamic_array`,
`deque`, `queue`, `bitset`, `fenwick_tree`, `segment_tree`) are
built on native `Base.Array`, which is **linear**: they are threaded (every
operation takes the structure and gives it back) and released explicitly
where a caller needs it. Failures never change the state -- an operation that
reports an error returns the input structure unchanged.

A generic array-backed structure also exposes executable `*_at` entry points
(`new_at`, `push_back_at`, `run_at`, ...) that take the element type as a
compile-time `~T` parameter. They exist because Bend 2.0.16's native backend
miscompiles `Base.Array` at an open element type (`docs/VALIDATION.md`); they
are the entry points the tests and benchmarks use, and
`proofs/<id>/closed.bend` proves each equal to the parametric definition the
laws are about.

## `dynamic_array`

Growable, bounds-checked array over native Base.Array. Representation:
DA{limit, depth, cap, length, slots} with cap = 2^depth kept in the record
(recomputing 2^depth per operation would make every push, capacity and
reserve cost O(depth)). `slots` is a Base.Array of 2^depth slots, which the
native backend lowers to one indexed memory block (the ALeaf/ANode tree is
the logical model, not the runtime layout -- see docs/C_EQUIVALENCE.md); slots
[0, length) hold Some{x}, the rest hold None. `limit` (<= 31) caps depth, so
every index passed to Base is < 2^31 and Base's masking is the identity.
Errors return the state unchanged: get/set out of range -> IndexOutOfRange;
pop on empty -> EmptyArray; push/reserve beyond 2^limit -> CapacityExceeded.
Cost (n = length, c = capacity): get/set/push/pop O(1) indexed access,
growth O(c) (a new half is allocated), reserve O(target capacity), clear O(c),
to_list O(c).

```
new(-T: Data) -> DynArray<T>
length(-T: Data, da: DynArray<T>) -> DynArray<T> & Nat
capacity(-T: Data, da: DynArray<T>) -> DynArray<T> & Nat
get(-T: Data, da: DynArray<T>, +i: Nat) -> DynArray<T> & Result<&2, &2, E.Error, T>
set(-T: Data, da: DynArray<T>, +i: Nat, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>
push(-T: Data, da: DynArray<T>, v: T) -> DynArray<T> & Result<&2, &2, E.Error, Unit>
pop(-T: Data, da: DynArray<T>) -> DynArray<T> & Result<&2, &2, E.Error, T>
reserve(-T: Data, da: DynArray<T>, +n: Nat) -> DynArray<T> & Result<&2, &2, E.Error, Unit>
clear(-T: Data, da: DynArray<T>) -> DynArray<T>
to_list(-T: Data, da: DynArray<T>) -> DynArray<T> & List<&2, T>
```

## `deque`

Double-ended queue over a native Base.Array: a window of occupied slots
inside a power-of-two block. Representation: DQ{depth, cap, lo, len, slots}
with cap = 2^depth; the elements are slots [lo, lo + len), front first, so
element j is slot lo + j and every end operation is one indexed read or
write. When a push has no free slot at its end the block is doubled, which is
one Base.Array node and one fresh empty half: a back push keeps every index
(the old block becomes the lower half) and a front push moves every index up
by the old capacity (the old block becomes the upper half), so no element is
ever copied and no index arithmetic is modular. Doubling gives 2^depth free
slots at that end, so a push is amortized O(1); pops, peeks and length are
O(1) and to_list is O(len). Capacity: depth < 31, which is the premise the
laws about pushes carry (see proofs/deque.bend). Errors: pop/peek on an empty
deque return Fail{EmptyDeque} and the deque unchanged.

```
new(-T: Data) -> Deque<T>
length(-T: Data, d: Deque<T>) -> Deque<T> & Nat
push_front(-T: Data, d: Deque<T>, x: T) -> Deque<T>
push_back(-T: Data, d: Deque<T>, x: T) -> Deque<T>
pop_front(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>
pop_back(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>
peek_front(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>
peek_back(-T: Data, d: Deque<T>) -> Deque<T> & Result<&2, &2, E.Error, T>
to_list(-T: Data, d: Deque<T>) -> Deque<T> & List<&2, T>
```

## `queue`

FIFO queue: the back-in/front-out specialization of src/deque.bend
(enqueue = push_back, dequeue = pop_front, peek = peek_front). It reuses the
deque representation and costs; see above. dequeue/peek on an empty queue
return Fail{EmptyQueue} and the queue unchanged.

```
new(-T: Data) -> Queue<T>
length(-T: Data, q: Queue<T>) -> Queue<T> & Nat
enqueue(-T: Data, q: Queue<T>, x: T) -> Queue<T>
dequeue(-T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>
peek(-T: Data, q: Queue<T>) -> Queue<T> & Result<&2, &2, E.Error, T>
to_list(-T: Data, q: Queue<T>) -> Queue<T> & List<&2, T>
```

## `doubly_linked_list`

Doubly linked list with stable opaque handles, values of an erased type T.

Representation: PARALLEL INDEXED ARENAS. Three `Base.Array` blocks of
2^depth slots share one index space -- `vals` (`Maybe<T>`: `None` for a slot
that was never used or whose element was removed), `prevs` and `nexts`
(`U32` arena indices, `2^32 - 1` meaning "no neighbour"). The element id IS
its slot index; ids come from a monotone counter and are never reused, so a
handle to a removed element is detected as stale (its `vals` slot is `None`)
and a handle whose tag differs from the list's is rejected as foreign. (Tags
are chosen by the caller of `new`; lists that must reject each other's
handles need distinct tags.) The blocks double when the counter reaches the
capacity, so every id keeps its slot. Keeping prev and next in their own
blocks makes relinking a neighbour ONE indexed write instead of a
read-modify-write of a node record.

Every failure returns the state unchanged; every operation, including the
read-only ones, takes the list by value and returns it (the state is
linear).

Cost (n = elements ever inserted): every handle operation, push and length
is O(1) indexed reads and writes; `to_list` reads O(count) slots; a push
that finds the blocks full doubles them, amortised O(1). Because ids are
never reused the blocks grow with n, not with the live count -- the same
trade the reference C implementation makes with its bump arena.

```
new(~T: Data, tag: U32) -> DList<T>
length(~T: Data, s: DList<T>) -> DList<T> & Nat
push_front(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle
push_back(~T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle
insert_before(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>
insert_after(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>
remove(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>
get(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>
set(~T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>
next(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>
prev(~T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, Maybe<&2, E.Handle>>
to_list(~T: Data, s: DList<T>) -> DList<T> & List<&2, T>
```

Handles are `E.H{list: U32, id: U32}` and element ids are `U32` (they were
`Nat` while the node store was an ordered map keyed by `Nat`).

## `binary_heap`

Min-heap PACKED IN AN ARRAY: the elements occupy the slots [0, size) of one `Base.Array` block of 2^depth slots, element i having children 2i+1 and 2i+2 and parent (i-1)/2, so the shape of the heap is its index arithmetic and no node or link is allocated per element. push writes at slot `size` and sifts up (early exit at the first parent that is not larger, which is what makes a random push O(1) expected); pop takes slot 0, lifts the last element into the hole and sifts it down through the smaller child; the block doubles when a push finds it full (the old block becomes the lower half, so every element keeps its index). The order is a static comparator ~cmp : A -> A -> Cmp (a template parameter); its total-order laws are proof obligations of each instance (proofs/lib/order.bend: U32 and String). Elements equal under cmp are identical under the laws, so multiplicities are exact.  Cost: push O(log n) worst case and O(1) expected, pop O(log n); peek, length O(1); from_list O(n log n); to_sorted_list O(n log n) plus one O(n) block clone (the heap itself is returned unchanged). Capacity: the block doubles, depth is bounded by 31, so every slot index is a representable U32. Errors: peek/pop on an empty heap -> Fail{EmptyHeap}, heap unchanged.

```
new(~A: Data) -> Heap<A>
length(~A: Data, h: Heap<A>) -> Heap<A> & Nat
push(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>, x: A) -> Heap<A>
peek(~A: Data, h: Heap<A>) -> Heap<A> & Result<&2, &2, E.Error, A>
pop(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>) -> Heap<A> & Result<&2, &2, E.Error, A>
from_list(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Heap<A>
to_sorted_list(~A: Data, ~cmp: A -> A -> Cmp, h: Heap<A>) -> Heap<A> & List<&2, A>
```

## `balanced_search_tree`

Ordered map with a comparator ~cmp (a total order, see proofs/lib/order), implemented as a RED-BLACK BINARY search tree: every node has exactly two children and a colour, the root and the empty leaves are black, no red node has a red child, and every root-to-leaf path contains the same number of black nodes. The height is therefore at most 2*log2(n + 1).  Insertion is Okasaki's: the new node is red, and `balance` repairs the one red-red edge a recursive insertion can create by rotating/recolouring the four classic cases; the root is blackened afterwards. Deletion is the conventional CLRS fixup in functional form: `del` returns TD (the black height is unchanged) or UF (the subtree lost one black level), and fix_left / fix_right repair a UF child by borrowing from or recolouring the sibling (red sibling -> rotate; black sibling with a red child -> rotate and recolour; black sibling with two black children -> recolour the sibling red and propagate). A deleted internal node is replaced by the minimum of its right subtree (split_min).  The comparison of the searched key with a node's key is computed by the caller and passed down (`a`), so every recursive call is on a subtree.  Errors never change the state: remove/lookup of a missing key give KeyNotFound; min/max of an empty map give EmptyTree; lower_bound with no key >= k gives KeyNotFound.  Cost (n entries, comparisons): insert/remove/lookup/contains/lower_bound/ min/max O(log n); range O(log n + m) for m results; to_list O(n); length O(1). The tree is persistent: an update rebuilds the O(log n) nodes on the path and shares everything else.  Checked instances: keys U32 (U32.cmp) and String (String.order); values are an erased type parameter.

```
new(-K: Data, -V: Data) -> OrdMap<K, V>
length(-K: Data, -V: Data, s: OrdMap<K, V>) -> Nat
insert(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K, +v: V) -> OrdMap<K, V>
remove(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> OrdMap<K, V> & Result<&2, &2, E.Error, V>
lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Result<&2, &2, E.Error, V>
contains(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Bool
min(-K: Data, -V: Data, s: OrdMap<K, V>) -> Result<&2, &2, E.Error, E.Entry<K, V>>
max(-K: Data, -V: Data, s: OrdMap<K, V>) -> Result<&2, &2, E.Error, E.Entry<K, V>>
lower_bound(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Result<&2, &2, E.Error, E.Entry<K, V>>
range(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +lo: K, +hi: K) -> List<&2, E.Entry<K, V>>
to_list(-K: Data, -V: Data, s: OrdMap<K, V>) -> List<&2, E.Entry<K, V>>
```

## `bitset`

Packed fixed-size bitset over native `Base.Array`.  A bitset of logical size
`len` stores its bits LSB-first in an array of 2^depth 32-bit words: bit i
lives in word i/32 at bit position i%32. The array holds at least
ceil(len/32) words and every bit at a position >= len (the unused tail of the
last used word, and any whole padding word) is zero. Both facts are the
invariant proven in `proofs/bitset.bend`; union/intersection/difference/xor
rely on it (difference is a AND NOT b, which stays masked because a's tail is
zero).

`Base.Array` is a **linear** fixed-capacity array with O(1) indexed read and
write, so - exactly like `dynamic_array` - every operation takes the bitset
and gives it back, and a bitset that is no longer needed is released with
`dispose`.  `clone` makes two independent bitsets with the same contents (the
linear form of sharing).

**Capacity.** `depth` is capped at 31, i.e. 2^31 words = 2^36 bits, so every
word index is a representable U32. The laws about `new(n)` carry the explicit
premise that n fits that capacity (`proofs/bitset.bend` `capacity`); every
other law holds at every state satisfying the invariant, and the invariant
implies the premise. This is the same kind of documented capacity bound that
`dynamic_array` carries, and the same one `benchmarks/native/bitset.c` has.

Errors never change the state: get/set/clear with index >= len fail with
IndexOutOfRange; binary operations on operands of different logical size fail
with LengthMismatch and return both operands unchanged.

Cost (w = 2^depth words): new O(w); length O(1); get/set/clear O(1) indexed
word access plus O(1) word arithmetic; count/to_list O(32 * w); binary
operations O(w); clone O(w); dispose O(w).

```
new(+n: Nat) -> Bitset
length(s: Bitset) -> Bitset & Nat
get(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Bool>
set(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Unit>
clear(s: Bitset, +i: Nat) -> Bitset & Result<&2, &2, E.Error, Unit>
count(s: Bitset) -> Bitset & Nat
union(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>
intersection(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>
difference(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>
xor(s: Bitset, t: Bitset) -> Bitset & Bitset & Result<&2, &2, E.Error, Unit>
to_list(s: Bitset) -> Bitset & List<&2, Nat>
from_bools(+bs: List<&2, Bool>) -> Bitset
clone(s: Bitset) -> Bitset & Bitset
dispose(s: Bitset) -> Unit
```

The trace runner's binary operations take the operand as a bit sequence and
compare the logical sizes *before* building the operand bitset
(`comb_bits`), so a mismatched operand costs nothing.

## `fenwick_tree`

Fenwick (binary indexed) tree over n U32 values; all sums wrap modulo 2^32 (U32.add / U32.sub).  Representation: the Fenwick partial sums kept in an explicit perfect tree of depth d (2^d >= n): every internal node stores the sum of its left subtree, exactly the quantity an array-based Fenwick tree stores at the node where a left block ends. Point addition updates the left-sums on the root-to-leaf path; a prefix sum adds the left-sums where the path turns right. Range sums are prefix differences (mod 2^32).  Errors never change the state: add with index >= n fails with IndexOutOfRange; prefix_sum(e) with e > n and range_sum(l, r) unless l <= r <= n fail with InvalidRange.  Cost: add / prefix_sum / range_sum O(log n); new O(log n) (untouched subtrees are shared); from_list O(n log n); length O(1).

```
new(+n: Nat) -> Fenwick
from_list(+xs: List<&2, U32>) -> Fenwick
length(t: Fenwick) -> Nat
add(f: Fenwick, +i: Nat, +v: U32) -> Fenwick & Result<&2, &2, E.Error, Unit>
prefix_sum(f: Fenwick, +e: Nat) -> Result<&2, &2, E.Error, U32>
range_sum(f: Fenwick, +l: Nat, +r: Nat) -> Result<&2, &2, E.Error, U32>
```

## `prefix_trie`

Prefix trie from String keys to values of an erased type V. Representation: first-child/next-sibling tree. A TNode holds one character code c, the value stored for the key spelled by the path ending at it, the list of its children (down) and its next sibling. Sibling lists are kept in strictly increasing character-code order, so a preorder walk enumerates keys in String.order. The root carries the value of the empty key. Removal prunes nodes that no longer carry a value or children.  Errors: lookup/remove of an absent key and longest_prefix with no matching key return Fail{KeyNotFound}; the state is unchanged. Cost (key length m, alphabet branching b, entries listed r with total key length R): insert/lookup/remove/contains O(m * b) (sibling lists are scanned linearly); longest_prefix O(m * b); prefix_entries O(m * b + nodes below the prefix + R).

```
new(-V: Data) -> PrefixTrie<V>
insert(-V: Data, s: PrefixTrie<V>, key: String, v: V) -> PrefixTrie<V>
lookup(-V: Data, s: PrefixTrie<V>, key: String) -> Result<&2, &2, E.Error, V>
remove(-V: Data, +s: PrefixTrie<V>, +key: String) -> PrefixTrie<V> & Result<&2, &2, E.Error, V>
contains(-V: Data, s: PrefixTrie<V>, key: String) -> Bool
prefix_entries(-V: Data, s: PrefixTrie<V>, p: String) -> List<&2, BE.Entry<String, V>>
longest_prefix(-V: Data, s: PrefixTrie<V>, text: String) -> Result<&2, &2, E.Error, BE.Entry<String, V>>
```

## `graph`

Finite simple graph over U32 vertex ids, directed or undirected (fixed at construction).

Representation: INDEXED VERTEX SLOTS plus ADJACENCY BLOCKS. `ids: Array<U32>`
holds the vertex ids ascending in a floating window `[lo, hi)` of a
power-of-two block; `adj: Array<Array<U32>>` holds one adjacency block per
slot, each a power-of-two U32 block with a three word header
(`deg | size | lcap`) followed by its neighbour ids, ascending. The vertex id
is EXTERNAL and arbitrary in U32: the id-to-slot map is the sorted `ids`
block searched by binary search, so no id is reserved and no density is
assumed, and neighbour entries are external ids too, so moving a slot never
renumbers an edge.

Policies (unchanged): isolated vertices are allowed; `add_vertex` of an
existing vertex fails with `VertexExists`; edge operations fail with
`VertexNotFound` when an endpoint is missing; self-loops fail with
`SelfLoop`; adding an existing edge succeeds and changes nothing; removing a
missing edge fails with `EdgeNotFound`; `remove_vertex` deletes all incident
edges. Every failure returns the state unchanged.

EVERY operation, including the read-only ones, takes the graph by value and
returns it: the state is linear (it owns two `Base.Array`s), so a query
cannot silently duplicate the graph.

Cost (V vertices, D = degree of the vertex touched): `has_vertex` and the
lookup part of every other operation O(log V) indexed loads; `has_edge`
O(log V + log D); `add_edge`/`remove_edge` O(log V + log D) plus O(D) words
moved inside the single adjacency block that changes; `neighbors` O(D);
`vertices` O(V); `edges` O(V + E); `add_vertex`'s insertion and
`remove_vertex`'s slot removal move the SHORTER side of the window, O(V)
words worst case and O(1) at either end (the window floats, and the block
doubles on the side that needs room); `remove_vertex` undirected
O(D (log V + D)) because only the actual neighbours are visited, directed
O(V + E) because in-edges are not indexed.

```
new(directed: Bool) -> Graph
add_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
remove_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
add_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
remove_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
has_vertex(g: Graph, +v: U32) -> Graph & Bool
has_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Bool>
neighbors(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, List<&2, U32>>
vertices(g: Graph) -> Graph & List<&2, U32>
vertices_block(g: Graph) -> VBlk            # VB{g, blk: Array<U32>, n: U32}
edges(g: Graph) -> Graph & List<&2, E.Edge>
```

`vertices_block` is the INDEXED-VIEW form of `vertices`: the same ascending
sequence of vertex ids, written into slots `[0, n)` of a fresh `Array<U32>`
instead of a cons list, so enumerating costs no allocation per vertex. The two
are proved to denote one sequence (`proofs/graph/vblk.bend
vertices_block_seq`, exposed as END_TO_END `graph_vertices_block`); both are
public and both are covered by the runtime tests (`vs` and `vb` tokens of
`tests/graph/main.bend`). The caller owns the returned block and releases it
by dropping it.

## Retained LRU

`src/lru.bend` is a thin reuse entry for the pinned `reference/lru` snapshot --
nothing is re-implemented. Usage:

```
new_with_size(V, capacity, size) -> Result<String, Cache<String, V>>
new(V, capacity)                 -> Result<String, Cache<String, V>>
run(V, requests, cache, zero_key, zero_value, clock_events) -> Trace<String, V>
execute(V, zero_key, zero_value, cache, clock_events, request) -> Outcome<String, V>
```

Requests (`Add`, `Get`, `Peek`, `Contains`, `Remove`, `Purge`, `Resize`,
`Keys`, `Len`) and the explicit clock are the reference's own types; semantics,
errors and the trusted TypeScript residue are documented in
`reference/lru/README.md` and `docs/lru-compat.md`.

## DLL owning iterator

`src/dlist_iterator.bend`: `iter_first`, `iter_last`, `next`, `previous`,
`has_next`, `has_previous`, `position`, `set`, `add`, `remove`, and `finish`.
The iterator owns the arena DLL until `finish`; all calls thread that ownership.
See [semantics, proof scope, and Bend/C benchmarks](DLIST_ITERATOR.md).
