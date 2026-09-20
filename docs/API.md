# API index

One public module per structure, `src/<id>.bend`. Every operation below is the
one named in `inventory/structures.json`; the exact error semantics and the
cost of each operation are documented in the header comment of the source file
(and repeated by the specification in `spec/<id>.bend`).

Some structures are **persistent**: an update returns a new value and shares
everything it did not have to rebuild. The array-backed ones (`dynamic_array`,
`deque`, `queue`, `bitset`, `union_find`, `fenwick_tree`, `segment_tree`) are
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
reserve cost O(depth)). `slots` is a Base.Array of 2^depth slots; slots
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

Doubly linked list with stable opaque handles, values of an erased type T. Representation: nodes {value, prev id, next id} in an ordered map keyed by element id (the Nat instance of src/balanced_search_tree.bend), plus head, tail, element count, the next fresh id and the list's tag. Ids are never reused, so a handle to a removed element is detected as stale; a handle whose tag differs from the list's is rejected as foreign. (Tags are chosen by the caller of new; lists that must reject each other's handles need distinct tags.) Every failure returns the state unchanged.  Cost (n elements ever inserted): every handle operation, push and length O(log n) (map lookups/updates, a constant number per operation); to_list O(n log n).

```
new(-T: Data, tag: Nat) -> DList<T>
length(-T: Data, s: DList<T>) -> Nat
push_front(-T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle
push_back(-T: Data, s: DList<T>, x: T) -> DList<T> & E.Handle
insert_before(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>
insert_after(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, E.Handle>
remove(-T: Data, s: DList<T>, h: E.Handle) -> DList<T> & Result<&2, &2, E.Error, T>
get(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, T>
set(-T: Data, s: DList<T>, h: E.Handle, x: T) -> DList<T> & Result<&2, &2, E.Error, Unit>
next(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>
prev(-T: Data, s: DList<T>, h: E.Handle) -> Result<&2, &2, E.Error, Maybe<&2, E.Handle>>
to_list(-T: Data, s: DList<T>) -> List<&2, T>
```

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

## `union_find`

Disjoint-set union over the elements 0 .. n-1.  Representation: three parallel native `Base.Array` arenas of 2^depth slots (2^depth >= n), indexed by element: `roots[x]` is x's class representative, and at a representative r, `sizes[r]` is its exact class size and `members[r]` the list of its members. `Base.Array` is linear, so every operation takes the structure and gives it back, and a structure that is no longer needed is released with `dispose`.  Union by size with eager full compression: the representative of the larger class survives (ties: the class of the first argument) and every member of the smaller class is repointed at it immediately. Because every element points straight at its representative, `find` is a single indexed read and never rewrites the structure: this is the documented Bend-appropriate equivalent of path compression, performed eagerly at union time instead of lazily at find time. `benchmarks/native/union_find.c` implements the same algorithm.  Errors never change the state: any index >= n yields OutOfRange.  Capacity: the arena depth stops at 31 (2^31 slots), so every slot index is a representable U32; the laws about `new(n)` carry that as an explicit premise.  Cost (documented, not proved): find / connected / component_size / component_count are a constant number of indexed reads; union performs one indexed write per member of the smaller class plus a constant number of reads; new O(n).

```
new(+n: Nat) -> UnionFind
find(s: UnionFind, +x: Nat) -> Result<&2, &2, E.Error, Nat>
union(s: UnionFind, +a: Nat, +b: Nat) -> UnionFind & Result<&2, &2, E.Error, Bool>
connected(s: UnionFind, +a: Nat, +b: Nat) -> Result<&2, &2, E.Error, Bool>
component_size(s: UnionFind, +x: Nat) -> Result<&2, &2, E.Error, Nat>
component_count(s: UnionFind) -> Nat
```

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

## `segment_tree`

Segment tree over n U32 values with lazy range addition; all arithmetic wraps modulo 2^32.  Representation: a perfect tree of depth d (2^d >= n). A leaf stores a value; an internal node stores a lazy tag z (pending addition for every value below it) and the sum of its subtree's values including its own tag (but excluding tags above it). The value at index i is the stored leaf plus all tags on the path to it.  get(i) / set(i, v)      walk the path, accumulating tags; set stores v minus the accumulated tags at the leaf range_query(l, r)       prefix(r) - prefix(l); a prefix walk adds the sums of fully covered left subtrees range_add(l, r, v)      lazy: add v to the first r values, then -v to the first l values; a fully covered subtree only receives a tag (O(1) node update), never a walk  Errors never change the state: get/set with index >= n fail with IndexOutOfRange; range_query/range_add unless l <= r <= n fail with InvalidRange.  Cost: every operation visits O(log n) nodes; each node visit scales a tag by the subtree width with U32.shln (O(log n) shifts), so get/set/ range_query/range_add cost O(log^2 n) word operations. new O(log n) (shared zero subtrees); from_list O(n log^2 n); length O(1).

```
new(+n: Nat) -> SegTree
from_list(+xs: List<&2, U32>) -> SegTree
length(t: SegTree) -> Nat
get(s: SegTree, +i: Nat) -> Result<&2, &2, E.Error, U32>
set(s: SegTree, +i: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>
range_query(s: SegTree, +l: Nat, +r: Nat) -> Result<&2, &2, E.Error, U32>
range_add(s: SegTree, +l: Nat, +r: Nat, +v: U32) -> SegTree & Result<&2, &2, E.Error, Unit>
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

Finite simple graph over U32 vertex ids, directed or undirected (fixed at construction). Representation: a red-black tree ordered map (src/ balanced_search_tree.bend, U32 instance) from each vertex to the ordered set (a red-black map to Unit) of its out-neighbours; an undirected edge is stored in both endpoint sets. Policies: isolated vertices are allowed; add_vertex of an existing vertex fails with VertexExists; edge operations fail with VertexNotFound when an endpoint is missing; self-loops fail with SelfLoop; adding an existing edge succeeds and changes nothing; removing a missing edge fails with EdgeNotFound; remove_vertex deletes all incident edges. Every failure returns the state unchanged.  Cost (V vertices, D = max neighbour-set size): has_vertex/add_vertex O(log V); add_edge/remove_edge/has_edge O(log V + log D); neighbors O(log V + D); vertices O(V); edges O(V + E); remove_vertex O(V log D + log V) because every neighbour set is visited (in-edges of directed graphs are not indexed separately).

```
new(directed: Bool) -> Graph
add_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
remove_vertex(g: Graph, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
add_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
remove_edge(g: Graph, +u: U32, +v: U32) -> Graph & Result<&2, &2, E.Error, Unit>
has_vertex(g: Graph, +v: U32) -> Bool
has_edge(g: Graph, +u: U32, +v: U32) -> Result<&2, &2, E.Error, Bool>
neighbors(g: Graph, +v: U32) -> Result<&2, &2, E.Error, List<&2, U32>>
vertices(g: Graph) -> List<&2, U32>
edges(g: Graph) -> List<&2, E.Edge>
```

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
