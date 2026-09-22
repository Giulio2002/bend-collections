# Architecture

## Layers

```
types/<id>.bend      neutral data types (entries, ops, observations, errors).
                     Imported by src/, spec/, proofs/ and tests/ alike; contains
                     no behaviour.

spec/<id>.bend       the independent mathematical model. Imports ONLY Base,
                     spec/ and types/ (automation/acceptance.py enforces this by
                     scanning every spec import). Written as lists/maps, never in
                     terms of the runtime representation.

src/<id>.bend        the public API and the real representation. Imports Base,
                     types/ and, where a structure reuses another, the other
                     src/ module. Never imports spec/ or proofs/.

proofs/<id>.bend     the public proof entry point for one structure; the
                     supporting modules live in proofs/<id>/.
proofs/lib/          reusable checked facts about Base (logic, nat, u32, list,
                     word, array, order).

END_TO_END.bend      every public law, stated over src/ and spec/ directly.
PROOF.bend           the single root; imports END_TO_END.bend and nothing else.
```

`PROOF.bend` -> `END_TO_END.bend` -> `proofs/<id>.bend` -> `proofs/<id>/*` is the
whole checked closure. `automation/acceptance.py` walks it and rejects any
`@unsafe`, hole or foreign import anywhere inside.

## Reuse graph between structures

```
dynamic_array  -> proofs/lib/array.bend (Base.Array)
bitset         -> proofs/lib/array.bend (Base.Array of packed U32 words)
queue          -> deque
graph          -> proofs/lib/{array,array2}.bend (indexed vertex slots and
                  adjacency blocks; it no longer uses the search tree)
doubly_linked_list -> proofs/lib/array.bend (parallel index arenas; it no
                  longer uses the search tree as a node store)
lru (retained) -> reference/lru (immutable pinned snapshot, re-exported
                  byte-identical by src/lru.bend and proofs/lru.bend)
lru (benchmarked) -> src/lru/fast.bend: a DIFFERENT runtime (native Map from
                  key to slot, plus an indexed arena with an intrusive
                  doubly linked recency list and U32-limb metrics). It is
                  proved on its own against spec/lru_fast.bend in
                  proofs/lru_fast/**; the retained reference proofs do NOT
                  prove it.
```

Nothing re-implements Base's Map, Set or List-as-stack.

## Runtime representation of each structure

No structure stores in a linked list what its algorithm does not need as
links. The runtime representation of every structure, what it is indexed by
and where a genuine link survives:

| structure | runtime storage | indexing | links (why the algorithm needs them) | representation-bridge / invariant proofs |
|---|---|---|---|---|
| `dynamic_array` | `Base.Array` of `Maybe<T>` slots, capacity `2^depth` | slot `i` is element `i` | none | `proofs/dynamic_array/{state,layout,walk,closed}.bend` |
| `deque` | `Base.Array` ring of `T` slots, capacity `2^depth`; an empty deque owns NO block (`DE{}`) because `Array.new` needs a filler element and `T` is an arbitrary `Data` with no default | element `j` is slot `wrap(lo + j)`, `wrap(x) = x < cap ? x : x - cap` | none | `proofs/deque/{ring,state,grow,layout,stepok,reads,pushes,steps}.bend` |
| `queue` | the deque (enqueue = push_back, dequeue = pop_front) | as the deque | none | `proofs/queue/{steps,trace}.bend` over the deque shadow |
| `bitset` | `Base.Array` of packed `U32` words | bit `i` is word `i / 32`, bit `i % 32` | none | `proofs/bitset/{state,loops,fastcount,steps}.bend` |
| `fenwick_tree` | one `Base.Array` of `U32` cells, flat split-point layout | value `t` is cell `2^d + t`; a block `[o, o + 2^p)` keeps its partial sum at cell `o + 2^(p-1)` | none | `proofs/fenwick_tree/{state,arr,walk,init,steps}.bend` |
| `segment_tree` | two `Base.Array`s of `U32` cells (sums, lazy tags), same split-point layout | as fenwick, plus the tag array at the block's split point | none | `proofs/segment_tree/{state,arr,walk,init,steps}.bend` |
| `binary_heap` | `Base.Array` of `Maybe<A>` slots, capacity `2^depth` (PACKED array heap) | element `i` is slot `i`, children `2i+1`/`2i+2`, parent `(i-1)/2` | none | `proofs/binary_heap/{state,slots,idx,up,down,steps}.bend` |
| `balanced_search_tree` | red-black tree of `Node{color, l, entry, r}` | — | tree children: a red-black BST is defined by its two-child nodes | `proofs/balanced_search_tree/{sorted,steps,colour}.bend` |
| `prefix_trie` | trie nodes `TNode{c, val, down, next}` | `down` = children, `next` = the sibling chain of one node's children | trie children: a trie node's children are its genuine edges (the sibling chain is the part still to migrate) | `proofs/prefix_trie/{keys,ops,steps,trace}.bend` |
| `doubly_linked_list` | THREE parallel `Base.Array` blocks (`vals: Maybe<T>`, `prevs: U32`, `nexts: U32`) sharing one index space | the element id IS its slot index (a monotone counter, never reused) | prev/next as ARENA INDICES: the requested structure is a doubly linked list with stable handles | `proofs/dlist/{state,links,items,alive,ibcore,rm,trace}.bend` |
| `graph` | indexed vertex slots plus adjacency blocks: `ids: Array<U32>` (ascending, in the window `[lo, hi)`) and `adj: Array<Array<U32>>`; an adjacency block is one power-of-two `U32` block whose first three words are `deg`, `size`, `lcap`, followed by the ascending neighbour ids | vertex id -> slot by binary search over `ids`; neighbour -> position by binary search inside the block | none (adjacency is contiguous, not linked) | `proofs/graph/{state,search,blk,nbrs,gstep,gtrace}.bend`; the BLOCK enumeration `vertices_block` in `proofs/graph/vblk.bend` |
| `lru` (retained) | `reference/lru` snapshot: `Map` + recency order | key | LRU recency order (inherent to the algorithm) | `proofs/lru.bend` (re-export of the pinned snapshot) |
| `lru` (benchmarked, `src/lru/fast.bend`) | native `Map<&2, Maybe<&2, U32>>` (key -> `Some{slot}`) plus an arena: `kys: Array<String>`, `ents: Array<Slot<V>>` (`Live{v}` / `Timed{v, deadline}`), `prevs`/`nexts: Array<U32>`, metrics as ten `U32` limbs in one `Array<U32>` | key -> slot through the native Map (crit-bit trie; the C reference uses a hash table, see docs/C_EQUIVALENCE.md); proofs: `proofs/lru_fast/` (`state.bend` invariant `inv`: links agree with the ghost order, free chain, table <-> order) | intrusive doubly linked recency as arena indices: O(1) touch/evict is the algorithm | `proofs/lru_fast/{state,table,chain,steps,trace}.bend` |

### Enumeration without a cons spine

`graph.vertices` has two public forms and they denote the SAME ordered
sequence (`proofs/graph/vblk.bend vertices_block_seq`):

* `vertices(g) -> Graph & List<U32>` -- the List form, unchanged;
* `vertices_block(g) -> VB{g, blk: Array<U32>, n: U32}` -- the block form:
  the ascending id window is copied into slots `[0, n)` of a fresh
  `Array<U32>` and the caller reads it by index. No cons cell is allocated.

The block form is what `benchmarks/bend/graph.bend` folds, because the pinned
`benchmarks/native/graph.c` `gr_vs` also folds its vertex keys in order
without building a list: the List form divided a Bend list construction by a
C fold (3.0-3.4x), the block form measures 0.86-1.29x with bit-identical
checksums. This is the operator's 2026-09-21 representation clarification;
the List form and all of its proofs are retained, and `tests/graph/main.bend`
exercises both (`vs` and `vb` tokens, answered identically by the oracle,
with two dedicated mutants of the copy loop).

`bitset.to_list` is the one remaining row whose C reference folds without
building a list; the same treatment would apply to it and has not been done.

### Constructors allocate eagerly

Every constructor builds the normal usable representation immediately and
initialises the storage it needs; none of them returns a deferred placeholder
that charges its allocation to the first operation. `dynamic_array`, `bitset`,
`binary_heap`, `fenwick_tree`, `segment_tree`, `graph` and
`doubly_linked_list` all allocate (and fill) their first block inside `new`.
Growth on later insertions is the conventional doubling; an empty structure
does not reserve future capacity. Deferred-initialization variants tried in
iterations 0011-0012 were removed in 0013/0014 at the user's instruction.

The one structure whose empty state owns no block is `deque` (and `queue`,
which wraps it): `Base.Array.new` needs a filler ELEMENT, and the deque's
element type is an arbitrary `Data` with no default value, so an empty
generic ring cannot allocate one. `DE{}` is that zero-capacity ring, the
first pushed element is the filler, and the pinned `benchmarks/native/deque.c`
does allocate one slot in `dq_init` -- the difference is disclosed in
docs/C_EQUIVALENCE.md rather than claimed as a speedup.

The remaining node-linked storage is where the operator's rule allows it:
tree/trie children (`balanced_search_tree`, `prefix_trie`), doubly-linked
prev/next (`doubly_linked_list`, as ARENA INDICES in parallel `Base.Array`
blocks) and LRU recency -- plus ONE place where it is not yet where it should
be: the `union_find` member list is still a cons list inside the arena slot
rather than `next`/`last` index links. Both that and the trie's sibling chain
are open representation work, named as such here rather than defended. `graph` holds no links at all: the
adjacency of a vertex is a contiguous sorted block of neighbour ids.
`prefix_trie` is the one structure whose migration is still outstanding (its
children are a first-child/next-sibling chain of `TNode` records).
`binary_heap` **is now a packed array heap**: the elements occupy slots
`[0, size)` of one `Base.Array`, the shape IS the index arithmetic, and no
node or link is allocated per element (`src/binary_heap.bend`, proofs in
`proofs/binary_heap/`). The migration and its measured effect are recorded
in `WORK_LOG.md`.

Self-audit: the table above was checked against `src/*.bend` (the `type`
declaration of each structure) and against the emitted C of the native
benchmark binaries (`build/bench/bend/<id>`), which is where `Base.Array`
shows up as a flat block and a `Data` node as a heap-allocated cell. The
`binary_heap` row was re-checked after its migration: `type Heap` is the
single record `BH{size, n, depth, cap, slots: Array<Maybe<A>>}` with no node
type left in the file, and the emitted C of `benchmarks/bend/binary_heap.bend`
says of a block that it "owns one allocation in its physical class (an ARR of
class c 2^c Terms in 2^c words)" and that "get, set, swap, size and new open
no half" -- one flat allocation, indexed access, no per-element node.

## Linear versus persistent state

`Base.Array` is a **linear** type: it is a flat array in the native backend
with O(1) indexed read and write, and it cannot be duplicated or dropped
implicitly. The structures built on it (`dynamic_array`, `deque`, `queue`,
`bitset`, `fenwick_tree`, `segment_tree`) are therefore
threaded - every operation takes the structure and gives it back - and
released explicitly where a driver needs it (`bitset`, `fenwick_tree` and
`segment_tree` expose `dispose` and `clone`). Their proofs are stated about
`thaw(t)`, the array built from a Data mirror tree `t`
(`proofs/lib/array.bend`), so arrays never appear in a proof term; the
per-operation and trace laws take a shadow (for example
`Sh{depth, lo, len, tree}` for the deque) and say which shadow the operation
lands on.

Generic array-backed structures additionally carry executable `*_at`
specializations (`~T` template parameters), because Bend 2.0.16's native
backend miscompiles `Base.Array` operations at an open element type
(`docs/VALIDATION.md`). `proofs/<id>/closed.bend` proves each specialization
equal to the parametric definition the laws are about, so every law transfers
to the code the tests and benchmarks actually run.

The remaining structures are persistent `Data` values and their laws are
stated directly over the runtime value. Which of the two a structure uses is a
performance decision with a proof cost: see the cost model at the top of
`BENCHMARKS.md`.

## Per-structure proof shape

Each `proofs/<id>/` contains the same four ideas, named consistently:

| module | contents |
|---|---|
| `steps.bend` | `abs` (abstraction), `inv` (representation invariant), `StepOK`, `step_ok` — every operation and every error path |
| `trace.bend` | `view`, `trace_from`, `inv_from` — arbitrary finite operation lists |
| others | the structure-specific lemmas (`tree.bend`, `query.bend`, `sorted.bend`, `specops.bend`, `model.bend`, `layout.bend`, …) |

`step_ok` is stated for *every* state satisfying `inv`, not only for reachable
ones; the trace law then composes it over an arbitrary finite op list starting
from the real constructor.

## Comparator parameterisation

`binary_heap` and `balanced_search_tree` are generic in a comparator. The laws
are Bend *templates* over `~cmp` together with `~o : O.Order(~K, ~cmp)` (flip,
antisymmetry, transitivity, in `proofs/lib/order.bend`). A template is only
checked when it is instantiated, so both structures instantiate every law at
`(U32, U32.cmp)` and `(String, String.order)` inside `proofs/<id>.bend`, and
`END_TO_END.bend` restates the instances.

## balanced_search_tree

A red-black binary search tree:

```
type Color = R | B
type Tree<K, V> = Leaf | Node{color, l, e, r}
type UpD<K, V>  = TD{t} | UF{t}          -- deletion: same black height / one less
type SM<K, V>   = SMNone | SMSome{e, rest}
type OrdMap<K, V> = BST{size: Nat, root: Tree<K, V>}
```

Insertion is Okasaki's: the new node is red and `balance` repairs the single
red-red edge below a black node. Deletion is the conventional functional CLRS
fixup. Bend forbids nested matches on constructor fields, so each case analysis
is a chain of single-match helper definitions (`bal_ll` … `balance`,
`fl_b3` … `fix_left`, and their mirrors) — the chain is the case analysis, not
an abstraction layer.

The comparison of the searched key against a node's key is computed by the
caller and passed down (`a`), so every recursive call is on a strict subtree and
Bend's termination check accepts it.

## Benchmarks

```
benchmarks/workloads.py   one row per (operation, workload)
benchmarks/run.py         builds both sides in release mode, calibrates, samples
benchmarks/bend/<id>.bend the Bend driver  ] identical argv, identical LCG,
benchmarks/native/<id>.c  the C reference  ] identical checksum fold
benchmarks/native/common.h    LCG, mix, arena, timing, DoNotOptimize barrier
benchmarks/native/redblack.h  the C red-black ordered map (shared by three drivers)
```

Each driver times three in-process regions of the same round (build + settle +
k measured operations + destroy): A with `k = 2 x count`, B with `k = count`
and C with `k = 0`, the build-and-destroy control. `A - B` is the cost of
`count x reps` measured operations with building, argument generation, process
start-up and file IO removed symmetrically; because both A and B end in a
state the operation has been applied to, a size-changing operation cannot move
deallocation work out of the difference. `argv[5]` selects whether the regions
run `ABC` or `CBA` and the runner alternates it over the samples, so a
monotone machine drift cancels. `verified` is true only when the Bend and C
checksums of *all three* regions agree.

An operation that removes elements cannot be isolated this way -- a round can
only remove what it built, so the difference stays a few percent of the round
and its sign is noise. Those rows are measured as a **restoring pair**
instead: the driver runs the removal together with the insertion that puts the
element back, on both sides, so the structure keeps its size and the batch can
be made arbitrarily long. The reported nanoseconds are the pair's, charged to
the removal (one insertion too many, never one too few); BENCHMARKS.md flags
every such row.
