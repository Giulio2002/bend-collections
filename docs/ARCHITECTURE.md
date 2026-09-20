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
graph          -> balanced_search_tree (U32 instance, twice: vertex map and
                  neighbour set)
doubly_linked_list -> balanced_search_tree (Nat instance, node store)
lru            -> reference/lru (immutable pinned snapshot; src/lru.bend is a
                  thin reuse entry, nothing is re-implemented)
```

Nothing re-implements Base's Map, Set or List-as-stack.

## Runtime representation of each structure

No structure stores in a linked list what its algorithm does not need as
links. The runtime representation of every structure, what it is indexed by
and where a genuine link survives:

| structure | runtime storage | indexing | links |
|---|---|---|---|
| `dynamic_array` | `Base.Array` of `Maybe<T>` slots, capacity `2^depth` | slot `i` is element `i` | none |
| `deque` | `Base.Array` of `Maybe<T>` slots; the elements are the window `[lo, lo + len)` | slot `lo + j` is element `j` | none |
| `queue` | the deque (enqueue = push_back, dequeue = pop_front) | as the deque | none |
| `bitset` | `Base.Array` of packed `U32` words | bit `i` is word `i / 32`, bit `i % 32` | none |
| `union_find` | three parallel `Base.Array`s (parent, size, members) | element `i` is slot `i` | none |
| `fenwick_tree` | one `Base.Array` of `U32` cells, flat split-point layout | value `t` is cell `2^d + t`; a block `[o, o + 2^p)` keeps its partial sum at cell `o + 2^(p-1)` | none |
| `segment_tree` | two `Base.Array`s of `U32` cells (sums, lazy tags), same split-point layout | as fenwick, plus the tag array at the block's split point | none |
| `binary_heap` | `Base.Array` of `Maybe<A>` slots, capacity `2^depth` (PACKED array heap) | element `i` is slot `i`, children `2i+1`/`2i+2`, parent `(i-1)/2` | none |
| `balanced_search_tree` | red-black tree of `Node{color, l, entry, r}` | — | tree children |
| `prefix_trie` | trie nodes `TNode{c, val, down, next}` | `down` = children, `next` = the sibling chain of one node's children | trie children |
| `doubly_linked_list` | `Base.OrdMap<Nat, Node>` node store (an indexed arena); each node holds `Maybe<Nat>` prev/next handles | node handle (a `Nat`) | DLL prev/next |
| `graph` | `Base.OrdMap<U32, Base.OrdMap<U32, Unit>>` adjacency (native map of native sets) | vertex id | none |
| `lru` (retained) | `reference/lru` snapshot: `Map` + recency order | key | LRU recency order |

The only remaining node-linked storage is where the operator's rule allows
it: tree/trie children (`balanced_search_tree`, `prefix_trie`),
doubly-linked prev/next (`doubly_linked_list`) and LRU recency. `graph` and
`doubly_linked_list` use Base's native map, not a hand-written list.
`binary_heap` **is now a packed array heap**: the elements occupy slots
`[0, size)` of one `Base.Array`, the shape IS the index arithmetic, and no
node or link is allocated per element (`src/binary_heap.bend`, proofs in
`proofs/binary_heap/`). The migration and its measured effect are recorded
in `WORK_LOG.md`.

Self-audit: the table above was checked against `src/*.bend` (the `type`
declaration of each structure) and against the emitted C of the native
benchmark binaries (`build/bench/bend/<id>`), which is where `Base.Array`
shows up as a flat block and a `Data` node as a heap-allocated cell.

## Linear versus persistent state

`Base.Array` is a **linear** type: it is a flat array in the native backend
with O(1) indexed read and write, and it cannot be duplicated or dropped
implicitly. The structures built on it (`dynamic_array`, `deque`, `queue`,
`bitset`, `union_find`, `fenwick_tree`, `segment_tree`) are therefore
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
