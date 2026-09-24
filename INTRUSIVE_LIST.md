# Intrusive doubly linked lists

`src/containers/intrusive_doubly_linked_list.bend` maintains membership of
application-owned nodes. Given a node identity, `remove` detaches it and
`prepend` attaches it to a root. Both perform a constant number of accesses;
with constant-time accessors they are O(1). They do not create or destroy the
node, move its payload, or scan the list.

Use this for entities moving between groups, scheduler queues, observers, or
other objects whose lifetime is independent of list membership. An entity
can participate in several associations by providing a different pair of
link accessors for each. Each association permits one list membership at a
time.

The existing `doubly_linked_list.bend` owns its arena and provides validated,
generational handles and positional insertion. This module leaves storage,
identity validity, payload lifetime, and root representation to the application.
Removing a member preserves its identity for immediate reuse in another root.
There is no mandatory container object, tail, member count, arena, or registry.

`DList` already removes a known handle in O(1) and recycles freed arena slots.
The contribution here is membership over **existing application-owned nodes**:
the application can reuse its own fields and identities across roots and
associations. A prewarmed object pool can repeatedly take a node, reset its
payload, attach it, process it, detach it and recycle it. Changing membership
does not require allocating an entity or a separate collection node.

| Concern | `DList` | `IntrusiveDoublyLinkedList` |
|---|---|---|
| Remove a known member | O(1), with checked generational handle | O(1) with constant-time accessors and valid membership |
| Insert at the head | Reuses an arena slot; amortized O(1) including growth | Links an existing detached node; O(1) with constant-time accessors |
| Move between roots | Remove and push; update the destination's list-local handle | Remove and prepend the same node identity |
| Keep application-owned payloads | Store external IDs, optionally with an application pool and ID-to-handle mapping | Use those IDs and application link fields directly |
| Several associations per entity | Separate lists and handles | Separate pairs of link accessors over the same identity |
| Stale/foreign membership | Checked by the collection | Application responsibility |

Both warmed implementations measured zero Bend allocator calls in the
[comparative workloads](benchmarks/INTRUSIVE_LIST.md). Choose this module for
the ownership and representation model; choose `DList` when its checked,
owning API is the better fit.

## Run the example

From a checkout containing this module:

```sh
bend tests/intrusive_doubly_linked_list/example.bend
```

The example starts with three entities in one group and moves entity 2 to
another by identity:

```text
Group 0: 1 3
Group 1: 2
```

The [complete example](tests/intrusive_doubly_linked_list/example.bend) uses
nominal entity IDs, different types for reading and writing roots, and a
single affine `Array<U32>` containing the application's fields. The identity
and root IDs are trusted, preallocated application values.

The [pooled pulse example](tests/intrusive_doubly_linked_list/pooled_pulses.bend)
adds payload fields and recycles four nominal entities across three pulses:

```sh
bend tests/intrusive_doubly_linked_list/pooled_pulses.bend
```

```text
3 pulses, 12 uses
Nodes created: 4 (all during prewarm)
Nodes available: 4
Payload sum: 2430
```

Every checkout resets the payload for its new use. Every return first removes
the entity from the active root, then puts it in the pool. The final payload
sum depends on all twelve resets; the factory counter stays at four. The
example's reserved storage and fixed workload guarantee sufficient capacity.
An application with unbounded bursts must define its own growth or rejection
policy. The pool does not reset payloads or validate lifetimes for the caller.

The [scheduler example](tests/intrusive_doubly_linked_list/scheduler.bend)
keeps the same entities in a render association while moving them between
ready and waiting queues. It checks both final scheduler roots, the unchanged
render order and the preserved payload sum on C and JS:

```sh
bend tests/intrusive_doubly_linked_list/scheduler.bend
```

```text
Ready: 2 3
Waiting: 1
Render: 1 2 3
Payload sum: 600
```

## Bind accessors once

Import the module and bind its closed `~` arguments in application functions:

```python
import ./src/containers/intrusive_doubly_linked_list.bend as IL

# These definitions come from the complete example.
def prepend(world: Array<U32>, group: Group, writer: Writer, node: Entity) -> Array<U32>:
  IL.prepend_as(~Array<U32>, ~Entity, ~Group, ~Writer,
    ~get_head, ~set_next, ~set_prev, ~set_nonempty,
    world, group, writer, node)

def remove(world: Array<U32>, writer: Writer, node: Entity) -> Array<U32>:
  IL.remove(~Array<U32>, ~Entity, ~Writer,
    ~next, ~prev, ~set_next, ~set_prev, ~set_head,
    world, writer, node)
```

Application code then calls `remove(world, writer, entity)` or
`prepend(world, group, writer, entity)`. Thread the returned world into the
next operation. Do not clone it to obtain a second reference.

| Parameter | Meaning |
|---|---|
| `S: Type` | Affine application state, including node fields and roots |
| `N: Data` | Stable node identity; an integer or a nominal/generational handle |
| `V: Data` | Observed value; often the entity identity itself |
| `H: Data` | Context for reading a root |
| `I: Data` | Context for writing that root; may differ from `H` |
| `C: Data` | Runtime callback context; captured mutable resources belong in `S` |
| `A: Type` | Fold accumulator; may own an array or other affine value |
| `T: Type` | Newly constructed result-list element |

The static arguments have these ordinary function types:

| Accessor | Type |
|---|---|
| `next`, `prev` | `S -> N -> S & Maybe<&2, N>` |
| `set_next`, `set_prev` | `S -> N -> Maybe<&2, N> -> S` |
| `get_head` | `S -> H -> S & Maybe<&2, N>` |
| `set_head` | `S -> I -> Maybe<&2, N> -> S` |
| `set_head_nonempty` | `S -> I -> N -> S` |
| `value` | `S -> N -> S & V` |

`None{}` represents no link. The two root setters are deliberately distinct:
`prepend` calls the nonempty setter exactly once; removing the head calls
the nullable setter, even when its successor is nonempty. Removing a nonhead
requires no root read or write. Root setters may perform application hooks,
provided they preserve coherent membership and unrelated links.

Bind accessors as individual closed static functions. A runtime record of
callbacks can allocate even when the logical operation only changes fields.
If an adapter has duplicable `+` parameters, give the static slot a closed
lambda with the expected function type, such as `~(s => i => n => set_full(s,
i, n))`. Pass varying callback inputs through `C`, rather than capturing the
affine world in a reusable closure.

## Operations

The primary module exposes 24 operations. Its `.bend` signatures and comments
are the reference; state-threading helpers live in `internal/`.

| Family | Operations | Behavior |
|---|---|---|
| Observations | `next`, `prev`, `value`, `get_head` | Forward to the selected accessor |
| Membership | `prepend`, `prepend_as`, `remove` | Constant accesses; preserve node and payload lifetime |
| Root queries | `is_empty`, `non_empty`, `at_least_two` | O(1) |
| Traversal | `foreach`, `fold_left` | Forward order; cache successor before callback |
| Search | `find` | First matching node identity; short-circuit |
| Predicates | `exists`, `forall`, `count`, `length` | O(n) worst case; length is not cached |
| Result list | `to_list` | Owning values in forward order |
| Builders | `from_values`, `from_nodes` | Forward construction; return an unpublished head |
| Pool | `pool_new`, `pool_free`, `pool_next` | LIFO reuse; make nodes at construction or exhaustion |
| Value wrapper | `new_node`, `types.DefaultNode<N,V>` | Optional `{next, prev, value}` storage record |

Applications needing the extended callback protocols can import
`src/containers/compat/intrusive_doubly_linked_list.bend`. It contains all the
primary operations plus the following helpers. Both facades forward to the
same implementation, without runtime dispatch or an extra callback record.

| Compatibility operations | Behavior |
|---|---|
| `find_some_this`, `find_convert`, `find_value`, `find_value_convert` | Alias and conversion/value searches |
| `foreach_remove_filter`, `foreach_remove_convert`, `foreach_remove_convert_filter` | Stateful removal visitors |
| `clear_list`, `clear_list_with_pool` | Empty root, then callbacks on the suffix and original head |
| `map_to_list`, `flat_map_to_list` | Tail-first callbacks; forward results; flat-map emits zero or one value |
| `map_from_values`, `map_from_nodes` | Conversion/factory builders |

Every removal visitor and clear operation also has an `_as` form with
separate read/write contexts. Unsuffixed forms use one context for both.
`find_some_this` aliases `find`; it needs no extra node interface or cached
option object. The unusual clear and mapping callback orders are explicit
compatibility behavior rather than new conventions for the core API.

`from_nodes` expects distinct, detached identities. The other builders
accept a factory that must supply such identities; that factory controls
allocation or reuse. `map_from_values` converts each input and then calls
the node factory; `map_from_nodes` maps each input directly to a node.
Factories and conversions execute in input order. The empty input returns
`None{}`. Builders do not publish a root or call its setters.

`new_node(~N, ~V, v)` returns `Node{None{}, None{}, v}`. Store these records in
application-owned storage and adapt their fields, or store links directly
in existing entities. The wrapper imposes no separate arena. Its `V: Data`
observation is suitable for immutable values and handles; an affine payload
can remain in `S` and be referred to by an observed handle.

## Bounds and callback behavior

Link traversal is not structurally decreasing in Bend. Traversals therefore
take an explicit `Nat` step bound and return the updated state alongside
`Result<&2, &1, Error, A>`. For a valid fixed or shrinking list, storage
capacity is a sufficient bound available in O(1); computing `length` just
to obtain the bound adds a scan. Empty lists succeed with bound zero.

`LimitExceeded{}` means the bound was exhausted before completion. Callback
effects already performed remain in the returned world; the result is not
a transaction. `clear_list` first checks that the original chain fits the
bound, so insufficient fuel performs no writes or callbacks. Map operations
first locate the tail; failure in that pass performs no mapping callbacks.
Each pass uses the supplied bound independently, so a two-pass map of n
members needs bound n, not 2n.

Observable behavior (clear, removal filters and mapping helpers refer to the
compatibility module):

- `foreach` and `fold_left` save the successor before invoking user code.
  Removing the current node is supported. The saved successor must remain
  valid in this association until it is visited; do not free or recycle it.
- Searches and `count` read the next link after an unsuccessful predicate
  or a counted value. Their predicates should normally preserve topology.
- Removal filters first process a prefix that re-reads the live head after
  the predicate and after `post_remove`. After keeping a head, tail visits
  cache the next node before calling the predicate. `False` removes the
  node; `True` keeps it. Do not independently detach a tail node that the
  filter will also remove. An unexpectedly missing live head or a rejected
  tail node with no predecessor returns `InvalidTraversal{}`.
- `clear_list` publishes an empty root before callbacks. For `[a,b,c]`,
  `post_remove` runs on `b,c,a`, each after its links are detached. Callbacks
  may reuse the detached node and change unrelated state, but must leave the
  unvisited original chain and its identities intact. An empty list invokes
  neither root setters nor removal callbacks.
- `map_to_list` and `flat_map_to_list` evaluate callbacks from tail to head,
  while their result retains forward order. `flat_map_to_list` accepts a
  `Maybe` result: it emits zero or one value for each input.
- `find_value` calls `eq(wanted, value)`; `find_value_convert` calls
  `eq(converted, wanted)`. Conversion occurs once per visited value. Failed
  conversions are skipped by searches and removed by conversion visitors.

For no removal callback, supply a closed no-op function such as
`~(s => c => n => s)`.

## Pool reuse

`types.Pool<N>` contains a free-list head and a count. `pool_free` takes the
world, the pool, and a detached node, returning the world and updated pool.
`pool_next` returns `S & (Pool<N> & N)`. The next link is cleared before
returning a reused node. `pool_new(size, ...)` makes `max(size, 1)` nodes;
size zero intentionally still creates one.

The pool uses the selected next link and preserves the payload. Its count
must equal the length of its acyclic free chain; pooled identities are distinct. Before
freeing a node, detach it from every association whose users require that
identity to remain live, and clear any payload references that the
application wants to release. The library cannot infer those lifetimes.
Double-free and recycling a node still in use violate the preconditions.

For `clear_list_with_pool`, put the pool in `S`, use `C` to locate it if
needed, and supply a removal callback that applies `pool_free` and stores
the returned pool. The [test adapter](tests/intrusive_doubly_linked_list/fixture.bend)
contains a complete `free`/`take` implementation.

## Preconditions and concurrency

Accessors must select the same association and coherent read/write views
of a root. Link reads are observations. Link writes preserve every other
field. Valid lists are acyclic, have distinct identities, reciprocal links,
a head with no predecessor, and a tail with no successor. `prepend` requires
a detached node; `remove` requires a member of the supplied root.

A node identity is not a proof of membership or liveness. Applications can
use nominal or generational handles and validate external input at their
boundary. In particular, `Base.Array` indexing is not bounds validation:
these examples must never receive an out-of-range raw ID. The generic core
adds no global registry, per-node allocation, or implicit validation scan.

Keep one affine owner of a world. Concurrent edits to the same association
need synchronization or partitioned ownership outside this module. Separate
worlds can be processed independently. There are no atomics or lock-free
claims in this API.

## Verification and performance

Run the complete focused gate with Bend 2.0.25, clang, Node.js and Python 3.10+:

```sh
python3 tools/check_intrusive.py --bend bend --cc clang
```

The gate checks generated-source consistency for both API facades and all
macro-generated proofs, requires clean kernel output with no holes or unsafe
reliance, and checks the package exports. It runs four examples on C and JS,
compares 4,313 histories / 36,809 operations against an independent Python
sequence-and-event model, and requires six well-typed runtime mutants to fail.
State comparisons include every root, both associations, payload fields,
pool state and callback events.

### What the proofs establish

The [proof entry point](proofs/containers/intrusive_doubly_linked_list/proof.bend)
checks these layers. The ghost model is used only by the checker, never by the
runtime list operations.

| Layer | Checked statement | Files in the proof package |
|---|---|---|
| Ordered sequences | Distinct members, matching root, reciprocal next/prev links, null outer ends; preservation under prepend and head/interior/tail removal | `graph.bend`, `shape.src`, `edits.src` |
| Primitive execution | Actual exported prepend/remove equal independent write programs, then the graph edits, given primitive accessor equations | `writes.bend`, `adapter.src`, `spec.bend` |
| Arbitrary finite histories | Every legal history preserves the ordered-sequence invariant; payload/other-association frame is unchanged | `history.src` |
| Concrete owned storage | Actual `Base.Array.get/set` satisfy every primitive law for four nominal node IDs and two nominal roots, with separate reader/writer types; public-function histories refine the valid final sequence | `array_adapter.src` |
| Unrelated membership | Disjoint chains keep every link; other roots retain their heads; removed nodes have cleared links under the stated validity premises | `frames.src` |
| Constant write bound | Remove has at most four primitive writes; prepend at most three, independent of list size | `costs.bend` |
| Nonempty witness | Eight legal edits exercise middle/head/tail removal and identity reuse with all initial and history premises discharged | `example.bend` |
| Traversal and reuse laws | Forward fold on structural chains; clear's root/suffix/head callback order on its stated observer instance; pool LIFO under read-after-write | `fold.bend`, `clear.bend`, `writes.bend` |

The generic semantic theorem is conditional on **primitive adapter laws**, not
an assumption that the final list is valid. The graph-to-storage representation
can erase ghost write history. Getters observe its links/root without changing
represented state; setters realize the corresponding field write and preserve
the modeled frame. The concrete array witness proves those laws rather than
postulating them. It covers every history length over its finite identity set;
the graph preservation theorem itself permits arbitrary identity types and
list lengths. Other layouts, including the benchmark's variable-size packed
U32 adapter, must establish their own laws; their C/JS tests do not become a
formal proof by resemblance to the witness.

The frame can model payloads and another association. Effectful root hooks
are covered by ordered write refinement. A hook that changes modeled frame
state must use an appropriate extended model; it does not satisfy an
unchanged-frame theorem automatically. The runtime core still permits the
explicit callback protocols described above.

`tools/check_intrusive_proofs.py` includes two further negative controls:

- A coordinated wrong-head edit keeps the implementation, write specification
  and graph execution in agreement. The old write gate and adapter refinement
  pass, while the independent sequence-invariant proof rejects it.
- An owned-array setter that ignores its write still typechecks as runtime
  code, but the concrete adapter-law proof rejects it.

Timeouts, missing imports and syntax errors never count as successful mutant
rejections. These controls guard against vacuous agreement between layers.

Formal coverage does not extend to every callback-driven traversal, every
application adapter, compiler/backend correctness, memory allocation or
concurrency. Independent histories, boundary cases and mutation checks cover
the remaining API behavior. No unsafe axiom or external proof service is used.

The allocation test instruments the emitted Bend `heap_alloc` entry during
the hot loop, including temporary tuples and closures. Setup, output and
teardown are outside the interval. A forced allocation is a positive
control. It checks zero allocations for 400,000 changing-node prepend/remove
edits and 200,000 preallocated pool operations. A C program performs the same
churn with the same checksum; timings are reported as seven-sample medians.
Generated reports are in `build/intrusive-list/`.

The zero-allocation result is for the fixed primitive-array adapter on the
native C backend and the tested compiler. Arbitrary callbacks, owning result
lists, node factories, boxed representations and the JavaScript backend do
not inherit that guarantee. Timing is descriptive, not a CI threshold. A
compiler or representation change should rerun the gate.

`benchmarks/intrusive.py` extends this with complete pooled lifecycles and
changing cross-root membership at several working-set sizes. It compares the
direct public `DList` API, a DList storage diagnostic without the generation
facade, this module and plain C against an independent ordered-map/stack oracle. Timing uses separate binaries without allocator
counters and an independent repeat of the same executable as an A/A control.
Separate builds measure live allocator-block bytes, including prewarmed arenas. The [benchmark notes](benchmarks/INTRUSIVE_LIST.md) give the work
definition, warmup, allocation scope, raw results and reproduction command.
The focused gate runs its correctness and allocation checks; the timing sweep
is an explicit benchmark command, without a machine-dependent speed gate.
