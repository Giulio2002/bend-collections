# Proof status

Checked with the pinned toolchain in `inventory/toolchain.json`
(bend 2.0.16, sha256 `da9bc514…`, base sha256 `e149828c…`).

Single root: `PROOF.bend` imports `END_TO_END.bend`, which imports every
`proofs/<id>.bend` entry plus `proofs/lru.bend`.

**Current state (iteration 0015): `bend PROOF.bend` reports `All terms check`,
with 3876 template instances** (fresh run; `bend END_TO_END.bend` prints the
same line, and `automation/acceptance.py` re-ran both plus the full
`tools/validate.py` suite: `build/validation.json` complete=True, 0 failures,
all twelve structures runtime/boundaries/differential/mutations/trace_proof
passed, `balanced_search_tree` and `graph` also structural). The closure covers all twelve structures, the
retained LRU (`proofs/lru.bend`) and the benchmarked indexed LRU
(`proofs/lru_fast.bend`, laws `lru_fast_*` in `END_TO_END.bend`). No
`@unsafe`, no holes, no axioms, no `?`-terms anywhere in the closure
(`automation/acceptance.py` re-checks this by scanning the import graph).

"Unsafe annotations" in the checker's summary line count *template
instantiations*, not unchecked terms: every instance is fully checked.

New in iteration 0015: `graph.vertices_block`, the public block (indexed
view) enumeration of the vertex ids, is proved in `proofs/graph/vblk.bend`
and exposed as END_TO_END `graph_vertices_block`: the graph comes back
unchanged, the produced block is exactly the one the mirror builds, and its
window `[0, n)` is the SAME ordered list `graph.vertices` returns. Both
enumerations stay public and both are exercised at runtime.

## What each structure proves

Every structure follows the same shape:

* an **abstraction** from the runtime representation to the independent model
  in `spec/<id>.bend` (which imports only `spec/` and `types/` and `Base`);
* a **representation invariant** that the constructor establishes;
* `step_ok`: for **every inventoried operation, including every error path**,
  the runtime step refines the spec step *and* preserves the invariant, from
  *any* state satisfying the invariant (not only reachable ones);
* a **trace law**: for an *arbitrary finite list of operations* run from the
  real constructor, the runtime run equals the spec run, and the final state
  still satisfies the invariant.

Seven structures — `dynamic_array`, `deque`, `queue`, `bitset`,
`union_find`, `fenwick_tree` and `segment_tree` — store their elements in
native `Base.Array`, which is a **linear** type. Their laws are therefore
stated in the *shadow* form: about `real(sh)`, the structure built from Data
mirror trees, with the law naming the shadow the operation lands on and
asserting its model and its invariant. `proofs/<id>/state.bend` proves
`real_inj` for each of them — a runtime structure determines its shadow — so
that form pins the abstract state rather than merely asserting the existence
of some shadow (laws `*_shadow_unique`).

Where a structure grows its array, the laws about the growing operations
carry the representation's capacity condition as an **explicit premise**,
never a hidden bound: `capacity(n)` for `fenwick_tree`, `segment_tree`,
`bitset` and `union_find` (a premise of the constructor laws only), and
`depth + (number of pushes) <= 31` for `deque`, `queue` and `binary_heap` (a
premise of the push, from_list and trace laws, discharged for a whole
operation list at once because `StepOK` also yields
`depth(sh2) <= depth(sh) + pushcost(op)`; for the heap `pushcost` of
`FromList{ys}` is `length(ys)`). That condition is conservative and is
documented as such: it charges one doubling to every push, where a doubling
really happens only when the block is full, so the trace law as stated covers
runs of at most 31 pushes rather than the 2^31 elements the representation
can hold. The sharper, amortized bound is not claimed.

A generic array-backed structure also exposes executable `*_at`
specializations, because Bend 2.0.16's native backend miscompiles
`Base.Array` at an open element type; `proofs/<id>/closed.bend` proves each
specialization equal to the parametric definition the laws are about, and
`END_TO_END.bend` restates that equality at the instance the tests and
benchmarks run (`deque_trace_at_is_the_trace`,
`queue_trace_at_is_the_trace`).

| structure | abstraction | invariant |
|---|---|---|
| `dynamic_array` | `Base.Array` slots → item sequence | the array realises a shadow satisfying `good` (depth <= limit <= 31, perfect tree, first `length` slots `Some` and the rest `None`) |
| `deque` | the `Some` slots of the window `[lo, lo + len)`, front first | depth <= 31, the slot tree is perfect of that depth, and the `Some` slots are exactly the window |
| `queue` | the underlying deque's window | the deque invariant (a queue shadow IS a deque shadow) |
| `doubly_linked_list` | items obtained by walking `next` from `head` | fully bidirectional links, distinct ids below `fresh`, every stored node on the walk |
| `binary_heap` | the sorted multiset of the slots `[0, size)` of one `Base.Array` block | depth <= 31, the block is a perfect tree of that depth, the elements occupy exactly the slots `[0, size)`, heap order holds over them (`slot((i-1)/2) <= slot(i)`), `size <= 2^depth` |
| `balanced_search_tree` | in-order entry list | sorted keys, **red-black invariant**, cached size = entry count |
| `bitset` | first `len` bits of the words of a native `Base.Array` | the depth is the one `depth_for` picks, the word array is a perfect tree of that depth, `len <= stored bits`, every stored bit at a position `>= len` is zero |
| `union_find` | representative of each element | three perfect `Base.Array` arenas of the depth `depth_for` picks, `n <= 2^depth`, every class exactly listed with its exact size, `count` = number of classes |
| `fenwick_tree` | the first `n` values of the tree the flat cells realise | the cell array is a perfect tree of depth d+1 (so every cell index is a representable U32), `n <= 2^d`, and every internal cell holds the exact U32 sum of its block's left half |
| `segment_tree` | first `n` values of the tree the two flat cell arrays realise (a node's tag applies to everything below it) | the sum array is a perfect tree of depth d+1 and the tag array one of depth d, `n <= 2^d`, and every node stores the exact sum of its subtree |
| `prefix_trie` | preorder enumeration, keys rebuilt character by character | every sibling list strictly increasing by code |
| `graph` | spec adjacency list of the vertex window `[lo, hi)` (vertex → key-sorted neighbour list) | perfect slot and block trees, ascending vertex ids, well-formed adjacency blocks, and spec well-formedness of the model |
| `lru` (indexed, `src/lru/fast.bend`) | capacity, lifetime, entries in recency order with deadlines, five 64-bit counters (`spec/lru_fast.bend`) | perfect arenas of depth <= 31, the ghost order and free list partition the slots below `fresh <= 2^depth`, prev/next links agree with the order, the free chain with the free list, every ordered slot occupied and mapped to by the table, the table's keys exactly the order's, crit-bit shape of the table, length <= capacity |

Comparator-parameterised structures (`binary_heap`, `balanced_search_tree`)
state their laws as templates over `~cmp` with the total-order laws
`O.Order(~K, ~cmp)` and instantiate them — and therefore check them — at both
instances `src/` exposes: `(U32, U32.cmp)` and `(String, String.order)`.

## balanced_search_tree: the red-black proof

`src/balanced_search_tree.bend` is an actual **red-black binary search tree**:
`type Tree = Leaf | Node{color, l, e, r}`, Okasaki insertion with the four
rotation cases, and the conventional functional deletion fixup (`TD`/`UF`,
`fix_left`/`fix_right`, `split_min`). `proofs/balanced_search_tree/tree.bend`
proves, generically in the comparator and instantiated at U32 and String:

| property | where |
|---|---|
| BST ordering (the in-order key list is strictly increasing) | `steps.bend` `inv`, via `SO.sorted` and `SP.sorted_ins` / `SP.sorted_del` |
| finite-map refinement of **every** inventoried operation | `steps.bend` `step_ok`, using `tree.bend` `insert_io` / `remove_io` and `query.bend` `find_ok` / `min_ok` / `max_ok` / `lb_ok` / `range_ok` / `entries_ok` |
| black root | `bal_root_black` (`bal t = and(not(is_red t), ok t)`) |
| black empty leaves | `leaf_black` (`is_red Leaf = False` by definition) |
| no red-red parent/child edge anywhere | `nrr_all` + `ok_nrr` |
| the same number of black nodes on **every** root-to-leaf path | `paths` (one entry per root-to-leaf path) + `all_eq` + `ok_paths` |
| initialisation establishes all of it | `new_bal` |
| insertion preserves it (incl. `balance` and all four rotations) | `balance_okl` / `balance_okr` → `ins_ok` → `insert_bal` |
| deletion preserves it (incl. the whole fixup path) | `fl_b3_ok` … `fix_left_ok`, `fr_b3_ok` … `fix_right_ok`, `rm_leaf_ok`, `rm_left_leaf_ok`, `split_min_ok`, `del_here_ok`, `del_ok` → `remove_bal` |
| arbitrary finite reachable traces | `trace.bend` `trace_from` / `inv_from`, exposed as `u32_trace` / `string_trace` |

All of these are restated as named laws in `END_TO_END.bend` at **both**
instances (`balanced_search_tree_u32_*`, `balanced_search_tree_string_*`).

The deletion proof is the CLRS fixup made explicit: `DelOK`/`FixOK` carry four
facts — the black height the parent should see (`dbh`), `ok` of the returned
tree, "a result that replaces a black subtree is never red", and "a fixup
under a red parent never propagates a deficiency". The impossible branches
(`fl_u` with an empty sibling, `fl_red` with an empty inner child, `dh_pick`
with `SMNone` under a non-empty right subtree) are discharged as `Empty`, not
assumed away.

The replaced 2-3 tree implementation and its proofs are archived verbatim in
`docs/archive/` for provenance.

## graph: well-formedness

`spec/graph.bend` defines the model-level well-formedness predicate `wf`:

* **closure** - every neighbour of every vertex is itself a vertex
  (`closed` / `all_vertices`), so every stored edge has both endpoints in the
  vertex set;
* **self-loop policy** - no vertex is one of its own neighbours (`loopfree`);
* **undirected symmetry** - an undirected model stores every edge at both
  endpoints (`symmetric` / `sym_set`).

**Status: PROVED.** `proofs/graph/wf.bend` establishes `wf(new d)`;
`proofs/graph/wfops.bend` `wf_step` proves that **every** spec operation
preserves it (`AddVertex`, `RemoveVertex`, `AddEdge`, `RemoveEdge` and the
five observation-only operations), and `proofs/graph.bend` `step_wf` connects
it to the runtime: for any graph satisfying the runtime invariant
`ST.inv`, the model of the state after any operation is well formed. Both are
exposed in `END_TO_END.bend` as `graph_step_well_formed` and
`graph_new_abs_well_formed`.

`RemoveEdge` genuinely needs the sortedness half of the runtime invariant:
without it the symmetry statement is false, not merely unproved (two entries
for the same vertex would let `sdel` remove only the first).

## union_find: three parallel arenas

`src/union_find.bend` keeps the roots, the class sizes and the class member
lists in three separate native `Base.Array`s of the same depth, indexed by
element. Narrow arenas are deliberate: a measured 3-field record read out of
an array cost 6.5 ns against 1.5 ns for a 1-field read, so `find` — one
indexed read of the roots arena — must not have to look at the other two.
Every law is in the same shadow style, over `Sh{n, depth, tr, tz, tm, count}`.

| step | where |
|---|---|
| the proof-level `Cell` and the **zip** of the three slot lists into one cell list | `proofs/union_find/cells.bend` |
| the partition mathematics: roots, classes, sizes, `labs`, `cnt_fix` | `proofs/union_find/model.bend` |
| merging two classes = the spec relabelling (`good2`, `labs_relabel`, `fix_count`) | `proofs/union_find/union.bend` |
| `Base.Array` get/set, `relink`, and the update of a slot against the slot lists | `proofs/union_find/arr.bend` |
| the zip commutes with a relink (`cells(rlr(...)) == rl(cells(...))`) | `proofs/union_find/bridge.bend` |
| the depth `depth_for` picks is below 32 | `proofs/union_find/depth.bend` |
| abstraction, invariant, shadow, `real_inj` | `proofs/union_find/state.bend` |
| every operation, including every OutOfRange case | `proofs/union_find/steps.bend` |
| the constructor's arenas (`iota_arr`, `Array.new`, `solo_arr`) | `proofs/union_find/init.bend` |
| arbitrary finite traces | `proofs/union_find/trace.bend` |

`spec/union_find.bend` and the two largest proof files (`model.bend`,
`union.bend`) are unchanged from the vector-of-cells version: the migration
replaced the bridge to the representation, not the mathematics.

**Capacity.** The arenas' depth is capped at 31 (2^31 slots), so every slot
index is a representable U32. The laws about `new(n)` carry the explicit
premise that `n` fits that capacity (`proofs/union_find.bend` `capacity`);
`step_ok` and the trace law from any invariant-satisfying state are
unconditional, and the invariant implies the premise.

## bitset: the packed array representation

`src/bitset.bend` stores its words in a native `Base.Array`, which is a
**linear** fixed-capacity array with O(1) indexed read and write. Every law is
therefore stated in the shadow style `proofs/dynamic_array` uses: about
`ST.real(sh)`, the array built from a Data mirror tree.

| step | where |
|---|---|
| `i / 32` and `i % 32` peel 32 bits at a time (from Base's own `Nat.divmod.go`) | `proofs/bitset/index.bend` |
| the word walks of the list model are one indexed access | `proofs/bitset/walk.bend` |
| `Base.Array` get/set against the slot list | `proofs/bitset/arr.bend` (on `proofs/lib/array.bend`) |
| the whole-array loops (`count`, `to_list`) equal the list folds | `proofs/bitset/loops.bend` |
| the word-wise combine loop equals `zip_words` | `proofs/bitset/zip.bend` |
| the depth `depth_for` picks is below 32 | `proofs/bitset/depth.bend` |
| abstraction, invariant, shadow, the all-zero array | `proofs/bitset/state.bend` |
| every operation, `from_bools` | `proofs/bitset/steps.bend` |
| arbitrary finite traces | `proofs/bitset/trace.bend` |

The independent bit-sequence specification (`spec/bitset.bend`) and all of the
Boolean-sequence mathematics (`proofs/bitset/lists.bend`, `word.bend`) are
unchanged from the list-backed version; `proofs/bitset/model.bend` keeps the
old word-list walks as the *proof model* that the array operations are shown
to implement.

**Capacity.** The word array depth is capped at 31 (2^31 words = 2^36 bits),
so every word index is a representable U32 and Base's index masking is the
identity. The laws about `new(n)` therefore carry the explicit premise that n
fits that capacity; every other law, including `step_ok` and the trace law
from any invariant-satisfying state, is unconditional, and the invariant
implies the premise (`ST.rep_fits`). This is a real, documented narrowing
compared with the earlier list-of-words representation, which had no capacity
bound: it is the price of O(1) indexed access, and it is the same bound the C
reference has.

## fenwick_tree and segment_tree: the flat split-point layout

Both store their cells in native `Base.Array`s (one for `fenwick_tree`; a sum
array and a lazy-tag array for `segment_tree`) in the layout described in
`docs/ARCHITECTURE.md`: the value at index `t` is cell `2^d + t`, and the
block `[o, o + 2^p)` with `p >= 1` keeps its total (and its tag) at its split
point `o + 2^(p-1)`.

| step | where |
|---|---|
| the interval arithmetic of the layout (which cells a block can occupy, and that sibling blocks are disjoint) | `proofs/lib/flat.bend` |
| the tree the flat cells realise, the frame lemmas, and that each index walk of the source IS the model's tree walk | `proofs/fenwick_tree/walk.bend`, `proofs/segment_tree/walk.bend` |
| the model itself, unchanged from the tree-shaped implementation | `proofs/fenwick_tree/model.bend`, `proofs/segment_tree/node.bend` + `model.bend` + `ops.bend` |
| `Base.Array` get/set/swap against the cell list | `proofs/<id>/arr.bend` (on `proofs/lib/array.bend`) |
| abstraction, invariant, shadow, `real_inj` | `proofs/<id>/state.bend` |
| every operation, including every error path | `proofs/<id>/steps.bend` |
| the constructors (`new`, `from_list`) | `proofs/<id>/init.bend` |
| arbitrary finite traces | `proofs/<id>/trace.bend` |

The point of the split-point layout is provability: the cells a block can
occupy are exactly `o+1 .. o+2^p-1`, so the frame lemmas ("this write does not
disturb that block") are interval arithmetic rather than a descendant
predicate over a heap-shaped layout.

## deque and queue: the window layout

`src/deque.bend` keeps the elements in the window `[lo, lo + len)` of a block
of `2^depth` slots. `proofs/deque/layout.bend` defines `win(xs, lo, n)` on the
slot list and reduces every window lemma at offset `lo` to the dynamic array's
lemmas at offset 0, so the two share their `somes`/`lay` mathematics.

| step | where |
|---|---|
| the window predicate and every end operation on it (push/pop at both ends, growth at both ends) | `proofs/deque/layout.bend` |
| the indexed read walk of `to_list` | `proofs/deque/walk.bend` |
| abstraction, invariant, shadow, `real_inj` | `proofs/deque/state.bend` |
| every operation, with the capacity premise for pushes | `proofs/deque/steps.bend` |
| the constructor | `proofs/deque/init.bend` |
| arbitrary finite traces, with one capacity premise for the whole list | `proofs/deque/trace.bend` |
| the executable `*_at` specializations compute the same thing | `proofs/deque/closed.bend` |

`queue` adds no new mathematics: `proofs/queue/steps.bend` maps each queue
operation to the corresponding deque operation (`dop`), maps the observation
(`qobs`, which is where `EmptyDeque` becomes `EmptyQueue`), proves the FIFO
spec step is the deque spec step of that operation (`qspec`), and derives the
queue's `step_ok` from the deque's.

## binary_heap: the packed array heap

`src/binary_heap.bend` keeps the elements in slots `[0, size)` of one
`Base.Array` block of `2^depth` slots: element `i` has children `2i+1` and
`2i+2` and parent `(i - 1) / 2`, and no node or link is allocated per
element. The shape of the heap IS its index arithmetic, so that is what the
proofs are about.

Two facts make the development possible at all. First, the block is linear,
so -- exactly as for `dynamic_array`, `bitset` and `deque` -- every law is
stated about the heap BUILT from a Data mirror tree (`ST.real` of a shadow
`Sh{size, depth, tree}`). Second, the implementation does its index
arithmetic in `U32` (a unary `Nat` index would make a sift loop cost the
index instead of its logarithm), so each loop step is bridged to the `Nat`
arithmetic the proofs use. The bridges never name `2^32`: they are stated
with a variable bound `k <= 32`, because a literal `2^32` would make the
checker expand a unary `Nat` of four billion successors.

| step | where |
|---|---|
| heap index arithmetic (`kidl`, `kidr`, `par`, halving, the `scale` fuel measure) | `proofs/binary_heap/idx.bend` |
| the `U32` bridges for `inc`, `shl`, `shr`, `sub`, `<`, `==` and for the parent index | `proofs/binary_heap/u32idx.bend` |
| slots, heap order (`pair_ok`, `ho_upto`), layout (`lay`), and the two "all pairs except..." forms a sift carries (`ho_exc`, `ho_exc2`) | `proofs/binary_heap/slots.bend` |
| the multiset of a block (`vals`, `msort`) and the one-slot replacement law `ins_set` | `proofs/binary_heap/vals.bend` |
| a slot swap is invisible to the sorted multiset (`vals_swap`) | `proofs/binary_heap/bag.bend` |
| the root is the minimum, the multiset has one element per occupied slot, `head_root` | `proofs/binary_heap/root.bend` |
| sift-up: the loop invariant, every step, and `sift_up_ok` | `proofs/binary_heap/up.bend` |
| sift-down: the loop invariant (the two pairs below the hole excluded), every step, and `sift_down_ok` | `proofs/binary_heap/down.bend` |
| doubling the block changes nothing but the capacity | `proofs/binary_heap/grow.bend` |
| shadow, abstraction, invariant, the constructor | `proofs/binary_heap/state.bend` |
| `push` (with and without a doubling) | `proofs/binary_heap/push.bend` |
| `pop` (swap out the last element, sift it down from the root) | `proofs/binary_heap/pop.bend` |
| `to_sorted_list` (drain a clone; every iteration is the pop of the clone) | `proofs/binary_heap/sorted.bend` |
| every operation, with the capacity premise for `push`/`from_list` | `proofs/binary_heap/steps.bend` |
| arbitrary finite traces, with one capacity premise for the whole list | `proofs/binary_heap/trace.bend` |

The sift laws are the heart of it. A sift-up carries, over the logical block
`update(slots, i, Some x)` with the hole at `i`: every pair except the one
into `i` holds (`ho_exc`), the parent of `i` is below both children of `i`
(`kids_le`), the layout is intact, and the sorted multiset is the target --
and it concludes that the loop lands on a block that is heap-ordered over
`[0, n)`, keeps the layout and has exactly that multiset. A sift-down carries
the same shape with the two pairs whose parent is the hole excluded
(`ho_exc2`) plus the pair above the hole, and its fuel bound is
`n <= scale(fuel, 1 + i)` (the hole index at least doubles every step), which
avoids `Nat.mul` entirely.

A wrap-around bug was found by these proofs and fixed in the source: the
"has a right child" test must be `l < size - 1`, not `l + 1 < size`, because
the latter wraps at 2^31 slots.

## Retained LRU

`proofs/lru.bend` pulls the retained cache's own end-to-end theorems into the
`PROOF.bend` closure and restates the public trace law for the reuse entry
`src/lru.bend`. Nothing in `reference/lru` is modified; `automation/
acceptance.py` re-verifies every file's sha256 against
`inventory/reference-sha256.json`. The retained cache cannot be compiled to a
native binary with this toolchain (its Word(64n) metrics exceed the native
arity limit; `tests/runtime_defects/wide_arity.bend`), so it is validated in
`bend` run mode.

## Indexed LRU (`src/lru/fast.bend`, the benchmarked cache)

The operator's scope correction (`docs/OPERATOR_LRU_SCOPE_CORRECTION.md`) puts
the natively compiled cache in scope. It is proven against its own independent
model `spec/lru_fast.bend` (entries in recency order with deadlines, the five
counters as 64-bit words; expiry and deadlines by the retained numeric
semantics, ported under `spec/lru_numeric.bend` and `proofs/lru_fast/num/`):

* `state.bend`: shadow, abstraction `model`, invariant `inv` / `good`, and the
  constructor (`init(cap)` is `real(initial cap)`, whose model is the spec's
  empty cache; `new` accepts and rejects exactly the capacities spec `new`
  does, laws `lru_fast_*_new_*`).
* The operation cores, each proven for the runtime result, the invariant and
  the model: slot removal `rs.bend`; `remove.bend`; touch `touch.bend` /
  `touch2.bend`; reads (get / peek / contains, including expiry) `read.bend`;
  add (replace, and insert from the free list, a fresh slot, or after growing
  every arena; eviction of the oldest when full) `add.bend`, `insert.bend`,
  `addop.bend`; purge / metrics / len / capacity / set_lifetime `simple.bend`;
  resize (a shrink loop with its own ghost; the invariant is carried at the old
  capacity while the loop runs) `resize.bend`; keys (the expired-prefix loop
  and the backward key walk) `keys.bend`, `kwalk.bend`.
* `steps.bend` / `trace.bend`: `step_ok` for every operation of
  `types/lru_fast.bend`, and traces of arbitrary length from the constructor.
  The premise is the capacity condition: every capacity the cache takes
  (initial and every Resize argument) is within `2^q`, `q <= 31`. The arrays
  only grow while the cache holds fewer entries than its capacity, so they stay
  below `2^31` slots (`capstep.bend` proves each spec step keeps the bound).
  **This premise is narrower than the public API.** `new` accepts every
  capacity in `1 .. 4294967294` and `resize` every positive `U32` (pinned by
  `tests/lru_fast/capacity_contract.bend`, wired into `tools/validate.py`);
  capacities above `2^31` are therefore an OPEN, documented proof gap, not an
  API limit, and narrowing the API to close it was explicitly rejected by the
  operator (`docs/OPERATOR_KEEP_CAPACITY_API.md`). `Base.Array` itself indexes
  correctly only below depth 32, so covering them needs a two-block arena.
* The laws are stated at V = U32 and V = String (`END_TO_END.bend`);
  `inst_*.bend` instantiate every template at U32 for fast local checks.
* `inj.bend` `real_inj` (law `lru_fast_*_shadow_unique`): a good shadow is
  determined by the cache it builds. The arrays come back by thaw/freeze, the
  lifetime by the Stamp round trip, the ghost recency order by walking the next
  links from the head, and the ghost free list by walking the free chain. So,
  as for the seven structures with `*_shadow_unique`, the shadow-form laws pin
  the abstract state.
* Runtime evidence: `tests/lru_fast/spec_diff.bend` runs the runtime against the spec on
  six seeded 300-operation traces (0 mismatches), next to the existing
  differential against the retained cache (`tests/lru_fast/main.bend`) and the
  native C differential (`tools/lru_diff.py`). All three are in `tools/validate.py`.

## Not proved / out of scope

* Asymptotic costs are documented in the source headers but are not machine
  checked; nothing in the proof closure depends on them.
* Performance is a separate, measured claim: see `BENCHMARKS.md`. It is **not**
  met. In the final 0008 run of the frozen table
  (`build/performance/report.json`, rendered into BENCHMARKS.md) 245 of 408
  workloads are within 2.5x, 160 are over, and 3 were not measurable above the
  clock minima. The frozen gate has no
  `lru.*` rows. The indexed LRU has a native C reference (`benchmarks/native/lru.c`)
  and a Bend driver; the rows are proposed additively in
  `docs/BENCHMARK_CHANGE_PROPOSAL.md`. The proofs are unaffected.

  `bitset` moved in an earlier iteration (median 1.24x at the time, 25 of its
  44 rows within the limit then), after its words were moved from a cons list to a
  native `Base.Array` (the list made `get`/`set` O(words) against an O(1) C
  reference, which was not the same algorithm). `BENCHMARKS.md` opens with the
  measured cost model that says which of the remaining structures can be
  brought within the limit the same way and which need a different
  representation entirely.
