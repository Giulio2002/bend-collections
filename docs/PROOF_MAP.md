> Current TreeMap migration (2026-09-22): the production balanced-search-tree
> module is now the indexed Data-key/Data-value TreeMap. Its 16 checked
> component laws are in `TREE_MAP_COMPONENT_PROOF.bend`; full indexed
> refinement/invariant/trace proofs remain incomplete. Every recursive-tree
> proof described below applies to `reference/legacy_balanced_search_tree.bend`,
> not to the new implementation. See `docs/TREE_MAP.md` (or `TREE_MAP.md`
> from this directory). No whole-library correctness claim is made.

# Proof map: public operation -> specification -> theorem -> tests

**Current status:** the whole-library gate is incomplete. The table below maps
proof source locations; it does not assert that those sources currently check
against every migrated implementation. Queue/deque and generational DLL trace
bridges remain unfinished.

The owning iterator's `ITERATOR_COMPONENT_PROOF.bend` gate checks U32/String
component laws and end-gap insertion equivalence with public append. It is
imported by `PROOF.bend`, but does not establish full cursor-invariant
preservation or arbitrary trace refinement. See [iterator proof scope](DLIST_ITERATOR.md).

| structure | spec model (`spec/<id>.bend`) | per-operation theorem | trace theorem | public laws in `END_TO_END.bend` | tests |
|---|---|---|---|---|---|
| `dynamic_array` | item sequence + capacity | `proofs/dynamic_array/steps.bend` `step_ok` | `trace_new`, `trace_with_limit` | `dynamic_array_*` | `tests/dynamic_array/` |
| `deque` | item sequence | `proofs/deque/steps.bend` `step_ok` (shadow form: the slot array is linear) | `proofs/deque/trace.bend` `trace_from`, exposed as `deque_trace` | `deque_*` | `tests/deque/` |
| `queue` | item sequence (FIFO) | `proofs/queue/steps.bend` `step_ok` (each step is the deque's step of the corresponding deque operation) | `proofs/queue/trace.bend` `trace_from`, exposed as `queue_trace` | `queue_*` | `tests/queue/` |
| `doubly_linked_list` | item sequence + handles | `proofs/dlist/trace.bend` `step_ok` (shadow form over the three parallel arenas; template, instantiated at U32 and String) | `trace_new`, `trace_from` | `doubly_linked_list_u32_*`, `doubly_linked_list_string_*` | `tests/doubly_linked_list/` |
| `binary_heap` | sorted multiset | `proofs/binary_heap/…` `step_ok` (template, instantiated at U32 and String) | `trace_new` | `binary_heap_u32_*`, `binary_heap_string_*` | `tests/binary_heap/` |
| `balanced_search_tree` | key-sorted entry list (finite map) | `proofs/balanced_search_tree/steps.bend` `step_ok` (template, instantiated at U32 and String) | `trace_from`, `inv_from` | `balanced_search_tree_u32_*`, `balanced_search_tree_string_*` | `tests/balanced_search_tree/` incl. the `rb32`/`rbstr` structural kinds |
| `bitset` | bit list | `proofs/bitset/steps.bend` `step_ok` (shadow form: the word array is linear) | `proofs/bitset/trace.bend` `trace_from`, exposed as `bitset_trace` | `bitset_*` | `tests/bitset/` |
| retained `lru` | `reference/lru/spec` | the retained cache's own theorems, re-checked under 2.0.16 | `lru_entry_string_trace` | `lru_entry_string_trace` | `tests/lru/` (run mode) |
| indexed `lru` (`src/lru/fast.bend`) | `spec/lru_fast.bend`: recency-ordered entries with deadlines + five 64-bit counters | `proofs/lru_fast/trace.bend` `step_ok` (every `types/lru_fast.bend` operation; shadow form; template, instantiated at U32 and String) | `trace_new`, `trace_from` (capacity condition: every capacity within 2^q, q <= 31) | `lru_fast_u32_*`, `lru_fast_string_*` | `tests/lru_fast/main.bend` (vs the retained cache), `tests/lru_fast/spec_diff.bend` (vs the spec), `tools/lru_diff.py` (vs C) |

`step_ok` always has the shape

```
StepOK(s, op) :=  { view(step(s, op)) == spec_step(abs(s), op) }
               &  { inv(fst(step(s, op))) == True }
```

for *every* `s` with `inv(s) == True` — every error path included — and the
trace theorem composes it over an arbitrary finite list of operations from the
real constructor.

For the array-backed structures the same shape is stated in *shadow* form,
because `Base.Array` is linear and cannot appear twice in a proof term: the
law is about `real(sh)`, the structure whose array is built from a Data mirror
tree, and it *names the shadow the operation lands on*
(`Sigma<Shadow, sh2 => step(real(sh), op) == (real(sh2), o) & good(sh2) & …>`).
`shadow_unique` (`real(a) == real(b) -> a == b`) is proved for each of them,
so naming the shadow pins the abstract state. Where a structure grows its
array, the law carries the representation's capacity condition as an explicit
premise (for the deque and the queue: `depth + (number of pushes) <= 31`,
i.e. at most 2^31 slots), never a hidden bound.

## balanced_search_tree: the red-black properties

| property | theorem | law in `END_TO_END.bend` |
|---|---|---|
| black root | `tree.bend` `bal_root_black` | `balanced_search_tree_{u32,string}_root_black` |
| black empty leaves | `tree.bend` `leaf_black` | `balanced_search_tree_{u32,string}_leaf_black` |
| no red-red parent/child edge | `tree.bend` `nrr_all` / `ok_nrr` | `balanced_search_tree_{u32,string}_no_red_red` |
| equal black height on every root-to-leaf path | `tree.bend` `paths` / `all_eq` / `ok_paths` | `balanced_search_tree_{u32,string}_uniform_black_height` |
| the empty tree satisfies all of it | `tree.bend` `new_bal` | `balanced_search_tree_{u32,string}_new_balanced` |
| insertion preserves it | `tree.bend` `ins_ok` / `insert_bal` | `balanced_search_tree_{u32,string}_insert_balanced` |
| deletion preserves it | `tree.bend` `del_ok` / `remove_bal` | `balanced_search_tree_{u32,string}_remove_balanced` |
| BST ordering | `steps.bend` `inv` (`SO.sorted` of the in-order list) | inside `…_step` and `…_trace_invariant` |
| finite-map refinement of each operation | `steps.bend` `step_ok` | `balanced_search_tree_{u32,string}_step` |
| arbitrary finite traces | `trace.bend` `trace_from` / `inv_from` | `balanced_search_tree_{u32,string}_trace(_invariant)` |

The same properties are re-derived at runtime, after every operation, by the
`rb32`/`rbstr` kinds of `tests/balanced_search_tree/main.bend`, so a proof that
did not match the compiled code would be caught by the test suite as well.

## graph: model well-formedness

| property | status |
|---|---|
| `wf` defined (endpoint closure, self-loop policy, undirected symmetry) | `spec/graph.bend` |
| finite-map laws it rests on | `proofs/graph/fmap.bend` (proved) |
| graph-level `hasv`/`nbrs`/`smem` laws under `put`/`del`/`strip`/`sadd`/`sdel` | `proofs/graph/wf.bend` (proved) |
| `wf(new d)` | `wf.bend` `wf_new`, laws `graph_new_well_formed`, `graph_new_abs_well_formed` |
| `AddVertex` preserves `wf` | `wfops.bend` `wf_add_vertex` |
| `RemoveVertex` preserves `wf` | `wfops.bend` `wf_remove_vertex` |
| `AddEdge` preserves `wf` (directed and undirected) | `wfops.bend` `wf_add_edge` |
| `RemoveEdge` preserves `wf` (directed and undirected) | `wfops.bend` `wf_remove_edge`, under the sortedness side condition |
| the five observation-only operations preserve `wf` | `wf.bend` `wf_*` |
| **every** operation at once | `wfops.bend` `wf_step` |
| connected to the runtime invariant | `proofs/graph.bend` `step_wf` discharges the sortedness side condition from `ST.inv`; public law `graph_step_well_formed` |

`RemoveEdge`'s sortedness premise is a real side condition, not a proof
convenience: `GS.put` inserts before the first greater key, so on an unsorted
list it could leave a stale duplicate entry that still claims the deleted edge.
The runtime invariant guarantees sortedness, so the public law carries no
leftover assumption.

## bitset: the packed `Base.Array` representation

| step | theorem |
|---|---|
| `i / 32` and `i % 32` peel 32 bits at a time | `proofs/bitset/index.bend` `wordix_small` / `wordix_step` / `bitix_small` / `bitix_step` |
| a word-list walk is one indexed access | `proofs/bitset/walk.bend` `get_index` / `put_index` |
| `Base.Array` get/set against the slot list | `proofs/bitset/arr.bend` `read_ok` / `write_ok` / `ws_upd` |
| `count` / `to_list` loops equal the list folds | `proofs/bitset/loops.bend` `count_ok` / `to_list_ok` |
| the word-wise combine loop equals `zip_words` | `proofs/bitset/zip.bend` `zip_go_ok` / `ztree_ws` / `zl_full` |
| the chosen depth is below 32 | `proofs/bitset/depth.bend` `depth_lt` |
| every operation, every error path | `proofs/bitset/steps.bend` `step_ok` |
| arbitrary finite traces from `new(n)` | `proofs/bitset/trace.bend` `trace_from`, law `bitset_trace` |

The laws about `new(n)` carry the explicit capacity premise
`Nat.is_le(n, 32 * 2^depth_for(n))` (2^36 bits); `step_ok` and the trace law
from any invariant-satisfying state are unconditional, and the invariant
implies the premise (`proofs/bitset/state.bend` `rep_fits`).


## graph: the proof after the representation change

`src/graph.bend` runs on indexed vertex slots plus adjacency blocks. The proof
against this representation is complete: `proofs/graph/state.bend` (shadow,
`real`, `good`, `model`), the search / shift / window / block lemmas, the nine
operation refinements, `gtrace.bend` `step_ok` and traces, exposed
as the `graph_*` laws. The archived ordered-map proofs
(`docs/archive/graph.ordmap.bend.txt`) describe the previous implementation
only. The model well-formedness development (`wf`) is a property of the spec;
`graph_step_well_formed` connects it to the runtime through `good`.

The public BLOCK enumeration `vertices_block` is proved in
`proofs/graph/vblk.bend`: `wr` is the mirror of the copy loop, `vb_go_ok`
proves the runtime loop IS that mirror, `wr_above` / `wr_top` / `wr_nth` give
the resulting slot contents, `blk_win` lifts them to the window, and
`vertices_block_ok` / `vertices_block_seq` give the whole operation on
`ST.real(sh)` and prove the block's window `[0, n)` is the SAME list
`G.vertices` returns. Public law: END_TO_END `graph_vertices_block`
(`GRVB.Built(sh)`, both facts).
