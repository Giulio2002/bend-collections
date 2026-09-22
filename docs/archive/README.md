# Archive: replaced implementations, kept verbatim for provenance

Nothing in this directory is read by the build, the proof closure, the tests
or the benchmarks. Each file is a runtime (or a proof about a runtime) that a
later requirement replaced; they are kept so that each replacement is
auditable rather than merely asserted.

| file | was | replaced by | why |
|---|---|---|---|
| `balanced_search_tree.two_three.bend.txt`, `proofs_tree.two_three.bend.txt`, `proofs_query.two_three.bend.txt` | the 2-3 tree ordered map and its proofs | an actual red-black binary tree | the requirement named red-black explicitly |
| `bitset.word_list.bend.txt`, `proofs_bitset*.word_list.bend.txt` | packed words in a cons list | packed words in a native `Base.Array` | O(words) indexed access against C's O(1) |
| `deque.two_lists.bend.txt`, `proofs_deque*.two_lists.bend.txt` | the banker's deque (two retained cons lists) | a window `[lo, lo+len)` of a `Base.Array` block | every end operation is now one indexed access instead of a retained `&2` list step (~8.6x C per step) |
| `fenwick_tree.node_tree.bend.txt`, `proofs_fenwick_*.node_tree.bend.txt` | the Fenwick partial sums in an explicit node tree | one flat `Base.Array` in the split-point layout | same reason; the node tree survives verbatim as the *proof model* in `proofs/fenwick_tree/model.bend` |
| `segment_tree.node_tree.bend.txt`, `proofs_segment_*.node_tree.bend.txt` | sums and lazy tags in an explicit node tree | two flat `Base.Array`s in the split-point layout | same reason; the node tree survives verbatim as the *proof model* in `proofs/segment_tree/node.bend` |
| `dynamic_array.clone_flatten_to_list.bend.txt` | `to_list` cloning the whole array and walking it structurally | the indexed read walk both `dynamic_array` and `deque` now use | a structural `ALeaf`/`ANode` walk costs ~15 ns per slot and the clone was an extra O(capacity) copy C never pays |

The `queue` is not listed separately: it has always been the back-in/front-out
specialization of the deque, and it followed the deque's representation.

## The replaced 2-3 tree `balanced_search_tree`

Before the red-black requirement, `balanced_search_tree` was implemented and
fully proved as a **2-3 tree** (`Leaf | Node2{l, e, r} | Node3{l, e1, m, e2, r}`,
all leaves at the same depth, insertion splitting an overflowing node upwards,
deletion repairing an underflow by borrowing from or merging with a sibling).
That work satisfied the same public ordered-map API, the same comparator
parameterisation and the same error semantics, and its proofs checked.

The user requirement changed to "the balanced search tree must be an actual
red-black BINARY search tree", and explicitly ruled out a renamed 2-3 tree or a
conversion facade with the old tree as the operational storage. The 2-3 runtime
and its proofs were therefore *replaced*, not wrapped. These files are kept
verbatim so the replacement is auditable — nothing in the build, the proof
closure or the benchmarks reads them.

| file | was |
|---|---|
| `balanced_search_tree.two_three.bend.txt` | `src/balanced_search_tree.bend` |
| `proofs_tree.two_three.bend.txt` | `proofs/balanced_search_tree/tree.bend` |
| `proofs_query.two_three.bend.txt` | `proofs/balanced_search_tree/query.bend` |

What carried over unchanged (so the replacement did not restart proven
mathematics):

* `types/balanced_search_tree.bend` and `spec/balanced_search_tree.bend` — the
  public types and the independent finite-map model never mentioned the tree;
* `proofs/balanced_search_tree/sorted.bend` and `specops.bend` — all of the
  spec-level sortedness and finite-map lemmas;
* `proofs/balanced_search_tree/steps.bend` and `trace.bend` — the abstraction,
  the invariant, `step_ok` and the trace composition needed only the four call
  sites that passed the 2-3 tree's second comparison (`c2`/`d2`) to be updated,
  because the invariant is stated as "sorted in-order list, balanced, exact
  size" and `bal` simply changed meaning from "all leaves at one depth" to the
  red-black invariant.

The C reference was replaced in the same way: `native_bench/twothree.h` was
deleted and `native_bench/redblack.h` implements the same red-black algorithm
that `src/balanced_search_tree.bend` does. `src/graph.bend` and
`proofs/graph/model.bend`, which reuse the ordered map, were ported to the
binary node shape at the same time.

# Archive: the replaced list-of-words `bitset`

Before the `Base.Array` migration, `src/bitset.bend` kept its packed words in
a `List<&2, U32>`. That made `get`, `set` and `clear` O(words) while the C
reference is O(1) on a flat array — not the same algorithm, and the reason
those rows were the worst in the whole benchmark suite (`bitset.set` at size
4096 was **2243x** the reference). The word array is now a native
`Base.Array`, which the measured cost model at the top of `BENCHMARKS.md`
shows is the only Bend primitive that is competitive with C.

| file | was |
|---|---|
| `bitset.word_list.bend.txt` | `src/bitset.bend` |
| `proofs_bitset.word_list.bend.txt` | `proofs/bitset.bend` |
| `proofs_bitset_state.word_list.bend.txt` | `proofs/bitset/state.bend` |
| `proofs_bitset_steps.word_list.bend.txt` | `proofs/bitset/steps.bend` |
| `proofs_bitset_trace.word_list.bend.txt` | `proofs/bitset/trace.bend` |

What carried over unchanged, so the replacement did not restart proven
mathematics:

* `types/bitset.bend` and `spec/bitset.bend` — the public types and the
  independent bit-sequence model never mentioned the representation;
* `proofs/bitset/lists.bend` and `word.bend` — all of the Boolean-sequence and
  U32 word mathematics;
* the word-list walks of the old implementation, kept verbatim as
  `proofs/bitset/model.bend`: they are now the *proof model* that the array
  operations are shown to implement, so every lemma of the old
  `state.bend` about them is retained rather than re-derived.

What the replacement cost: the packed array has a capacity (2^31 words = 2^36
bits, so that every word index is a representable U32), so the laws about
`new(n)` now carry an explicit premise that `n` fits it. The list version had
no capacity bound. `step_ok` and the trace law from any invariant-satisfying
state remain unconditional.

