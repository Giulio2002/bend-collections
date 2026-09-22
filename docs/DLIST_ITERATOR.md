# Owning DLL iterators

`src/dlist_iterator.bend` exports a bidirectional gap cursor for the arena DLL.
It supports any `Data` element type. Create it with `iter_first(~T, list)`
(before the first element) or `iter_last(~T, list)` (after the last element).
The list moves into the iterator; `finish(~T, iterator)` returns it. Every
operation returns the updated iterator alongside its result.

| Operation | Behavior |
|---|---|
| `next` | Return the next value and move the gap forward |
| `previous` | Move the gap backward and return the preceding value |
| `has_next`, `has_previous` | Inspect whether movement is possible |
| `position` | Return the zero-based gap position |
| `set` | Replace the last value returned by successful movement |
| `add` | Insert immediately before the gap's next element; advance the gap |
| `remove` | Remove the last value returned by successful movement |
| `finish` | Return ownership of the list |

A failed movement returns `Exhausted` and preserves the cursor, including the
last returned element. `set` and `remove` return `NoCurrent` before successful
movement or after `add`/`remove`. `set` preserves that current element. Adding
at the end appends. No operation materializes the list for traversal.

The iterator stores two arena links, a direction flag, and a gap index. Links
use index-plus-one with zero as the sentinel. They are not public handles:
the affine iterator owns the list, so no independent mutation can invalidate
them. Public DLL handles still carry owners and generations. Iterator removal
uses the same generation increment, free-slot recycling, and exhausted-
generation retirement code as public removal. Retaining a handle across
`finish` does not make a removed slot valid again.

Use the constructors and operations above. The low-level `IT` representation
and cursor helpers are internal implementation details. Forging a cursor or
editing its slots manually violates its representation invariant. Bend's
exposed constructors do not themselves prove that invariant.

## Validation and remaining proof work

`ITERATOR_COMPONENT_PROOF.bend` checks ownership return, exhausted forward
movement, current-element requirements, query state preservation, successful
edit metadata, forward/backward movement metadata, and preservation of metadata
on failed movement. It also proves that insertion at the end gap equals public
DLL append, including its allocation/recycling path. U32 and String component
instantiations are checked. These are component laws, **not** a complete proof
of preservation of the arena/cursor invariant or arbitrary sequence refinement.
The whole-library `PROOF.bend` gate remains incomplete.

`tools/check_iterators.py` compares every observation and list content with an
independent Python list/gap model in both Bend and C: 102 histories and 32,429
operations. C can additionally run under ASan/UBSan. `handles.bend` checks that
recycling invalidates a removed public handle, preserves a surviving handle,
and retires a slot whose generation is UINT32_MAX.

```sh
bend ITERATOR_COMPONENT_PROOF.bend
bend tests/dlist_iterator/main.bend -o build/test-iterator
cc -O3 -std=c11 tests/dlist_iterator/native.c -o build/test-iterator-c
python3 tools/check_iterators.py
bend tests/dlist_iterator/handles.bend -o build/test-iterator-handles
build/test-iterator-handles  # prints 23 and 1 on separate lines
python3 benchmarks/bench.py --build
python3 tools/bench_iterators.py
```

## Benchmark interpretation

The native C reference uses the same owning gap cursor and arena algorithm.
It is compiled with `-O3 -march=native`; Bend uses the stock 2.0.16 native C
backend and one worker. No FFI, compiler patches, generated-C modifications,
or reference slowdowns are used.

The 11 operation labels cover sizes 64, 4096, and 65,536. Add/remove rows both
measure the restoring **add + previous + remove** sequence, with different
pinned seeds. They are not isolated mutation timings. First/last/finish include
finish/recreate cycles. Traversal cycles restart at the appropriate end.
Results and full A/B/C sample logs are in `build/iterator-performance/`.
The runner uses the existing full calibration gates: six samples alternating
region order, at least 50 ms Bend A−B difference per sample, matching checksums.
The target is a ratio of median Bend/C times of at most 2.5 on every row.

The driver specializes each operation outside its hot loop and shares the
movement call after selecting an end-reset cursor. This retains the exact
public calls and checksum stream while avoiding runtime operation dispatch and
large duplicated branches. Library improvements use compact cursors, fused
value/link reads, small metadata branches, and a common insertion-at-gap path.
