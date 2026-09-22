# Two-list queue and deque

User-supplied design: `/Users/monkeair/Downloads/deque_queue.bend`, ported to stock Bend 2.0.16. The original uses older Bend syntax. The active library now has no standalone doubly linked list, no DLL dependency in the queue/deque, no node arrays, no handle generations, and no channel implementation. Prior DLL work is archived under `history/retired-doubly-linked-list`.

## Algorithms and API

- Queue owns `front`, reversed `back`, and a cached count. Enqueue conses onto back. Dequeue/peek reverse the whole back only if front is empty.
- Deque owns `front`, reversed `back`, and a cached count per side. When the requested side is empty, it keeps floor(n/2) nodes at the opposite end and reverses the rest into the requested end. Peek retains this rebalance in the returned state.
- Both materialize `front ++ reverse(back)`. The supplied file omitted the final reverse; this was corrected, not copied into the library.
- Existing public operations, result/error types and consumed-state API remain. Element types remain `T: Data`; this change does not complete the earlier separate request for arbitrary owning `Type` elements.
- Push/pop/peek are amortized O(1) along a consumed state history. A reversal/split is O(n); `to_list` is O(n), not O(1). Cached length avoids scanning the list. This asymptotic claim has not been formally cost-proved.
- Native Bend owns/frees ordinary list nodes. C uses malloc/free per singly linked node. C splits and reverses links in place; Bend consumes the corresponding lists. Neither implementation has retained arena slots.

## C equivalent

`benchmarks/native/two_list.h` implements both modes. `queue.c` selects FIFO full reversal; `deque.c` selects half splitting. Original benchmark selectors, RNG, counts, checksum work and calibrated measurement methodology are retained. The C reference changed only because the user explicitly requested this algorithm change. Earlier references/evidence remain historical, not current acceptance evidence.

## Reproduce validation

```
bend tests/deque/main.bend -o build/two-deque
bend tests/queue/main.bend -o build/two-queue
python3 tools/check_two_list.py
python3 tools/check_two_list_mutations.py
bend TWO_LIST_COMPONENT_PROOF.bend
clang -O1 -g -fsanitize=address,undefined tests/two_list/native.c -o build/test-two-deque-c
clang -O1 -g -fsanitize=address,undefined -DTWO_LIST_FIFO tests/two_list/native.c -o build/test-two-queue-c
build/test-two-deque-c
build/test-two-queue-c
python3 benchmarks/operator_two_list_bench.py
```

94 independent-oracle histories / 39,858 operations pass. Ten compiled semantic mutants are detected. Each C mode passes 100,000 randomized operations with ordering/count invariants and allocation balance under ASan/UBSan. 240 C/Bend benchmark input combinations have matching checksums. The deque stress keeps 262,144 live elements through 10,000,000 pop/push cycles: zero errors, checksum 762746048, peak process RSS 7,782,400 bytes on this machine. RSS is a diagnostic measurement, not a universal bound.

## Proof status — incomplete

`TWO_LIST_COMPONENT_PROOF.bend` passes with U32 and String instantiations. It checks the actual split's universal sequence reconstruction, materialization against the independent specification, push ordering, same-end push/pop round trips, FIFO normalization ordering, singleton and empty behavior. It is a component gate, not the whole-library gate. Checker warnings from imported Base/library declarations remain visible; no new unsafe annotations, axioms or holes were introduced.

**Full arbitrary-operation trace refinement, cached-count preservation through all rebalances, and amortized cost proofs are not completed.** Old ring-buffer deque/queue trace files remain incompatible with the new representation; `PROOF.bend` is not passing. Historical proof claims must not be applied to the new implementation.

## Final measured performance

60/60 rows have matching C/Bend checksums; 58/60 meet the unchanged 2.5x threshold. Empty to_list fails for deque (3.813x; 4.824 ns vs 1.265 ns) and queue (3.282x; 4.980 ns vs 1.517 ns). No threshold exemption was applied. Raw six-sample results and source verification are in `benchmarks/evidence/operator-two-list-20260922/`. These two failures and unfinished trace proofs prevent final acceptance.
