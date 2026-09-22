# Work-in-progress snapshot: two-list queue/deque

The user supplied `deque_queue.bend` and requested replacing the DLL approach. Both public Bend implementations now use ordinary singly linked lists; C implements the same FIFO reversal / deque half-split algorithms. The standalone DLL is retired from the active inventory and archived with its historical work.

Validation: 94 independent-oracle histories (39,858 operations), 10 compiled semantic mutants detected, 100,000 randomized C operations per mode under ASan/UBSan, and 240 benchmark checksum compatibility cases. Final calibrated benchmark: 60/60 checksums agree; 58/60 rows meet 2.5x C. Empty `to_list` fails at 3.813x (deque) and 3.282x (queue).

`TWO_LIST_COMPONENT_PROOF.bend` passes for U32/String. It is not full acceptance: arbitrary-trace refinement, cached-count/rebalance invariants and cost proofs remain unfinished. `PROOF.bend` fails on the obsolete ring proof representation. Earlier full-proof/performance statements in historical documents do not establish current acceptance. Owning-Type expansion is also not completed by this change.

The worker remains stopped. See `docs/TWO_LIST_MIGRATION.md` and `benchmarks/evidence/operator-two-list-20260922/` for commands, exact evidence and limitations. Historical recovery evidence is preserved.
