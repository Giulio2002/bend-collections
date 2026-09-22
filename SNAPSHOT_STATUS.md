# Work in progress

WIP library; DLL iterator performance passes all 33 calibrated rows at <=2.5x optimized C (worst median 1.575x). Compact owning cursors, matching C reference, 32,429 differential operations, handle recycling/retirement tests and component laws pass. Full cursor invariant/trace refinement and whole-library PROOF.bend remain incomplete. Segment tree removed. Quick screen: 119 operations, 31 slow, 4 unresolved, 40.575 seconds. DSA worker remains stopped.

See BENCHMARKS.md, docs/DLIST_ITERATOR.md and benchmarks/evidence/iterator-20260922/.
