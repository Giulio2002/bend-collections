# Private work-in-progress snapshot

The production balanced search tree is now an indexed red-black TreeMap using
Data keys/values and the shared dynamic array. It includes comparator-based
ordering, replacement/conditional edits, navigation/polling, editable owning
iterators, and backed bounded/descending views.

- 92,544 operations over 300 histories pass, with independent red-black,
  parent-link, ordering, cached-state and exhaustive live/free-slot checks.
- Capacity rejection/reuse and String keys with custom Data records pass.
- 16 explicit component laws pass; three compiled semantic mutants are rejected
  by both the tests and the component proof gate.
- Existing Data dynamic-array proof and retained legacy recursive-tree proof
  pass. The latter applies only to the code in `reference/`.
- Full indexed-map refinement, balancing, arbitrary iterator/view trace proofs
  are unfinished. The global proof root still fails at the existing deque
  constructor-pattern migration; the exact failure is archived.
- Native C benchmark sweep: 23/33 rows within 2.5x, 10 slow, none unresolved.
  Remaining performance failures: range/iteration, small-tree remove/reinsert,
  and construction. C reference source unchanged. Source hashes, checksums,
  samples and initial noisy sweep retained in the evidence directory.
- The actual map constructor is timed, including its two initial buffers; the
  final benchmark does not replace construction with a literal zero result.

No FFI, compiler modification, or patched generated C. DSA auto-implementer
remains stopped. This snapshot is not a whole-library completion or acceptance
claim. See `docs/TREE_MAP.md` and `benchmarks/evidence/tree-map-20260922/`.

Latest: reduced range/iteration overhead; see benchmarks/evidence/tree-range-20260922/README.md. Complete indexed proofs and performance acceptance remain open.
