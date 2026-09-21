# Independent bend-dsa completion audit

Read the frozen objective, inventory and installed-Base audit. Inspect every actual public API, independent spec, theorem statement, dependency, instance and runtime test. Audit all twelve structures and the reused LRU compatibility; do not approve partial work. No empty/finite-only/vacuous/circular specs, extra hidden bounds, assumed high-level Map/Array correctness, unsafe escapes, or missing error behavior. Prove arbitrary finite traces from constructors. Static generic templates require checked real instantiations.

Check data-structure invariants: dynamic-array bounds/growth, DLL handle ownership and bidirectional links, FIFO/deque order, heap multiplicity and priority, search ordering/balance, bitset tail masks, DSU equivalence classes and sizes, graph endpoint/symmetry rules, prefix trie enumeration, Fenwick sums, lazy-segment updates. Compare independent models, legal domains and numeric overflow rules to documented APIs. Complexity claims must match Bend's actual representation; no O(1) array/Map folklore.

Trace tools/validate.py report claims to executable independent tests and semantic mutants. Ensure expected answers never enter the tested Bend backend. Read checker logs, source fingerprints and proof closure. Frozen acceptance performs minimum mechanical checks; report booleans and theorem-name presence are not semantic evidence. Worker and orchestrator self-audit never replace this independent audit. Note unperformed checks and preserve honest partial status. Approve only with no substantive remaining finding. Review only; no edits, commits, pushes, delegation, or scope waivers.


## Native performance release contract — latest user requirement

This extends the existing whole objective; all implementation, proofs, conformance,
mutation and audit requirements remain. Preserve the seeded work and session.
First accepted versions MUST satisfy native runtime <= 2.5 times optimized C same-algorithm implementations
for EVERY required operation/workload, not just an aggregate. Performance is a
measured acceptance condition, not a proved universal timing theorem. Do not
claim current work meets it without fresh comparable evidence. No partial
checkpoint is completion. Continue all missing implementation + proofs + native
benchmarks + optimization + self-audit in each assignment. No arbitrary worker
four-hour cap or planned checkpoint exit; earlier prose to that effect is superseded.

Implement benchmarks/run.py --report PATH, and BENCHMARKS.md with a reproducible
command and tables for ALL operations in automation/performance_contract.json.
That contract and automation/performance_gate.py are frozen operator-owned gates.
Read the gate to follow its exact report schema. Add workload sizes, seeds,
valid/invalid cases where applicable and realistic representative larger cases;
the listed operations are the MINIMUM, never permission to omit other public APIs.
Benchmark small/medium/large nonempty workloads for each scalable operation and
edge cases separately. One smoke-sized fixture or a mixed average is insufficient.
DSA includes reused LRU in these benchmarks; no separate LRU worker is needed.

Build BOTH sides optimized in release mode on the same machine; Bend must use its
native C backend, one sequential execution thread. No Bun/JS result qualifies.
Create genuinely optimized C implementations of the SAME DSA algorithms with
identical semantics, numeric domain, representation choices and workloads. C may
use normal efficient memory management; never deliberately penalize the reference.
BLS uses pinned upstream blst C with its normal optimized assembly enabled where
supported; match Ethereum POP domain, input validation, subgroup checks and
aggregation/security semantics. C/blst are benchmark references ONLY, never foreign
runtime replacements for the proved Bend algorithms. SSZ uses pinned Go fastssz,
not a C SSZ library; its maximum is 5x, not 2.5x. All 109 Fulu types need serialize,
deserialize and root comparisons, with generated fastssz definitions where needed.
Start SSZ with the five existing BeaconState cases; preserve the separate native
32,000,000-byte decode-overhead gate and all proofs. Add representative larger
states as supplemental evidence, clearly distinguishing synthetic from production.

At least five alternating independent samples per workload, calibrated enough to
avoid timer quantization; include repeated batches for tiny operations and record
operations per sample. Input generation, compilation and unrelated file IO excluded
from operation timings symmetrically. Include required validation/allocation and
consume all results; no precomputation, cached answers, fixture detection, omitted
checks or dead-code-eliminated calls. Preserve raw timing logs and output checks;
record exact sources, reference pins, compiler versions/flags, CPU/OS, executable
hashes, operation definitions and sample counts. Reference times must be positive.
Do not hide bad workloads with geomeans. Report medians and individual samples;
each workload median ratio must meet the limit. Audit noise, variation and rerun
borderline cases under controlled conditions before final acceptance.

The runner must freshly build and execute measured programs; honor no skip-build
flag in acceptance. Report current source_sha256 for all candidate runtime/proof/
benchmark inputs, artifacts with raw logs/executable hashes, and correct outputs.
The numeric gate cannot prove honesty of a worker-authored runner: the independent
auditor MUST inspect harnesses, C reference quality, workload coverage, proof linkage
and reproduce timings before accepting. Missing native compiler support is a real
blocker to report and fix in source; never silently substitute JS or patch a trusted
compiler. Keep implementation simple and reusable; do not restart proven mathematics.

Review the entire remaining objective in every assignment. Worker can read this exact audit policy. Immediately continue an explicitly incomplete worker without wasting a final audit. Independently inspect work; never accept numeric self-reports as proof of measurement integrity.


## Latest user requirement: actual red-black binary search tree

The balanced_search_tree implementation MUST be a red-black BINARY search tree,
not the current 2-3 tree, an AVL tree, or an unbalanced tree. This supersedes the
earlier AVL-default suggestion. Binary heap is unchanged; other data structures
remain in scope unchanged. Replace the current runtime representation/algorithms
with explicit red/black nodes and two children, using a conventional red-black
variant (including left-leaning if helpful). Keep the complete existing ordered-map
API and comparator/error semantics. A renamed 2-3 tree or conversion facade with
the old tree as the actual operational storage does not satisfy the requirement.

Prove ordering and map semantics, a black root, black empty leaves, no red-red
parent/child edges, equal black height on every path, initialization and invariant
preservation for insertion AND deletion, plus all other inventoried operations
and arbitrary reachable operation traces. Connect these to actual runtime paths
and END_TO_END. Reuse independent ordered-map specs and useful checked lemmas;
preserve all unrelated implementation/proofs. Prior 2-3 tree proof evidence does
not verify the new implementation. Archive provenance of replaced work in docs.

Update the optimized C reference to the SAME red-black algorithm and representation
policy, with full operation/workload coverage and <=2.5x per-workload native Bend/C
timing. Include empty/singleton, duplicates, absent removal, root removal, ordered
and reverse-ordered insertions, and adversarial mixed deletion/insert histories.
Runtime tests must check structural red-black invariants as well as abstract
contents; independent audit must inspect actual invariants and proof linkage.
All other frozen correctness and benchmark gates remain mandatory. Keep working
on the entire remaining objective each assignment and retain the worker session.


## Latest user correction: ALL DSA performance <=2.5x C

Every in-scope DSA structure, including reused LRU and the required red-black
binary search tree, must execute every required native benchmark workload in
at most 2.5 times its optimized same-algorithm C reference time. This supersedes
all older 10x DSA limits, not just the tree limit. Retain all correctness proofs,
red-black invariants, conformance/mutation tests, full operation coverage, fair
optimized C controls and independent audit requirements. No averages hiding
failing workloads. Preserve all seeded work; keep implementing the whole scope.
SSZ and BLS limits are unaffected.


## Latest user correction: ALL DSA performance <=2.5x C

Every in-scope DSA structure, including reused LRU and the required red-black
binary search tree, must execute every required native benchmark workload in
at most 2.5 times its optimized same-algorithm C reference time. This supersedes
all older 10x DSA limits, not just the tree limit. Retain all correctness proofs,
red-black invariants, conformance/mutation tests, full operation coverage, fair
optimized C controls and independent audit requirements. No averages hiding
failing workloads. Preserve all seeded work; keep implementing the whole scope.
SSZ and BLS limits are unaffected.

## Operator requirement: representation appropriate to the algorithm

Do NOT use linked lists as runtime storage for algorithms that do not intrinsically
need linked lists. Use native Base.Array, packed word arrays, indexed arenas,
fixed records and appropriate existing native Map/Set facilities. No linked-list
backing for dynamic arrays, ring-buffer queues/deques, binary heaps, bitsets,
union-find parent/size/member storage, Fenwick/segment-tree indexed storage, or
merely to hold graph neighbors/trie children. Logical adjacency lists do not require
cons-cell storage; use an appropriate array/indexed or native-map representation.
Do not convert arrays to lists internally for convenience, then convert back.
Avoid a persistent cons spine as a generic array/vector substitute. Inspect emitted
C and benchmark indexing, traversal, allocation and updates rather than assuming
Bend source types guarantee efficient native layout. Native Array indexed access
is the intended primitive; do not structurally walk its ANode tree for indexing.

Exceptions must follow the actual algorithm: the requested doubly linked list
still needs explicit previous/next links and stable handle semantics; LRU may need
recency links; tree/trie nodes need their genuine child relationships. Links may
be indices into an arena. A tree is not prohibited merely because it has edges.
Retain the actual red-black binary tree requirement and its invariants. Do not
replace necessary links or reimplement native Map/Set/Stack or native String just
because this rule mentions linked lists. Keep the immutable reused LRU snapshot
intact and port only necessary copies within authorized editable scope.

Pure mathematical specifications and erased proof models may use lists. They must
not dictate runtime storage or execute in the hot path. Preserve every semantic
operation, generic/comparator instance, invalid-input behavior, invariant and trace
proof; re-establish proofs against the actual changed representation. No vacuous
adapter-only proof or new arbitrary capacity restriction to make the proof easier.

Add a concise representation table in docs/ARCHITECTURE.md covering each structure,
its native backing, any retained links, why those links are algorithmically needed,
and the associated representation bridge/invariant proofs. Worker must self-audit
this table against code and emitted C. Orchestrator and independent auditor must
reject unnecessary linked-list runtime backing, not just accept passing tests.

This is an additional requirement, not a new partial assignment: complete ALL
remaining implementation, proof, runtime-test and performance obligations together.
The <=2.5x optimized same-algorithm C requirement remains for EVERY required row.
Retain current array-migration work and proofs; use targeted benchmarks during
changes and complete full gates at meaningful milestones. Continue incomplete
work immediately instead of treating a checkpoint as completion.


# User correction: reject lazy initialization

The user explicitly rejects lazy initialization as an optimization direction. This supersedes prior experimentation with lazy constructors. Do not optimize constructor scores by returning a deferred placeholder and charging initialization/allocation to the first operation.

Remove deferred-initialization variants recently introduced for union-find, graph and doubly linked list; inspect other structures for the same pattern. Constructors must establish the normal usable representation immediately, with required initial storage initialized. Preserve conventional capacity growth on later insertions; this does not require allocating maximum future capacity in an empty structure. Optimize actual constructor work, not movement of that work out of its benchmark.

Preserve valid unrelated improvements (ring buffers, branchless segment-tree access, bitset, Fenwick, efficient native indexed storage). Repair and check proofs for the final eager representation. Archive useful experimental evidence with accurate labels; lazy-only speed claims cannot count as acceptance. Keep original optimized C references, workloads and 2.5x limits unchanged; do not replace them with lazy C twins to claim success. Include constructor-plus-first-use and mixed-operation checks to detect hidden deferred costs. Existing capacity, type/helper proof gaps and every remaining structure remain part of the objective. Continue all missing implementation, proofs and performance work; no early stop after reverting lazy paths.
