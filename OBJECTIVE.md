# bend-dsa: verified missing data structures for Bend

Deliver all twelve missing data structures in inventory/structures.json in pure Bend, with usable public APIs, independent mathematical specifications, universal functional-correctness proofs, invariant preservation, and arbitrary finite operation-trace composition. Reuse existing native structures and the completed LRU; do not build another Map, Set or Stack. Read inventory/base-audit.md and the installed `bend guide` before implementation. This project is setup only until automation/run.sh is explicitly launched.

## Scope and sensible implementation choices

The protected inventory is the minimum complete public operation set. Write APIs in src/<id>.bend, independent specs in spec/<id>.bend, proofs in proofs/<id>.bend, public laws in END_TO_END.bend imported by PROOF.bend. Additional internal modules are allowed. Native Base.Array is fixed capacity with wrapping indices: dynamic_array must add logical length, safe get/set, growth/reserve, empty behavior and overflow rejection while reusing it; never pass unchecked indices or an unrepresentable capacity. Use native indexed storage and verify its generated C layout; do not infer complexity merely from the source type.

Recommended dependency order: dynamic_array first; deque and its queue specialization; heap and packed bitset; union-find, Fenwick and segment trees; balanced search tree, prefix trie, graph and doubly linked list. This is an implementation order, NOT separate assignments or stopping points. Finish the whole scope each invocation.

For doubly linked lists use stable opaque handles with stale/foreign-handle rejection and exact bidirectional-link invariants; adapt to Bend ownership with explicit returned state, without unsafe pointers. For trees/heaps parameterize a comparator with explicit total-order laws and check concrete instances. The balanced search tree must be an actual red-black binary tree with proved red-black invariants; AVL and 2-3 runtime trees do not satisfy the user requirement. A binary heap must maintain heap order and exact element multiplicities. Bitsets must use packed words, enforce logical size and mask unused tail bits. Queue must be FIFO, deque both-ended; avoid a naive full-list append on every enqueue. Native Map may support handles, graphs and prefix tries; do not reinvent it.

DSU must implement union-by-size/rank and path compression or a documented Bend-appropriate equivalent, with partition/component-size correctness. Graph means the directed and undirected finite simple adjacency structure, including isolated vertices, vertex removal, self-loop policy, idempotent edge insertion and endpoint errors. Traversal, shortest paths and unrelated graph algorithms are not requested. Trie operates on String/Char prefixes with deterministic enumeration and exact prefix and longest-prefix semantics.

Fenwick supports point addition and half-open prefix/range sums. Segment tree supports point assignment, half-open range queries and lazy range addition. Use a precise numeric domain (default U32 modular sums/addition with wrap explicit) rather than silently overflowing a mathematical integer specification. Arbitrary-monoid variants, persistence histories, concurrency, FFI, callbacks, crypto and AESENC are not required. Generic element/value types and supported key/order instances must be documented and genuinely checked. No runtime JS/TS data-structure implementation or host wrapper is needed: expose pure Bend APIs and use host code only for tests. Every error operation must have explicit state-preservation semantics.

## Reuse, proofs and completion

reference/lru is an immutable completed project snapshot. Preserve all its proofs and pin provenance; reuse needed Map, word and codec lemmas instead of deriving them again. The new installed compiler is Bend 2.0.16: first establish which retained proofs still check and port only necessary copies, never modify the reference or assume its old test evidence proves new compatibility. Integrate a small reuse entry/guide under src/lru.bend and proofs/lru.bend once compatibility is established. Inherited TypeScript residue remains explicitly trusted; do not describe it as formally proved or introduce it into the new pure-Bend structures.

Specs must be independent list/finite-map/partition/multiset/sequence mathematics, not calls to src or a renamed copy of its algorithms. Prove initialization, every inventoried operation, errors, invariant preservation and arbitrary finite traces from constructors through the real public APIs. Discharge invariants at reachable states. For native Base dependencies reused by new structures, prove needed high-level algorithm properties or reuse checked proofs; primitive semantics and the unmodified checker are trusted, not unproved Map/Array algorithms. Compiler, runtime and hardware are outside the functional proof. No unsafe escapes, holes, unfilled declarations, axioms, trusted expected outputs, finite enumeration masquerading as universal proof, vacuous equality or hidden bounds. Check every static-parameter specialization used by actual APIs; checking an unused generic template is insufficient.

Create tools/validate.py --report PATH with real Bend runtime tests against independent oracles, boundary/invalid-input tests, deterministic stateful differential histories and semantic mutation rejection per structure. Preserve trace seeds and exact source hashes. No skipping, fake reports, answer leakage, weakened checks, or mutation crashes counted as semantic rejection. Completion report schema is fixed by automation/acceptance.py. A suite status is a claim until independently audited: the auditor must trace it to executable checks and actual proof statements. No substring-only completion decision. Maintain per-structure API/proof/trace/test obligations and truthful complexity documentation. Do not claim amortized/O(1)/inverse-Ackermann guarantees without supporting analysis; proof effort should first close functional composition, not unnecessary generic frameworks.

Keep building the entire remaining scope continuously. Maintain recovery notes without ending an invocation at each milestone. Read literal AUDITOR.md, perform its checks yourself, repair all findings, then request final audit. The orchestrator independently reviews and immediately continues incomplete work rather than auditing a knowingly partial milestone. Reuse sessions. Only a genuine process/context interruption warrants needs_work. No time/cycle cap. Worker may edit only the candidate: no subagents, commits, pushes, toolchain changes or other projects.

```toml
name = "bend-dsa: missing data structures with universal functional proofs"
project = "/Users/monkeair/work/dsa-performance/runs/20260919T231929Z-da17b50c/iterations/0003/workspace"
backend = "claude"
claude = "/Users/monkeair/.local/bin/claude"
claude_effort = "medium"
model = "claude-opus-5"
orchestrator_model = "claude-opus-5"
max_iterations = 0
agent_timeout = 0
orchestrator_timeout = 0
validation_timeout = 43200
editable = ["benchmarks/*", "BENCHMARKS.md", "src/*", "spec/*", "proofs/*", "types/*", "tests/*", "tools/*", "*.bend", "README.md", "WORK_LOG.md", "PROOF_STATUS.md", "VALIDATION.json", "docs/*"]
protected = ["automation/*", "inventory/*", "reference/*"]
ignore = ["build", "build/*", "__pycache__", "*.pyc", ".nanocodex", ".nanocodex/*"]
validation = [["/Users/monkeair/auto-implementer/.venv/bin/python", "automation/acceptance.py"], ["/Users/monkeair/auto-implementer/.venv/bin/python", "automation/performance_gate.py"]]

[criteria]
red_black = "Actual red-black binary search tree, all ordering/color/black-height laws and insert/delete/trace proofs; matching optimized C reference within 2.5x."
performance = "All native benchmark workloads <= 2.5x optimized C same-algorithm implementations; full operation coverage, independently audited optimized references, raw reproducible samples, no missing evidence."
inventory = "All 12 missing structures and every inventoried operation implemented; native Map/Set/Stack excluded and completed LRU reused."
proofs = "Independent mathematical specs, universal actual-public-operation proofs, invariant preservation and finite traces for all new structures, with checked instances."
runtime = "Actual Bend runtime passes independent model/differential/boundary tests for every operation; semantic mutations are rejected."
composition = "PROOF imports real END_TO_END and all public laws; reachable premises and native primitive-to-algorithm bridges discharged; no vacuity or assumed result."
reuse = "Pinned LRU reused without lost proofs; new toolchain compatibility established and exact trust boundary retained."
engineering = "Usable pure Bend APIs, reproducible evidence, native storage reuse and honest representation/cost/error documentation."
```


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
