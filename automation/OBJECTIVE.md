> User scope update (2026-09-22): standalone DLL retired; queue/deque use the two-list design. Empty timing rows excluded for all structures; empty correctness/proof obligations remain. Full sweep includes LRU and retains the 2.5x threshold. See docs/NONEMPTY_BENCHMARK_SCOPE.md.

# bend-dsa: verified missing data structures for Bend

Deliver all twelve missing data structures in inventory/structures.json in pure Bend, with usable public APIs, independent mathematical specifications, universal functional-correctness proofs, invariant preservation, and arbitrary finite operation-trace composition. Reuse existing native structures and the completed LRU; do not build another Map, Set or Stack. Read inventory/base-audit.md and the installed `bend guide` before implementation. This project is setup only until automation/run.sh is explicitly launched.

## Scope and sensible implementation choices

The protected inventory is the minimum complete public operation set. Write APIs in src/<id>.bend, independent specs in spec/<id>.bend, proofs in proofs/<id>.bend, public laws in END_TO_END.bend imported by PROOF.bend. Additional internal modules are allowed. Native Base.Array is fixed capacity with wrapping indices: dynamic_array must add logical length, safe get/set, growth/reserve, empty behavior and overflow rejection while reusing it; never pass unchecked indices or an unrepresentable capacity. This is a tree-backed dynamic array, not a promise of C-vector complexity.

Recommended dependency order: dynamic_array first; deque and its queue specialization; heap and packed bitset; union-find, Fenwick and segment trees; balanced search tree, prefix trie, graph and doubly linked list. This is an implementation order, NOT separate assignments or stopping points. Finish the whole scope each invocation.

For doubly linked lists use stable opaque handles with stale/foreign-handle rejection and exact bidirectional-link invariants; adapt to Bend ownership with explicit returned state, without unsafe pointers. For trees/heaps parameterize a comparator with explicit total-order laws and check concrete instances. A balanced tree must maintain an actual balance invariant (AVL is a reasonable default); do not substitute an unbalanced search tree. A binary heap must maintain heap order and exact element multiplicities. Bitsets must use packed words, enforce logical size and mask unused tail bits. Queue must be FIFO, deque both-ended; avoid a naive full-list append on every enqueue. Native Map may support handles, graphs and prefix tries; do not reinvent it.

DSU must implement union-by-size/rank and path compression or a documented Bend-appropriate equivalent, with partition/component-size correctness. Graph means the directed and undirected finite simple adjacency structure, including isolated vertices, vertex removal, self-loop policy, idempotent edge insertion and endpoint errors. Traversal, shortest paths and unrelated graph algorithms are not requested. Trie operates on String/Char prefixes with deterministic enumeration and exact prefix and longest-prefix semantics.

Fenwick supports point addition and half-open prefix/range sums. Segment tree supports point assignment, half-open range queries and lazy range addition. Use a precise numeric domain (default U32 modular sums/addition with wrap explicit) rather than silently overflowing a mathematical integer specification. Arbitrary-monoid variants, persistence histories, concurrency, FFI, callbacks, crypto and AESENC are not required. Generic element/value types and supported key/order instances must be documented and genuinely checked. No runtime JS/TS data-structure implementation or host wrapper is needed: expose pure Bend APIs and use host code only for tests. Every error operation must have explicit state-preservation semantics.

## Reuse, proofs and completion

reference/lru is an immutable completed project snapshot. Preserve all its proofs and pin provenance; reuse needed Map, word and codec lemmas instead of deriving them again. The new installed compiler is Bend 2.0.16: first establish which retained proofs still check and port only necessary copies, never modify the reference or assume its old test evidence proves new compatibility. Integrate a small reuse entry/guide under src/lru.bend and proofs/lru.bend once compatibility is established. Inherited TypeScript residue remains explicitly trusted; do not describe it as formally proved or introduce it into the new pure-Bend structures.

Specs must be independent list/finite-map/partition/multiset/sequence mathematics, not calls to src or a renamed copy of its algorithms. Prove initialization, every inventoried operation, errors, invariant preservation and arbitrary finite traces from constructors through the real public APIs. Discharge invariants at reachable states. For native Base dependencies reused by new structures, prove needed high-level algorithm properties or reuse checked proofs; primitive semantics and the unmodified checker are trusted, not unproved Map/Array algorithms. Compiler, runtime and hardware are outside the functional proof. No unsafe escapes, holes, unfilled declarations, axioms, trusted expected outputs, finite enumeration masquerading as universal proof, vacuous equality or hidden bounds. Check every static-parameter specialization used by actual APIs; checking an unused generic template is insufficient.

Create tools/validate.py --report PATH with real Bend runtime tests against independent oracles, boundary/invalid-input tests, deterministic stateful differential histories and semantic mutation rejection per structure. Preserve trace seeds and exact source hashes. No skipping, fake reports, answer leakage, weakened checks, or mutation crashes counted as semantic rejection. Completion report schema is fixed by automation/acceptance.py. A suite status is a claim until independently audited: the auditor must trace it to executable checks and actual proof statements. No substring-only completion decision. Maintain per-structure API/proof/trace/test obligations and truthful complexity documentation. Do not claim amortized/O(1)/inverse-Ackermann guarantees without supporting analysis; proof effort should first close functional composition, not unnecessary generic frameworks.

Keep building the entire remaining scope continuously. Maintain recovery notes without ending an invocation at each milestone. Read literal AUDITOR.md, perform its checks yourself, repair all findings, then request final audit. The orchestrator independently reviews and immediately continues incomplete work rather than auditing a knowingly partial milestone. Reuse sessions. Only a genuine process/context interruption warrants needs_work. No time/cycle cap. Worker may edit only the candidate: no subagents, commits, pushes, toolchain changes or other projects.

```toml
name = "bend-dsa: missing data structures with universal functional proofs"
project = ".."
backend = "claude"
claude = "/Users/monkeair/.local/bin/claude"
claude_effort = "medium"
model = "claude-opus-5"
orchestrator_model = "claude-opus-5"
max_iterations = 0
agent_timeout = 0
orchestrator_timeout = 0
validation_timeout = 43200
editable = ["src/*", "spec/*", "proofs/*", "types/*", "tests/*", "tools/*", "*.bend", "README.md", "WORK_LOG.md", "PROOF_STATUS.md", "VALIDATION.json", "docs/*"]
protected = ["automation/*", "inventory/*", "reference/*"]
ignore = ["build", "build/*", "__pycache__", "*.pyc", ".nanocodex", ".nanocodex/*"]
validation = [["/Users/monkeair/auto-implementer/.venv/bin/python", "automation/acceptance.py"]]

[criteria]
inventory = "All 12 missing structures and every inventoried operation implemented; native Map/Set/Stack excluded and completed LRU reused."
proofs = "Independent mathematical specs, universal actual-public-operation proofs, invariant preservation and finite traces for all new structures, with checked instances."
runtime = "Actual Bend runtime passes independent model/differential/boundary tests for every operation; semantic mutations are rejected."
composition = "PROOF imports real END_TO_END and all public laws; reachable premises and native primitive-to-algorithm bridges discharged; no vacuity or assumed result."
reuse = "Pinned LRU reused without lost proofs; new toolchain compatibility established and exact trust boundary retained."
engineering = "Usable pure Bend APIs, reproducible evidence, native storage reuse and honest representation/cost/error documentation."
```
