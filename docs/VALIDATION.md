# Validation: what is run, and how to reproduce it

Everything below runs from the workspace root with the pinned toolchain in
`inventory/toolchain.json` (bend 2.0.16; `automation/acceptance.py` re-hashes
the binary and `base.bend` before doing anything else).

## 1. The proofs

```sh
bend PROOF.bend          # the single root: END_TO_END.bend and everything under it
bend END_TO_END.bend     # the public laws on their own
bend proofs/<id>.bend    # one structure
```

`All terms check` is the only accepted result. The "N unsafe annotations" in the
summary line counts *template instantiations*; every instantiation is itself
fully checked, and `automation/acceptance.py` separately greps the whole import
closure for `@unsafe`, `?holes` and foreign imports.

## 2. Behavioural validation

```sh
python3 tools/validate.py --report build/validation.json
python3 tools/validate.py --report build/validation.json --only balanced_search_tree
```

For each of the twelve structures it

1. compiles `tests/<id>/main.bend` to a **native binary** (so the compiled
   backend, not just the interpreter, is exercised);
2. **functional** — runs the scenarios in `tools/scenarios.py` `FUNCTIONAL`,
   which between them exercise every operation in
   `inventory/structures.json`, and compares every output line against the
   independent Python model in `tests/support/oracles.py` (the Bend side never
   sees an expected answer);
3. **boundary** — empty structures, out-of-range indices, invalid ranges,
   foreign/stale handles, capacity limits; each rejected operation is followed
   by an observation of the whole state, so state preservation after an error
   is checked, not only the error value;
4. **differential** — deterministic pseudo-random histories from the seeds in
   `tools/scenarios.py` `SEEDS`;
5. **structural** — only `balanced_search_tree` today: the `rb32`/`rbstr`
   driver kinds re-derive the red-black invariants from the tree that `src/`
   actually built, after *every* operation (black root, no red-red
   parent/child edge, one black height on every root-to-leaf path, strictly
   increasing in-order keys, cached size = entry count);
6. **mutations** — per-structure semantic mutants of `src/<id>.bend`
   (`tools/mutants.py`). A mutant must be *rejected by a scenario*: a mutant
   that fails to compile or crashes does **not** count as killed;
7. **trace_proof** — re-runs `bend proofs/<id>.bend`.

### Where the packed-bitset representation invariant is checked at runtime

`bitset` keeps its words in a `Base.Array` of 2^depth words, so a bitset can
carry both *tail* bits (the unused high bits of the last used word) and whole
*padding* words. The invariant says every stored bit at a position `>= len` is
zero, and the proof relies on it. At runtime that is checked behaviourally,
which is stronger than inspecting the words: `count` and `to_list` report the
population and the member indices of the **whole** word array, so a single
stray bit beyond `len` would make them disagree with the independent Python
model. The scenarios therefore include sizes that are not multiples of 32 and
sizes whose word array has a whole padding word:

| size | words needed | array words | what it exercises |
|---|---|---|---|
| 0  | 0 | 1 | an entirely padding array |
| 1  | 1 | 1 | 31 tail bits |
| 4  | 1 | 1 | 28 tail bits, with combines |
| 12 | 1 | 1 | 20 tail bits, all four combines |
| 40 | 2 | 2 | a word boundary at bit 32, 24 tail bits |
| 65 | 3 | 4 | a word boundary at 32 and 64, 31 tail bits **and** a whole padding word; plus combines against operands one bit shorter and one bit longer |

`tools/mutants.py` additionally kills a mutant that drops the bit index inside
the word (`bitix` -> 0) and one that stops the whole-array combine one word
short, both of which are only observable through the same reports.

### Where the graph's sorted representation is checked at runtime

`graph` keeps its vertex ids ascending in a window of one block and each
vertex's neighbours ascending in one adjacency block, and it finds both by
BINARY SEARCH. A representation that silently stopped being sorted would
still answer many queries correctly, so the scenarios insert both vertices
and neighbours OUT of order and then observe the sorted enumerations and the
searches that depend on them:

| scenario | what it exercises |
|---|---|
| `av:9 av:3 av:7 av:1 av:5 vs ...` | the vertex window stays sorted when ids arrive in no order; `vs` observes it |
| `ae:1:9 ae:1:3 ae:1:7 ae:1:5 nb:1 edges` | the adjacency block stays sorted when neighbours arrive descending and interleaved |
| `he:1:3 he:1:5 he:1:7 he:1:9 he:1:1` | every entry is found by the binary search, and a non-neighbour is not |
| `re:1:7 nb:1 he:1:7 ae:1:7 nb:1` | deletion closes the gap and re-insertion lands back in order |
| undirected `ae:4:8 ae:4:2 ae:4:6 nb:2 nb:6 nb:8 rv:4 ...` | symmetry, and that removing a vertex leaves no stale edge in any block |

`tools/mutants.py` kills a mutant that appends a neighbour instead of
inserting it in order (`blk_put(b, deg, ent_end(deg), w)`), one that keeps
the previous occupant's neighbours when a new vertex takes a slot, one that
stores an undirected edge at one endpoint only, one that removes it from one
endpoint only, one that accepts self-loops and one that negates
`has_vertex` -- six mutants, all rejected by a scenario, none by a crash.

The LRU is validated in `bend` run mode (see the blocker below) through
`tests/lru/main.bend` and reported as `lru_reuse`.

## 3. The mechanical acceptance gate

```sh
python3 automation/acceptance.py
```

Protected and frozen. It checks the toolchain hashes, every
`reference/lru` file hash, the presence of `src|spec|proofs/<id>.bend` for all
twelve structures, the absence of unsafe/holes/foreign imports in the whole
proof closure, that `PROOF.bend` and `END_TO_END.bend` check, and that
`tools/validate.py` reports every structure passing every category with every
inventoried operation covered.

Last run in this workspace: **passed**
(`Mechanical gates passed; independent full semantic audit still required.`).

## 4. Performance

```sh
python3 automation/performance_gate.py          # builds, runs and validates
python3 benchmarks/run.py --report build/performance/report.json   # runner only
```

See `BENCHMARKS.md`. The gate is **not** satisfied; the numbers and the reasons
are recorded there rather than worked around.

## Known toolchain defects (reproducers under `tests/runtime_defects/`)

* **`wide_arity.bend` — arity over 255.** Bend 2.0.16's native C backend
  flattens a non-recursive `Data` constructor into a single node and rejects a
  flattened arity above 255. `Word(64n)` occupies 64 slots, so three such
  fields (192) compile and four (256) do not.
  `reference/lru/types/model.bend` declares
  `Metrics = Counts{inserts, evictions, removals, hits, misses}` with five
  `Word(64n)` fields (320 slots) and every `Cache` contains one, so **no LRU
  program can be compiled to a native binary**. `reference/` is a protected,
  hash-pinned snapshot, so this cannot be repaired in editable source; a
  wrapper type in `src/lru.bend` does not help, because the rejected
  constructor is `Metrics` itself (verified: a program that only builds
  `M.Counts{…}` still fails). Flattening is **transitive through
  non-recursive `Data`**: boxing each counter as
  `type Int64 is Data: I64{bits: Word(64n)}` and declaring five `Int64` fields
  still fails (5 x 64 = 320 slots), while five fields of a *recursive* type
  compile (a recursive type is a pointer, arity 5). Both variants are in
  `tests/runtime_defects/wide_arity.bend`. A native LRU therefore needs the
  field type of `Metrics` changed inside the hash-pinned snapshot, or the whole
  reference (25k lines, 22.5k of them proofs, 383 `Counts{…}` sites) ported
  into editable `src/`. Consequence: the LRU is validated in run mode and
  has no native benchmark rows.
* **`generic_u32.bend` — erased-generic U32 corruption.** U32 values passed
  through erased-generic (`-T`) compiled code are corrupted after a real call.
  Generic structures are runtime-tested with `Nat`/`String` elements; `U32`
  only appears in concrete code.
* **Matching a `Base.Array` structurally destroys its flat representation.**
  `ALeaf`/`ANode` patterns work, but a structural traversal of a 128-word
  array measured ~15 ns per word where an indexed loop measured ~0.3 ns:
  `Base.Array` is a flat array in the native backend and only indexed access
  keeps it that way. `src/bitset.bend` therefore walks its word array by
  index, never structurally.
* **Closed `Base.Array` element type.** The native backend needs a closed
  element type for `Base.Array`; `src/dynamic_array.bend` therefore provides
  `*_at` template specialisations, proved equal to the generic versions in
  `proofs/dynamic_array/closed.bend`.

## Environment caveat for timings

The measurements in `BENCHMARKS.md` were taken on a machine that was **not
idle**: other, unrelated processes were using whole cores throughout (load
average 3–7). `benchmarks/run.py` detects and rejects unusable measurements
rather than reporting them, but the surviving numbers still carry that noise.
Re-run on an idle machine for publication-quality figures.
