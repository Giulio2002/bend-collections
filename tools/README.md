# Tools

Everything here is Python (3.10+) and serves development: building the checked
proof files from their sources, validating the containers against independent
oracles, and differential tests. Nothing in `src/` depends on it, and the
committed `.bend` proofs check without it.

## Toolchain

`toolchain.json` pins the Bend release the project is checked with (2.0.25) by
path and SHA-256, and `toolchain.py` exposes it to the scripts. Paths may start
with `~`. To use a private copy of the pinned release, set `BEND_HOME` to a
directory holding `.bend/bin/bend` and `.bend/bend2`. The benchmark and proof
scripts outside `tools/` fall back to `$BEND` or `bend` on the PATH.

## Proof sources: `.src` files and `generators/mac.py`

Bend proofs repeat long types and argument lists constantly (the TreeMap
invariant alone takes eleven fields). So most proof files are written as a
`.src` file next to the `.bend` it becomes, and `mac.py` expands it:

```sh
python3 tools/generators/mac.py proofs/containers/lru/add.src proofs/containers/lru/add.bend
```

The `.bend` is what the checker checks and what is committed; always
regenerate it after editing the `.src`, never edit such a `.bend` by hand.
A `.src` is ordinary Bend plus these lines:

| Line | Meaning |
|---|---|
| `%def NAME text` | every `$NAME` expands to `text` |
| `%def NAME(a, b) text` | `$NAME(x, y)` expands to `text` with `a`, `b` replaced; arguments split at top-level commas, `<\|x, y\|>` keeps its commas |
| `%tmpl NAME(a, b)` ... `%end` | a multi-line template; a line `%use NAME(x, y)` expands to its lines |
| `a##b` | token pasting inside templates (`N##_c` with `N = put` gives `put_c`) |
| `%include file.src` | imports the `%def`s and templates of another source (paths relative to the including file) |

Macros may use other macros; expansion repeats until nothing changes.
Example, from the TreeMap proofs:

```
%def FT +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: $NL, +pl: $PL, +tg: ST.Tr, +fl: $LN
%def F n, root, lo, hi, free, l, d, nl, pl, tg, fl
%def SH ST.SH{$F}
def size_eq($TK, $FT, +hg: $GF) -> {n == SC.length($E, $EST) : Nat}:
```

To regenerate every proof from its source:

```sh
for f in $(find proofs -name '*.src'); do [ -f "${f%.src}.bend" ] && python3 tools/generators/mac.py "$f" "${f%.src}.bend"; done
```

A `.src` without a `.bend` of the same name holds only shared macros for
`%include` (for example `balanced_search_tree/wrap.src`).

## Generators

Each writes checked Bend files that are committed; rerun it after changing
what it generates from.

| Generator | Writes |
|---|---|
| `generators/intrusive_list.py` | intrusive core/compatibility facades and shared internal implementation; `--check` verifies committed output without rewriting |
| `generators/tree_map.py` | the implementation `src/containers/balanced_search_tree.bend` (state threading lowered into helpers) |
| `generators/tm_state.py` | the TreeMap's shadow, model and invariant (`proofs/containers/balanced_search_tree/state.bend`) |
| `generators/tm_mirror.py` | the TreeMap's mirror of the implementation over shadows (`mirror.bend`) and the proofs that the implementation computes the mirror (`sim.bend`); hand-written heads in `balanced_search_tree/gen/*.part` |
| `generators/tm_gate.py` | the TreeMap's entry point `proof.bend`: one theorem per public operation, restated from the proof modules |
| `generators/hash_table_state.py` | the hash map's invariant (in `hash_table/state.bend`) and its rebuild lemmas (`rebuild.bend`) |
| `generators/lru_state.py` | the LRU's invariant (in `lru/state.bend`, after the generated-section marker) |
| `generators/dll_state.py` | the doubly linked list's shadow, model and invariant (`doubly_linked_list/state.bend`) |
| `generators/trace_data.py` | the trace-refinement module of a structure with Data state (`trace.bend`) |
| `generators/pat_expand.py` | helper: expands overlapping match rows into disjoint ones (the checker only reduces on a row that names the shape) |
| `generators/blake2s_gen.py`, `blake2s_tests.py` | BLAKE2s's unrolled compression, block reads, proof lemmas and test vectors |
| `generators/blake2b_gen.py` | BLAKE2b's lanes, unrolled compression, block reads, proof lemmas and tests |
| `generators/blake3/gen.py`, `proofs.py`, `tests.py` | BLAKE3's compression and block reads, their proof modules, and test vectors from the official C |
| `toposort.py` | reorders the definitions of a Bend file so every callee precedes its callers (Bend has no forward references) |

## Validation and differential tests

| Script | Checks |
|---|---|
| `check_intrusive_proofs.py --bend bend` | regenerate proof sources, clean semantic and concrete-adapter checks, coordinated specification and adapter negative controls |
| `check_intrusive.py --bend bend --cc clang` | intrusive-list proofs, C/JS conformance, examples, semantic mutants and native heap-allocation measurements; see [guide](../INTRUSIVE_LIST.md) |
| `../benchmarks/intrusive.py --bend bend --cc clang` | warmed entity transfers and pooled lifecycles against the public DList API and C; independent oracle, generation-layer diagnostic, A/A control, separate timing/allocation/live-byte binaries, raw samples; [method and results](../benchmarks/INTRUSIVE_LIST.md) |
| `validate.py --report build/validation.json` | every container in `tests/structures.json`: builds `tests/<id>/main.bend`, compares its output with the Python oracle in `tests/support/oracles.py` on functional, boundary, differential and structural scenarios (`scenarios.py`), runs semantic mutants that must be caught (`mutants.py`), and checks the container's proof |
| `check_hash_table.py` | the hash map against a Python dict on random histories (growth, backward-shift deletion, every key kind) |
| `check_lru_spec.py` | the LRU against its executable specification, step by step with a moving clock |
| `lru_diff.py` | the Bend LRU against the C reference and its ASan/UBSan build, bit for bit |
| `check_tree_map.py`, `check_tree.py`, `check_tree_map_mutations.py` | the TreeMap against an ordered-map oracle with red-black invariant checks, and mutations that must be caught |
| `check_iterators.py`, `check_queue_facades.py`, `check_two_list.py`, `check_two_list_mutations.py`, `check_owned_array.py`, `check_owned_array_guards.py` | the iterators, the queue facades, the two-list deque and queue, and owning arrays against independent oracles |

The hash functions are fuzzed by `tests/crypto/fuzz.py` (random messages
against hashlib, pycryptodome and the official BLAKE3 C).

## Changing a proof

1. Edit the `.src` (or the generator), regenerate the `.bend`.
2. Check the package: `python3 proofs/prove.py <package>` (or
   `bend proofs/containers/<package>/proof.bend`); success prints
   `All terms check.`
3. Before committing, make sure every source still reproduces its committed
   `.bend` (the loop above leaves `git status` clean).
