# Dynamic arrays with owning elements

The existing `DynArray` representation now takes an element quantity:

- `DynArray<&2, T>` stores copyable `Data`. The existing `new_at`, `get_at`, `set_at`, `push_at`, `pop_at`, and other Data APIs remain available.
- `DynArray<T>` means `DynArray<&1, T>` and accepts any `Type`, including native arrays, nested dynamic arrays, and closures. The owning entry points have an `_owned` suffix.

Both use the same `DA{limit, depth, capacity, length, slots}` record and native `Base.Array` storage. This is a source-level type-annotation change for existing Data clients: write the explicit `&2`. It does not add a wrapper or alternate storage representation.

## Ownership API

| Operation | Behavior |
|---|---|
| `new_owned(~T)` / `with_limit_owned(~T, limit)` | Empty array; depth limit clamped to 31 |
| `length_owned` / `capacity_owned` | Return array and scalar |
| `push_owned(~T, array, value)` | Move value into the next slot; return rejected value on capacity failure |
| `pop_owned(~T, array)` | Move last value out and clear its slot |
| `swap_owned(~T, array, index, value)` | Replace a slot and return its previous value; reject out-of-bounds writes and return input value |
| `set_owned(~T, array, index, value)` | Replace a slot and drop the previous value; reject out-of-bounds writes and return input value |
| `update_owned(~T, ~R, array, index, f)` | Give `f` ownership of the element; `f: T -> T & R` must return a replacement and a result |
| `reserve_owned` | Retain contents while growing capacity; errors leave the array unchanged |
| `clear_owned` | Drop all elements, preserve capacity |
| `into_list_owned` | Consume array and move elements into a list in order |

There is no copying `get` for arbitrary Type elements. A callback can inspect or modify an owning element and return it. For example, an element that is itself an array can use its own get/set APIs inside that callback. `into_list_owned` deliberately consumes the container; it does not alias its values. A callback supplied to an invalid-index update is not invoked and is dropped, along with any captured resources. Bend is affine, so dropping values is permitted.

A rejected push/set/swap contains `Rejected{error, value}`. Successful swap returns `Some{old}` on every valid, densely populated array. `None` would indicate an externally constructed invalid representation. Constructors are visible in Bend; representation invariants apply to arrays built and manipulated through the public operations.

## Native implementation and performance limits

Stock Bend 2.0.16 lowers `Array.swap`/`Array.set` to indexed block reads/writes. Owning updates use swap-out / callback / swap-in; they do not clone the array. Pop writes an empty slot before returning the payload. Payloads remain live when returned to the caller and are released when subsequently dropped.

Empty owning buffers cannot use Base's `Array.new`, which requires a Data element. The owning initializer constructs fresh empty slots recursively. The emitted C merges blocks at each level, so this initializer currently costs **O(capacity * log(capacity))**, not O(capacity). Growth and clear inherit this cost. Ordinary indexed access remains O(1); ordinary push without growth and pop are O(1). Owning push is currently amortized O(log n), whereas the original Data specialization retains its prior behavior. This limitation is explicit; no custom compiler, generated-C edits, FFI, or unsafe cast bypasses it. A tree built on this API must account for this cost and be measured before replacing the current tree.

The existing Data push/get/set small-workload regression measurements remain essentially unchanged (about 1% variation). This is not an owning-element performance acceptance result. Raw measurements are in the accompanying evidence directory.

## Validation and exact proof coverage

- Native nested-array differential tests: 118 histories / 26,795 observations. Includes growth, reserve, failed writes returning their inputs, retained reads, replacement, pop, clear, and ordered drain.
- Native closure storage and extraction: the stored function returns the expected result.
- Existing Data driver: 107 deterministic/random histories pass.
- Existing Data universal operation/trace proofs remain intact, with their type annotations made explicit.
- `owned_swap.bend`: a checked, parametric theorem for **all Type elements** proves the actual `Array.swap.go` traversal is reversible at a fixed size/index: swap in a replacement, then restore the extracted element, and obtain the exact original array and replacement. The proof carries owning intermediate values in a dependent certificate rather than duplicating them.
- `owned.bend` supplies laws for initialization, rejected writes/updates, empty pop, the first push/pop/swap/update/drain, and clear metadata. `owned_instances.bend` explicitly checks these templates at native arrays, nested dynamic arrays, and closures. Template declarations alone are not counted as checked proofs.
- A broken push that omits the length increment is rejected by the instantiated proof gate. The checker also rejects attempts to duplicate either an owning array or its owning element.

**Not established yet:** universal public-operation/trace refinement for every arbitrary Type payload, the full native-array wrapper roundtrip (including recomputed size), and owning-element C performance acceptance. The fixed-size swap-traversal theorem does not by itself establish these larger claims. Native compiler/runtime correctness remains part of the trusted toolchain.

## Reproduce

```sh
bend proofs/dynamic_array.bend
bend tests/dynamic_array/owned.bend -o build/indexed-tree/owned-test
python3 tools/check_owned_array.py
python3 tools/check_owned_array_guards.py
bend tests/dynamic_array/owned_closure.bend -o build/indexed-tree/closure-test
build/indexed-tree/closure-test  # 12
```
