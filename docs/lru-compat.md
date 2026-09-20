# Retained LRU on Bend 2.0.16: compatibility record

Source: `reference/lru` (immutable). Provenance: commit
`38d77f4053e33dfa4320b805bdf36e55d15ddc79` (`inventory/structures.json`, `reuse.lru`).
Per-file pins: `inventory/reference-sha256.json` (307 files, all verified before use).
Its original evidence (`reference/lru/evidence/*`, `VALIDATION.json`) was produced with
Bend 2.0.5. That evidence is **not** taken as proof of 2.0.16 compatibility. Everything
below was re-run with the pinned 2.0.16 binary (`inventory/toolchain.json`).

## Results (re-run with `python3 tools/lru_compat.py`)

| Entry | 2.0.16 result |
|---|---|
| `reference/lru/PROOF.bend` | `All terms check, with 1180 unsafe annotations.` |
| `reference/lru/END_TO_END.bend` | `All terms check, with 1180 unsafe annotations.` |
| `bend reference/lru/PROOF.bend --checkup` | END_TO_END import checks |
| each of the 236 `.bend` files checked as its own root | 232 check; 4 fail (below) |

The per-file table is `docs/lru-compat-modules.tsv`.

### "unsafe annotations"
The retained closure contains **no** `@unsafe` def: the gate regex finds none in the
234-file END_TO_END closure. The checker's count is computed (in the 2.0.16 binary) as
`t.u === true || k.includes("~")`. `~` names are template instantiations. Instances are
parsed with the template's own unsafe flag (false here), and the termination check
(`lhs.u !== true`) applies to them. The 1180 are therefore template instances, not
termination escapes. Our own closure reports its count the same way. `tools/validate.py`
separately checks that no `@unsafe` text occurs in the closure.

### Four files that fail only as standalone roots
| File | Error on 2.0.16 when it is the root file |
|---|---|
| `types/model.bend` | `duplicate declaration: Event`. Base 2.0.16 now declares `Event` (window events); a root file shares Base's namespace. |
| `spec/clock.bend` | same `Event` clash |
| `spec/public_commands.bend` | same kind of clash with a Base constructor name (`Boolean`) |
| `proofs/rename_map.bend` | parse error at `+keys = ...` in the imported `invariants.bend` template instance when this file is the root |

All four are inside the END_TO_END closure, and that closure **does** check. Imported
modules are namespaced by their alias, so the clashes do not occur there. None of the four
is modified or ported. We import only through `reference/lru/END_TO_END.bend` and
individual proof modules that check.

## What we reuse
* `proofs/lru.bend` imports `reference/lru/END_TO_END.bend`. The whole checked LRU closure
  (`public_string_trace`, `public_initialization`, the Integer/Word64 traces, native Map
  laws) is thus in `PROOF.bend`'s closure. It is re-checked on every run.
* `src/lru.bend` is the reuse entry: thin, checked aliases of the retained public driver
  (`D.run`, `C.new_with_size`, request constructors). `proofs/lru.bend` proves by
  reflexivity that the aliases are exactly the retained functions.
* Native Map lemmas (`proofs/lib/map.bend`) are re-exported from the retained
  `map_insert.set_same`, `map_set_frame.other_lookup_unchanged`,
  `map_set_critbit.preserves_critbit`, delete frame/critbit laws, key membership and
  key uniqueness. They are not re-derived.
* Word/U32 interpretation lemmas (`proofs/lib/u32.bend`) reuse the retained
  `word_comparison.u32_lt`, `subtraction_bounds.u32_exact`, `word_shift.exact`,
  `modular_addition.increment_refines/reconstruct`, `word_value.from_nat_value` and
  `numeric.primitive_word_interpretation`.

No reference file was ported or copied, because every needed module checks on 2.0.16
inside its closure. The acceptance gate re-verifies all 307 reference hashes.

## Trust boundary of the retained LRU (unchanged, not upgraded by this project)
From `reference/lru/README.md` "Trust boundary" and `PROOF_STATUS.md`. `reference/lru/PROOF.bend`
begins with "Checked partial claims only". The retained project's own status file
lists what its laws cover. Still trusted (not proved):
* the TypeScript residue of `reference/lru/src/adapter.ts` (clock provider call, exception
  capture, the 8-line host loop, identity passing, constructor-tag checks);
* the JS runtime's decimal conversions `String(bigint)`/`BigInt(text)`;
* the checker, the compiler, the runtime and the hardware.

The new data structures neither call nor include that TypeScript. They are pure Bend,
and host code is used only by the Python test driver.
