# Callback-free single-threaded Bend LRU

A Bend LRU cache that reproduces the single-threaded observable behaviour of
elastic/go-freelru at `3a0a715f3309fbbaed5d9afd402d53ff5e1efd81` with callbacks
disabled. Keys are looked up in Bend's native `Base` `Map`. There is no custom
hash, hash table or AESENC.

Callbacks are excluded by the user's latest scope and frozen
[callback-exclusions.json](callback-exclusions.json). Neither the TypeScript
facade nor the Bend public machine exposes SetOnEvict. There is no no-op
registration method and no user eviction-function dispatch. Every constructed
state has the legacy callback flag false, and every reachable state keeps it
false; this is proved in `public_string_request_safe` and the trace theorems.
The Go reference is always constructed with a nil eviction callback. Historical
callback evidence is archived in tests/new/callback-archive.json. It counts as
neither passing coverage nor a completion blocker.

## API adaptation map

All frozen api.manifest.json declarations are mapped below. Every command goes
through the single behaviour implementation `src/public.bend`
(`start`/`resume`/`abandon`). Generic constructors take a key codec instead of
an upstream hash callback.

| Go declaration | Bend request / public adapter | Observable behavior and adaptation |
| --- | --- | --- |
| `New` | `C.new(K,V,capacity:U32)` / `new LRU(capacity,codec,clock,zeroKey,zeroValue)` | Hash-free. Capacity must be positive. The reserved maximum is rejected through the size rule. |
| `NewWithSize` | `C.new_with_size` / final constructor `size` argument | Checks zero capacity, size `0xffffffff` and size below capacity, in upstream order with upstream messages. U32 enforces input width. Size is a **nonbinding storage hint**: no buckets are allocated. |
| `SetLifetime` | `SetLifetime{ns}` / `SetLifetime` | Sets the default signed nanosecond duration. Existing deadlines are unchanged. |
| `Len` | `Len{}` / `Len` | Counts stored entries, including expired ones. No clock read and no expiry. |
| `AddWithLifetime` | `AddWithLifetime{k,v,ns}` / `AddWithLifetime` | Replacement ignores the previous expiry, keeps the stored original key, and updates recency and deadline. Increments Inserts. An insert into a full cache evicts the oldest entry (counted before the clock read). Returns true only for that eviction. |
| `Add` | `Add{k,v}` / `Add` | Uses the configured default lifetime. |
| `Get` | `Get{k}` / `Get` | An expired entry is removed (Removals) before the miss. A hit moves the entry to newest. Updates Hits/Misses. |
| `GetAndRefresh` | `GetAndRefresh{k,ns}` / `GetAndRefresh` | Finds without an expiry check, so it also revives expired entries. Counts the hit and moves to newest, then sets the new deadline. |
| `Peek` | `Peek{k}` / `Peek` | Checks expiry. No recency movement and no hit/miss counts. |
| `Contains` | `Contains{k}` / `Contains` | Same expiry/removal semantics as Peek. |
| `Remove` | `Remove{k}` / `Remove` | Removes even an expired entry. Increments Removals. |
| `RemoveOldest` | `RemoveOldest{}` / `RemoveOldest` | Removes the oldest entry regardless of expiry. Returns key/value/flag, with caller-supplied zero key/value when empty. |
| `GetOldest` | `GetOldest{}` / `GetOldest` | Peek semantics. **Retains the oldest key on an expired miss** (lru.go:561), with the zero value and false. |
| `Keys` | `Keys{}` / `Keys` | First removes the expired *oldest prefix* (one clock sample per finite oldest entry inspected). Then returns original keys, oldest first. |
| `Values` | `Values{}` / `Values` | Same expiry prefix as Keys, then values oldest first. |
| `Purge` | `Purge{}` / `Purge` | Empties the cache and zeroes all metrics. Natively this replaces the table with `Map.new`. Observably it equals upstream's remove-all-then-reset. |
| `PurgeExpired` | `PurgeExpired{}` / `PurgeExpired` | Examines only the oldest entry. Stops at a future finite deadline and never advances past an immortal oldest entry. No global expired-entry scan. |
| `Metrics` | `Metrics{}` / `Metrics` | Inserts, Evictions, Removals, Hits, Misses. **Collisions is a reserved zero (not applicable)**: native Map has no Go hash buckets. Reference comparisons project out only this storage-dependent field. Counters wrap modulo 2^64. |
| `ResetMetrics` | `ResetMetrics{}` / `ResetMetrics` | Returns the prior counters, then zeroes them without altering contents or recency. |
| `PrintStats` | `Diagnostics{}` / `Diagnostics`, `PrintStats` | Describes the actual Base Map crit-bit storage: leaf count (`Map.size`, proved equal to the number of entries), recency length, capacity and metrics. Collisions is reported as not applicable. There are no invented Go bucket, collision-percentage, allocation or speed statistics, and the output format intentionally differs. |

## Keys and codecs

`Cache<K,V>` stores the original key inside each entry. The encoded `String`
code is the `Map` key and the element of the bounded, oldest-first recency list.
Lookups use **Map.get**, writes **Map.set** and removals **Map.del**. There is
no second map underneath.

Built-in codecs (`src/codec.bend`), all with checked round-trip and injectivity
laws:

- `string_encode`: the identity on the full Base String domain, including the
  empty string and embedded zero characters.
- `word64_encode` (= `word_encode(64n, ·)`): 64 characters `'0'`/`'1'`, least
  significant bit first. The adapter's `uint64Codec` and `int64Codec` (two's
  complement) run the Bend machine at key type `Word(64n)` with this codec.
- `integer_encode` for the canonical signed `T.Integer`: `Positive(n)` is n and
  `Negative(n)` is -(n+1), so zero is unique. The encoding is unary, i.e.
  O(magnitude) long (a key of magnitude m is an m-character string, so Map
  paths and code comparisons cost O(m)). It has a full end-to-end theorem but
  is proof-level only: the adapter uses the Word64 codecs for integers.

The specification compares keys with an independent key equality `same`: String
equality for String, and the structural `integer_equal`/`bits_equal` in
`spec/keys.bend`. These equalities are proved sound and reflexive
(`spec_*_equality_sound/reflexive`). For each built-in codec it is proved that
String equality of codes equals `same` (`proofs/key_equality.bend`). Distinct
user keys are therefore never collapsed. A custom codec obtains the same
end-to-end theorem (`PublicKeys.from_construction`) by discharging two stated
contracts: codec injectivity (`inj`) and agreement of the chosen key equality
with code equality (`agree`).

String keys must be Unicode scalar strings: zeros and empty strings are
accepted, unpaired surrogates are rejected (`H.string_key`, proved against
`spec/host.bend` `scalar`). That is a subset of the formal Base String domain.

## Storage and costs

The installed Map is a crit-bit tree (`MTip`, `MLeaf`, `MNode`). Its bit stream
has one presence bit plus 32 character bits per position, which distinguishes a
zero character from string termination. Costs of the actual representation:

- Map get/set/del: proportional to tree depth plus key length.
- Recency maintenance is a list, so Add, hits and removal scan up to capacity
  entries (`without`) and append walks the list.
- Len is `List.length` of the recency list, O(capacity).
- Keys/Values do one Map lookup per recency entry.
- Host conversion of a 64-bit integer: 64 exact halvings of its decimal digit
  list (about 20 digits), and 64 digit-list doublings to render it back.

No O(1), Go GC, allocation or speed parity is claimed. Stored metadata is
bounded by capacity (proved invariant). No history or event log is retained.

## Clock and time model

Time samples are signed int64 milliseconds. Durations are signed int64
nanoseconds, divided by one million with truncation toward zero. Addition wraps
at 64 bits. A zero deadline is immortal, and a finite deadline expires when
`deadline <= now`. Counters wrap as uint64. These are the pinned upstream
semantics, proved against `spec/numeric.bend`.

The clock is requested only at the operation points upstream reads it:
- Add: after room is made.
- Reads: only for a present finite-deadline entry.
- Refresh: after the hit is counted.
- Keys/Values/PurgeExpired: once per inspected finite oldest entry.

If the provider throws or returns an invalid sample, the command fails. Effects
completed before the request are retained exactly as specified (an eviction
before Add's sample, a refresh's hit and recency move, completed expiry
removals), and the original error propagates. Missing, malformed, out-of-range
or failed transport is never a cache success. The clock must not re-enter or
mutate the cache.

```ts
import {LRU, stringCodec} from './src/adapter.ts';
const cache = new LRU(2n, stringCodec, () => 1000n, '', 0n);
cache.AddWithLifetime('key', 42n, 1000000n);
cache.Get('key'); // [42n, true]
```

Run TypeScript using Bun with the installed Bend preload
(`bun --preload ~/.bend/current/bend2/main.ts file.ts`).

## Execution path and proof composition

The host boundary is Bend code in `src/host.bend`; `src/adapter.ts` only calls it:

- Integers cross the JS/Bend boundary as decimal text: `String(bigint)` into
  Bend, `BigInt(text)` out of Bend. They cannot cross as Bend `Nat`, because a
  compiled Bend `Nat` holds at most 2^48−1, so a 64-bit value does not fit.
- `H.uint64_key`, `H.int64_key`, `H.time` and `H.create` parse and range-check
  the text and build the `Word(64n)`/`Word(32n)` value. They split a decimal
  digit list into bits by exact halving, then check that nothing is left over.
  Rejections are Bend `Fail{message}` values, which the adapter throws as
  `RangeError(message)`.
- `H.string_key` accepts exactly the strings of Unicode scalar values.
- `H.uint64_text` and `H.int64_text` render words back as decimal text.
- A request runs as `H.begin(codec.encode, zeroKey, zeroValue, state, request)`.
  While the action is `Ask`, the adapter calls the clock provider once:
  - a returned value becomes `H.sample(text)`, which is a `Sample` or an
    `InvalidSample`;
  - a thrown exception becomes `H.thrown()`.

  `H.answer` (which is `D.advance`) then resumes or stops. The resulting
  `Return` or `Raise` action carries the state that the adapter adopts
  unchanged.

END_TO_END.bend (imported by PROOF.bend) exposes, universally quantified:

- `public_initialization` and constructor error facts.
- `public_string_request`: every request, from every represented,
  callback-disabled String-key state and every provider event list, is related
  to the independent typed semantics `PublicSpec.execute`. The relation fixes the
  exact reply or error, the exact unused events and request count, and a
  canonically equal abstract finite map with exact recency, lifetime and
  metrics. Per-operation instances (`public_string_add`, `…_keys`, …) are also
  exposed.
- `public_string_request_safe`: after every request (success or retained
  failure state), the full representation invariant holds and callbacks stay
  disabled. This covers the capacity bound, unique recency, recency/Map key-set
  equality, Map crit-bit shape and key identity.
- `public_string_trace`: for every capacity/size input, request list and event
  list, construction either fails with the independent error or yields an
  actual trace whose final state, unused events, request count and every
  per-request outcome refine `Traces.run`.
- `public_integer_trace`, `public_word64_trace`: the same arbitrary-trace
  refinement for `T.Integer` and `Word(64n)` keys against the independent
  K-keyed specification (`Keys.integer_same` / `Keys.word64_same`).
  - Replies, including returned keys, are compared exactly at the key type.
  - States are compared canonically after renaming keys to their codes.
  - Both are proved by transporting the String theorem along two proved
    renamings: one of the actual machine (`proofs/rename_map.bend` for every
    Map operation, `proofs/rename_machine.bend` for the cache, public machine
    and driver), and one of the specification (`proofs/rename_spec.bend`).
- Host boundary, against the independent `spec/host.bend` (positional decimal
  numerals, width-bit range as the round trip `unsigned(from_nat(v)) == v`,
  and two's complement −(k+1) = ¬k):
  - `host_uint64_key`, `host_int64_key`: each reader accepts exactly the
    in-range numerals, yields the specified word, and rejects everything else.
    `host_unsigned_word` and `host_signed_word` state the same for every width.
  - `host_uint64_text`, `host_int64_text`: each rendered text reads back as the
    word's value.
  - `host_uint64_roundtrip`, `host_int64_roundtrip`: key identity through the
    text.
  - `host_time`, `host_sample`, `host_thrown`, `host_create`,
    `host_string_key`: the remaining boundary functions.
  - `host_fits_meaning` (v < 2^n implies fits) and `host_fits_bound` (fits
    implies v < 2^n): together they show the round-trip range condition
    `fits(n, v)` holds exactly when `v < 2^n`, so out-of-range numerals are
    rejected, never wrapped.
  - `host_loop_drive`, `host_loop_string`, `host_loop_word64`: the loop
    `begin`, then `answer` once per provider event, adopting the result, is
    `D.drive` and `D.execute` over the sequence of events the provider produced.
    `D.execute` is the machine in every trace theorem above.
- `drive_finished`, `drive_advance`: unfolding lemmas that show `D.drive`
  iterates `D.advance`. These are facts about the Bend driver only.
- Numeric laws: 64-bit addition and increment, signed duration division,
  deadline arithmetic, and native limb packing and decoding.

Specifications in `spec/` import only neutral datatypes (`types/model.bend`,
`spec/clock.bend`, `spec/numeric.bend`), never `src/` or `proofs/`.

## Trust boundary

Trusted (not proved):
- The unmodified Bend 2.0.5 checker and the primitive Base semantics. Base Map
  algorithms are *not* trusted: their get/set/del/size/keys/to_list laws are
  proved against the installed definitions.
- The compiler, the runtime (Bun) and the hardware, which are separate from the
  functional claim. This includes the JS runtime's decimal text conversions
  `String(bigint)` and `BigInt(text)`. `tests/new/host_bridge.ts` checks the
  whole boundary against independent JS oracles, with every edge case and
  2,000 pseudo-random 64-bit values.
- The residue of `src/adapter.ts`:
  - calling the clock provider and catching its exception;
  - the 8-line loop that passes the provider's event to `H.answer` while the
    action is `Ask`, then adopts the carried state;
  - identity passing of Bend values;
  - constructor-tag checks.

  The loop is the one `HostLoop.loop` models. `tests/new/clock_failures.ts`
  checks failure propagation and retained states. `Date.now()` is the default
  clock. `tools/validate.py` (full_scope) rejects any arithmetic, shift, mask,
  width reduction or `Number` conversion in the adapter. It also rejects any
  Bend call that no END_TO_END law covers, and it self-tests that injected
  arithmetic is rejected.

Checker caveat: Bend's static `~` parameters are specialized at each use, and a
`~`-generic definition checked alone is not meaningful. Every generic lemma
used here is therefore instantiated with concrete static arguments inside the
PROOF.bend closure: String, `T.Integer`/`integer_encode`, and
`Word(64n)`/`word64_encode`. `tools/validate.py` mutation checks confirm that
the instantiations are rejected when an implementation or specification
changes.

## Validation

`tools/validate.py --report build/validation.json` runs:
- all 12 upstream test groups, ported with an exact assertion inventory
  (excluded callback assertions are listed individually, never counted as
  passes);
- the PROOF.bend checker and spec template smoke tests;
- boundary, clock-failure and host-bridge checks, plus the full_scope
  composition gate described above;
- stateful differential traces against pinned Go through a transparent
  time-controlling reference adapter, with String, int64 and uint64 keys
  including extremes (expected results never reach the Bend backend);
- numeric boundaries;
- implementation and specification mutation checks, each rejected at its named
  proof location;
- transport rejection checks.

The frozen acceptance command is
`/Users/monkeair/auto-implementer/.venv/bin/python automation/acceptance.py`.
PROOF_STATUS.md lists the obligation table; WORK_LOG.md has the checkpoints.
