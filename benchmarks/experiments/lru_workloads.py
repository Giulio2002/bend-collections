"""Additive `lru.*` workload rows, prepared for operator review (CORRECTED).

Nothing here is read by `benchmarks/run.py`. Applying it means appending the
body of `rows(...)` below to `benchmarks/workloads.py` after the `graph`
block (append-only; no existing row, helper or threshold changes). The
helpers it calls are the ones defined there, with the same meaning.

This revision answers the operator rejection of 2026-09-21:

* the C reference is REBUILT (benchmarks/native/lru.c): open-addressing hash
  + intrusive indexed doubly linked recency list, O(1) touch/evict/remove,
  uint32 keys with no partially initialised buffer;
* purge and resize are WHOLE-ROUND rows (`grow='reps'`), because the
  default classification in `growth()` would have made them size-preserving
  ('count') rows, whose longer batches would re-purge an already EMPTY cache
  and re-resize an already shrunk one;
* even in whole rounds, region A runs 2k and region B k operations, so a
  plain purge row would isolate purges of an empty cache (A - B = the purges
  after the first). The measured purge/resize are therefore RESTORING PAIRS
  that put the full cache back after every call, so EVERY measured purge
  empties a full cache of `size` entries and EVERY measured resize really
  evicts; the plain no-op cases are separate, explicitly labelled
  `edge-empty` rows;
* `new` performs observable construction: it constructs a cache of capacity
  `size` through the validating constructor and folds the constructed
  cache's capacity and length (and the rejection code for capacity 0).

---------------------------------------------------------------- selectors

`benchmarks/bend/lru.bend` and `benchmarks/native/lru.c` take the identical
argv `[op, size, count, reps, seed, order]` like every other pair, draw every
argument from the identical LCG `s*1664525 + 1013904223` and fold every
result into the identical checksum `c*31 + v`. A round builds a cache of
capacity max(size, 1) holding keys 0 .. size-1 (Bend: the one-character
String Chr{65536 + i}; C: the uint32 i), value i+1, oldest first, and settles it by
folding its key list. Keyed operations use i = lcg % (size + 1).

     0  add            insert/replace i; folds 1 if an entry was evicted
     1  get            touches, counts hit/miss; folds the value or 0
     2  peek           no touch, no metric; folds the value or 0
     3  contains       folds 1 or 0
     4  remove         plain removal (edge row only); folds value or 0
     5  purge          plain purge (edge row only); folds the count
     6  resize         plain resize to i (edge row only: resize(0) fails)
     7  keys           folds every key, oldest first
     8  len            folds the length
     9  new            constructs a cache of capacity `size`; folds its
                       capacity and length, or 2^32-1 when rejected
    10  remove + add   restoring pair for `remove` (COMPOSITE)
    11  purge + refill restoring pair for `purge`: purges the FULL cache
                       (folds the count, always `size`), re-adds 0 .. size-1
    12  resize + back  restoring pair for `resize`: shrinks to
                       t = 1 + lcg % size (folds t and the evictions, which
                       average size/2), grows back to `size` (folds 0), and
                       re-adds exactly the evicted keys (both drivers track
                       the rotation offset of the recency order)
    13  capacity       folds the capacity
    14  set_lifetime   sets the lifetime to the drawn nanosecond count; folds
                       it and the length
    15  metrics        folds the five 64-bit counters (ten U32 limbs)
    16  expiry         the round sets a one millisecond lifetime ONCE, before
                       the measured region; every step then adds key i at
                       stamp 0 (deadline 1) and gets it back at stamp 2, so
                       the read finds the entry EXPIRED, drops it (a removal)
                       and answers a miss. This is the expiry path of `read`,
                       which no other selector reaches. COMPOSITE (add + get).
    17  remove_seq     ISOLATED removal: step j removes key (o + j) mod cap,
                       a distinct key that is still present. Used only with
                       count = size / 2, so region A's 2 x count removals are
                       exactly the full sweep of the cache the round prepared
                       and region B's are its first half: the difference is
                       count removals of live entries from a nonempty cache,
                       with no re-insertion inside the measured region.
    18  purge (pool)   ISOLATED purge: every region builds the SAME pool of
                       2 x (the ROW's count) independent full caches, so the
                       whole preparation cancels in A - B; region A then
                       purges 2k of them and region B k, and every measured
                       purge empties a freshly prepared FULL cache. No purge
                       ever runs on an already emptied cache.
    19  resize (pool)  ISOLATED shrink over the same pool: cache j is resized
                       to 1 + lcg mod cap, folding the target and the
                       evictions. Every measured resize really evicts.
     _  null           value-stream step (the A/B/C control)

Every round ends with the same drain on both sides: sixteen peeks, the
length, and the low and high 32-bit halves of the five 64-bit metrics
(inserts, evictions, removals, hits, misses), so metric bookkeeping is
checked too.

--------------------------------------------------- size-changing behaviour

    operation  selector  growth  why
    add        0         count   full cache: an insertion evicts; size kept
    get        1         count   read
    peek       2         count   read
    contains   3         count   read
    remove     10        count   restoring pair (method='pair')
    purge      11        reps    whole rounds; the pair restores the cache
    resize     12        reps    whole rounds; the pair restores the cache
    keys       7         count   read
    len        8         count   read
    new        9         count   independent of the round's cache

The pair's time is charged to purge/resize, which over-charges BOTH sides by
the refill (size adds for purge, ~size/2 for resize). The refill is the same
work on both sides, so the ratio is not flattered; it is recorded next to
the row in docs/C_EQUIVALENCE.md. These composite rows are KEPT, explicitly
labelled `purge+refill` / `resize+refill`, and they are no longer the only
evidence: selectors 17, 18 and 19 measure the destructive operations in
isolation on independently prepared, nonempty states.

--------------------------------------------- isolation of destructive calls

    operation           selector  isolation
    remove              17        the round's own full cache, swept once;
                                  count = size / 2 so region A is exactly the
                                  sweep and no removal misses
    purge               18        one freshly built full cache per call, from
                                  a region-independent pool of 2 x count
    resize (shrink)     19        the same pool; every call evicts

The preparation of the pool costs more than the operation it isolates, and it
is paid in EVERY region, so it cancels in A - B but inflates both terms: the
pooled rows therefore need long regions and modest sizes to stay above the
harness's noise floor. That is the price of isolation and it is why the
composite rows are kept alongside them rather than replaced.

------------------------------------------------------ checksum equivalence

`python3 tools/lru_diff.py` builds the Bend driver, the C reference with the
benchmark flags and the C reference with -fsanitize=address,undefined, and
requires the three region checksums of every selector, over a grid of sizes,
counts, seeds and both region orders, to agree bit for bit.
"""


def rows(add, three, pair, empties, SIZE_CHANGING_FULL):
    """Append-only body. `add`, `three`, `pair`, `empties` and
    `SIZE_CHANGING_FULL` are the helpers/sets of benchmarks/workloads.py,
    unchanged except that two NEW operation names are added to the set."""

    # purge/resize and every isolated destructive row are whole-round rows
    # (see the module docstring)
    SIZE_CHANGING_FULL.update({'lru.purge', 'lru.resize', 'lru.remove_seq',
                               'lru.purge_isolated', 'lru.resize_isolated',
                               'lru.expiry'})

    LRU = (64, 4096, 262144)
    LRUF = (100000, 50000, 20000)

    three('lru', 'add', 0, LRU, LRUF)
    three('lru', 'get', 1, LRU, LRUF)
    three('lru', 'peek', 2, LRU, LRUF)
    three('lru', 'contains', 3, LRU, LRUF)
    pair('lru', 'remove', 10, LRU, LRUF)
    three('lru', 'purge', 11, LRU, (2000, 40, 2))
    three('lru', 'resize', 12, LRU, (4000, 80, 4))
    three('lru', 'keys', 7, (64, 4096, 32768), (20000, 500, 40))
    three('lru', 'len', 8, LRU, (200000, 200000, 200000))
    add('lru', 'new', 9, 'small', 64, 200000)
    add('lru', 'new', 9, 'medium', 4096, 200000)
    add('lru', 'new', 9, 'large', 262144, 50000)
    three('lru', 'capacity', 13, LRU, (200000, 200000, 200000))
    three('lru', 'set_lifetime', 14, LRU, (200000, 200000, 200000))
    three('lru', 'metrics', 15, LRU, (50000, 50000, 50000))
    three('lru', 'expiry', 16, LRU, (50000, 50000, 20000))

    # isolated removal: count = size / 2 (the `sized` rule of
    # benchmarks/workloads.py), so region A is exactly one full sweep
    for label, size in zip(('small', 'medium', 'large'), LRU):
        add('lru', 'remove_seq', 17, label, size, max(1, size // 2))

    # isolated purge / shrink over a region-independent pool of 2 x count
    # full caches; the sizes and counts are bounded by the pool's memory
    POOL = (64, 1024, 4096)
    POOLC = (200, 20, 8)
    three('lru', 'purge_isolated', 18, POOL, POOLC)
    three('lru', 'resize_isolated', 19, POOL, POOLC)

    empties('lru', [('new', 9), ('add', 0), ('get', 1), ('peek', 2),
                    ('contains', 3), ('remove', 4), ('purge', 5),
                    ('resize', 6), ('keys', 7), ('len', 8),
                    ('capacity', 13), ('set_lifetime', 14), ('metrics', 15),
                    ('expiry', 16)], 100000)


def table():
    """The rows this proposal adds, built with a private copy of the helpers
    (for review and for tools that want to measure them outside run.py)."""
    import importlib.util
    import pathlib
    here = pathlib.Path(__file__).resolve().parent.parent / 'workloads.py'
    spec = importlib.util.spec_from_file_location('_wl', here)
    wl = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wl)
    start = len(wl.TABLE)
    rows(wl.add, wl.three, wl.pair, wl.empties, wl.SIZE_CHANGING_FULL)
    return wl.TABLE[start:]


if __name__ == '__main__':
    for r in table():
        print('%-14s %-11s op=%-2d size=%-6d count=%-6d grow=%-5s method=%s'
              % (r['operation'], r['workload'], r['op'], r['size'], r['count'],
                 r['grow'], r['method']))
