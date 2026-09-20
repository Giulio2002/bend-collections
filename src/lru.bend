import Base
import ../reference/lru/src/cache.bend as C
import ../reference/lru/src/driver.bend as D
import ../reference/lru/src/public.bend as Pub
import ../reference/lru/src/codec.bend as Codec
import ../reference/lru/spec/clock.bend as Clock

# Reuse entry for the retained LRU cache (reference/lru, immutable snapshot,
# commit 38d77f4053e33dfa4320b805bdf36e55d15ddc79; per-file sha256 pins in
# inventory/reference-sha256.json). Nothing here re-implements the cache.
#
# Usage (String keys, any Data value type V):
#   c = new_with_size(V, capacity, size)          -- Result: Fail{message} or Done{cache}
#   t = run(V, requests, cache, zero_key, zero_value, clock_events)
# where requests are reference Pub.Request values (Add, Get, Peek, Remove,
# Keys, Len, ...) and clock_events feed the explicit clock (Clock.Sample{ms}).
# Semantics, errors and the trusted TypeScript residue: reference/lru/README.md
# and docs/lru-compat.md. Theorems: proofs/lru.bend.

def new_with_size(-V: Data, +capacity: U32, +size: U32) -> Result<&2, &2, String, C.Cache<String, V>>:
  C.new_with_size(String, V, capacity, size)

def new(-V: Data, +capacity: U32) -> Result<&2, &2, String, C.Cache<String, V>>:
  C.new(String, V, capacity)

def run(-V: Data, requests: List<&2, Pub.Request<String, V>>, c: C.Cache<String, V>, +zero_key: String, +zero_value: V, events: List<&2, Clock.Event>) -> D.Trace<String, V>:
  D.run(~String, ~Codec.string_encode, V, requests, c, zero_key, zero_value, events)

def execute(-V: Data, +zero_key: String, +zero_value: V, c: C.Cache<String, V>, events: List<&2, Clock.Event>, request: Pub.Request<String, V>) -> D.Outcome<String, V>:
  D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)
