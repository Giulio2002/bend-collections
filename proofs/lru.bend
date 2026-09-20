import Base
import ../reference/lru/END_TO_END.bend as LRU
import ../reference/lru/src/cache.bend as C
import ../reference/lru/src/driver.bend as D
import ../reference/lru/src/public.bend as Pub
import ../reference/lru/src/codec.bend as Codec
import ../reference/lru/spec/cache.bend as S
import ../reference/lru/spec/clock.bend as Clock
import ../reference/lru/proofs/public_trace.bend as PT
import ../reference/lru/proofs/refinement.bend as Initial
import ../src/lru.bend as Entry

# The retained LRU's checked end-to-end theorems enter the PROOF.bend closure
# through this module (the whole reference END_TO_END is imported and checked
# under Bend 2.0.16). The reuse entry src/lru.bend is exactly the retained API.

def entry_new_with_size(-V: Data, +capacity: U32, +size: U32) -> {Entry.new_with_size(V, capacity, size) == C.new_with_size(String, V, capacity, size) : Result<&2, &2, String, C.Cache<String, V>>}:
  {==}

def entry_run(-V: Data, +requests: List<&2, Pub.Request<String, V>>, +c: C.Cache<String, V>, +zero_key: String, +zero_value: V, +events: List<&2, Clock.Event>) -> {Entry.run(V, requests, c, zero_key, zero_value, events) == D.run(~String, ~Codec.string_encode, V, requests, c, zero_key, zero_value, events) : D.Trace<String, V>}:
  {==}

# Retained public trace law, restated for the reuse entry: every accepted
# construction and every request/clock-event list refines the LRU spec.
def entry_string_trace(-V: Data, +zero_key: String, +zero_value: V, +capacity: U32, +size: U32, +requests: List<&2, Pub.Request<String, V>>, +events: List<&2, Clock.Event>) -> PT.created_rel(V, zero_key, zero_value, requests, events, Entry.new_with_size(V, capacity, size), S.new_with_size(String, V, capacity, size)):
  LRU.public_string_trace(V, zero_key, zero_value, capacity, size, requests, events)

def entry_initialization(-K: Data, -V: Data, +capacity: U32, +size: U32) -> {Initial.abstract_created(K, V, C.new_with_size(K, V, capacity, size)) == S.new_with_size(K, V, capacity, size) : Result<&2, &2, String, S.Model<K, V>>}:
  LRU.public_initialization(K, V, capacity, size)
