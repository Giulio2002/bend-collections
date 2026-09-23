import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T

def item(-K: Data, -V: Data, step: C.Step<K, V>) -> Maybe<&2, T.Entry<K, V>>:
  C.Out{cache, result, flag, events} = step
  result

# Recency and hit accounting cannot change any lookup.
law live_lookup:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for tracked: Bool
  for query: String
  {C.lookup(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, tracked)), query) == C.lookup(K, V, c, query) : Maybe<&2, T.Entry<K, V>>}
def live_lookup(K, V, c, code, entry, tracked, query):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law miss_lookup:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for query: String
  {C.lookup(K, V, P.finish_miss(K, V, c, True{}), query) == C.lookup(K, V, c, query) : Maybe<&2, T.Entry<K, V>>}
def miss_lookup(K, V, c, query):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law live_item:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  {item(K, V, C.read_live(K, V, c, code, entry, True{})) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
def live_item(K, V, c, code, entry):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for found: Maybe<&2, T.Entry<K, V>>
  for decision: {C.lookup(K, V, c, code) == found : Maybe<&2, T.Entry<K, V>>}
  {C.lookup(K, V, C.step_cache(K, V, P.refresh_prepare_found(K, V, c, code, found)), code) == item(K, V, P.refresh_prepare_found(K, V, c, code, found)) : Maybe<&2, T.Entry<K, V>>}
def prepare_found(K, V, c, code, found, decision):
  match found:
    case None{}:
      Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, P.finish_miss(K, V, c, True{}), code), C.lookup(K, V, c, code), None{}, miss_lookup(K, V, c, code), decision)
    case Some{+entry}:
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, item(K, V, C.read_live(K, V, c, code, entry, True{})), Some{entry}, live_item(K, V, c, code, entry)) : {C.lookup(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, True{})), code) == _ : Maybe<&2, T.Entry<K, V>>}
      Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, True{})), code), C.lookup(K, V, c, code), Some{entry}, live_lookup(K, V, c, code, entry, True{}, code), decision)

# Arbitrary actual preparation returns the binding still stored in its output
# state. No validity, expiration or assumed successful-transport premise.
law prepare:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  {C.lookup(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code) == item(K, V, P.refresh_prepare(K, V, c, code)) : Maybe<&2, T.Entry<K, V>>}
def prepare(K, V, c, code):
  prepare_found(K, V, c, code, C.lookup(K, V, c, code), {==})

law successful_prepare:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for returned: {item(K, V, P.refresh_prepare(K, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {C.lookup(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
def successful_prepare(K, V, c, code, entry, returned):
  Equal.trans(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code), item(K, V, P.refresh_prepare(K, V, c, code)), Some{entry}, prepare(K, V, c, code), returned)

def flag(-K: Data, -V: Data, step: C.Step<K, V>) -> Bool:
  C.Out{cache, result, success, events} = step
  success

law live_flag:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  {flag(K, V, C.read_live(K, V, c, code, entry, True{})) == Maybe.is_some(&2, T.Entry<K, V>, item(K, V, C.read_live(K, V, c, code, entry, True{}))) : Bool}
def live_flag(K, V, c, code, entry):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law found_flag:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for found: Maybe<&2, T.Entry<K, V>>
  {flag(K, V, P.refresh_prepare_found(K, V, c, code, found)) == Maybe.is_some(&2, T.Entry<K, V>, item(K, V, P.refresh_prepare_found(K, V, c, code, found))) : Bool}
def found_flag(K, V, c, code, found):
  match found:
    case None{}: {==}
    case Some{entry}: live_flag(K, V, c, code, entry)

law prepare_flag:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  {flag(K, V, P.refresh_prepare(K, V, c, code)) == Maybe.is_some(&2, T.Entry<K, V>, item(K, V, P.refresh_prepare(K, V, c, code))) : Bool}
def prepare_flag(K, V, c, code):
  found_flag(K, V, c, code, C.lookup(K, V, c, code))
