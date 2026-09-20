import Base
import ../src/cache.bend as C
import ../types/model.bend as T
import ../src/codec.bend as Codec
import ./invariants.bend as Inv

# Renaming the original keys stored in native table VALUES through a codec.
# Map keys (the encoded codes), tree shape and discriminators are untouched,
# so every Base Map operation commutes with the renaming. These are laws about
# the actual Base Map definitions (get/set/del/size/keys/to_list).

def rn_entry(~K: Data, ~enc: K -> String, -V: Data, e: T.Entry<K, V>) -> T.Entry<String, V>:
  T.Item{k, v, d} = e
  T.Item{enc(k), v, d}

def rn_item(~K: Data, ~enc: K -> String, -V: Data, m: Maybe<&2, T.Entry<K, V>>) -> Maybe<&2, T.Entry<String, V>>:
  match m:
    case None{}: None{}
    case Some{e}: Some{rn_entry(~K, ~enc, V, e)}

def rn_map(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> Map<&2, Maybe<&2, T.Entry<String, V>>>:
  match m:
    case MTip{}: MTip{}
    case MLeaf{k, v}: MLeaf{k, rn_item(~K, ~enc, V, v)}
    case MNode{p, lo, hi}: MNode{p, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi)}

# ---------------------------------------------------------------------------
# Lookup.
def lo_value(-K: Data, -V: Data, +p: Nat, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, T.Entry<K, V>>) -> {C.lookup_result(K, V, Map.lo(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p, hi, r0)) == C.lookup_result(K, V, r0) : Maybe<&2, T.Entry<K, V>>}:
  (m, r) = r0
  {==}

def hi_value(-K: Data, -V: Data, +p: Nat, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, T.Entry<K, V>>) -> {C.lookup_result(K, V, Map.hi(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p, lo, r0)) == C.lookup_result(K, V, r0) : Maybe<&2, T.Entry<K, V>>}:
  (m, r) = r0
  {==}

def get_leaf(~K: Data, ~enc: K -> String, -V: Data, +v: Maybe<&2, T.Entry<K, V>>, r: (String & String) & Cmp) -> {C.lookup_result(String, V, Map.get.leaf(Maybe<&2, T.Entry<String, V>>, None{}, rn_item(~K, ~enc, V, v), r)) == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get.leaf(Maybe<&2, T.Entry<K, V>>, None{}, v, r))) : Maybe<&2, T.Entry<String, V>>}:
  ((key2, k2), c) = r
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def get_bit(~K: Data, ~enc: K -> String, -V: Data, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, +p2: Nat, kb: String & Bool, ih_lo: @+k: String -> {C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), k)) == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, lo, k))) : Maybe<&2, T.Entry<String, V>>}, ih_hi: @+k: String -> {C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, hi), k)) == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, hi, k))) : Maybe<&2, T.Entry<String, V>>}) -> {C.lookup_result(String, V, Map.get.bit(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), p2, kb)) == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get.bit(Maybe<&2, T.Entry<K, V>>, None{}, lo, hi, p2, kb))) : Maybe<&2, T.Entry<String, V>>}:
  (+key2, b) = kb
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup_result(String, V, Map.lo(&2, Maybe<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, p2, rn_map(~K, ~enc, V, hi), Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), key2))), C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), key2)), lo_value(String, V, p2, rn_map(~K, ~enc, V, hi), Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), key2))) : {_ == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.lo(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p2, hi, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, lo, key2)))) : Maybe<&2, T.Entry<String, V>>}
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.lo(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p2, hi, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, lo, key2))), C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, lo, key2)), lo_value(K, V, p2, hi, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, lo, key2))) : {C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, lo), key2)) == rn_item(~K, ~enc, V, _) : Maybe<&2, T.Entry<String, V>>}
      ih_lo(key2)
    case True{}:
      %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup_result(String, V, Map.hi(&2, Maybe<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, p2, rn_map(~K, ~enc, V, lo), Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, hi), key2))), C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, hi), key2)), hi_value(String, V, p2, rn_map(~K, ~enc, V, lo), Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, hi), key2))) : {_ == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.hi(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p2, lo, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, hi, key2)))) : Maybe<&2, T.Entry<String, V>>}
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.hi(&2, Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, p2, lo, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, hi, key2))), C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, hi, key2)), hi_value(K, V, p2, lo, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, hi, key2))) : {C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, hi), key2)) == rn_item(~K, ~enc, V, _) : Maybe<&2, T.Entry<String, V>>}
      ih_hi(key2)

# Native lookup commutes with the value renaming.
def get(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String) -> {C.lookup_result(String, V, Map.get(Maybe<&2, T.Entry<String, V>>, None{}, rn_map(~K, ~enc, V, m), key)) == rn_item(~K, ~enc, V, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, m, key))) : Maybe<&2, T.Entry<String, V>>}:
  match m:
    case MTip{}: {==}
    case MLeaf{+k, +v}: get_leaf(~K, ~enc, V, v, String.cmp(key, k))
    case MNode{+pos, +lo, +hi}: get_bit(~K, ~enc, V, lo, hi, pos, Map.bit(key, pos), q => get(~K, ~enc, V, lo, q), q => get(~K, ~enc, V, hi, q))

# ---------------------------------------------------------------------------
# Seek, put, splice, insert and set.
def rn_seek(~K: Data, ~enc: K -> String, -V: Data, r: Map<&2, Maybe<&2, T.Entry<K, V>>> & String & Maybe<&2, String>) -> Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>:
  (m, key, found) = r
  (rn_map(~K, ~enc, V, m), key, found)

def lo_seek(~K: Data, ~enc: K -> String, -V: Data, +p2: Nat, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & String & Maybe<&2, String>) -> {Map.lo(&2, Maybe<&2, T.Entry<String, V>>, String & Maybe<&2, String>, p2, rn_map(~K, ~enc, V, hi), rn_seek(~K, ~enc, V, r0)) == rn_seek(~K, ~enc, V, Map.lo(&2, Maybe<&2, T.Entry<K, V>>, String & Maybe<&2, String>, p2, hi, r0)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}:
  (m, key, found) = r0
  {==}

def hi_seek(~K: Data, ~enc: K -> String, -V: Data, +p2: Nat, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & String & Maybe<&2, String>) -> {Map.hi(&2, Maybe<&2, T.Entry<String, V>>, String & Maybe<&2, String>, p2, rn_map(~K, ~enc, V, lo), rn_seek(~K, ~enc, V, r0)) == rn_seek(~K, ~enc, V, Map.hi(&2, Maybe<&2, T.Entry<K, V>>, String & Maybe<&2, String>, p2, lo, r0)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}:
  (m, key, found) = r0
  {==}

def seek_bit(~K: Data, ~enc: K -> String, -V: Data, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, +p2: Nat, kb: String & Bool, ih_lo: @+k: String -> {Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), k) == rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, lo, k)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}, ih_hi: @+k: String -> {Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), k) == rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, hi, k)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}) -> {Map.seek.bit(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), p2, kb) == rn_seek(~K, ~enc, V, Map.seek.bit(&2, Maybe<&2, T.Entry<K, V>>, lo, hi, p2, kb)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}:
  (+key2, b) = kb
  match b:
    case False{}:
      %Equal.sym(Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>, Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), key2), rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, lo, key2)), ih_lo(key2)) : {Map.lo(&2, Maybe<&2, T.Entry<String, V>>, String & Maybe<&2, String>, p2, rn_map(~K, ~enc, V, hi), _) == rn_seek(~K, ~enc, V, Map.lo(&2, Maybe<&2, T.Entry<K, V>>, String & Maybe<&2, String>, p2, hi, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, lo, key2))) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}
      lo_seek(~K, ~enc, V, p2, hi, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, lo, key2))
    case True{}:
      %Equal.sym(Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>, Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), key2), rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, hi, key2)), ih_hi(key2)) : {Map.hi(&2, Maybe<&2, T.Entry<String, V>>, String & Maybe<&2, String>, p2, rn_map(~K, ~enc, V, lo), _) == rn_seek(~K, ~enc, V, Map.hi(&2, Maybe<&2, T.Entry<K, V>>, String & Maybe<&2, String>, p2, lo, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, hi, key2))) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}
      hi_seek(~K, ~enc, V, p2, lo, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, hi, key2))

def seek(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String) -> {Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key) == rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, m, key)) : Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>}:
  match m:
    case MTip{}: {==}
    case MLeaf{+k, +v}: {==}
    case MNode{+pos, +lo, +hi}: seek_bit(~K, ~enc, V, lo, hi, pos, Map.bit(key, pos), q => seek(~K, ~enc, V, lo, q), q => seek(~K, ~enc, V, hi, q))

def put_bit(~K: Data, ~enc: K -> String, -V: Data, +x: Maybe<&2, T.Entry<K, V>>, +p2: Nat, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, kb: String & Bool, ih_lo: @+k: String -> {rn_map(~K, ~enc, V, Map.put(&2, Maybe<&2, T.Entry<K, V>>, lo, k, x)) == Map.put(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), k, rn_item(~K, ~enc, V, x)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}, ih_hi: @+k: String -> {rn_map(~K, ~enc, V, Map.put(&2, Maybe<&2, T.Entry<K, V>>, hi, k, x)) == Map.put(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), k, rn_item(~K, ~enc, V, x)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}) -> {rn_map(~K, ~enc, V, Map.put.bit(&2, Maybe<&2, T.Entry<K, V>>, x, p2, lo, hi, kb)) == Map.put.bit(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, x), p2, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), kb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (+key2, b) = kb
  match b:
    case False{}: Equal.cong(Map<&2, Maybe<&2, T.Entry<String, V>>>, Map<&2, Maybe<&2, T.Entry<String, V>>>, t => MNode{p2, t, rn_map(~K, ~enc, V, hi)}, rn_map(~K, ~enc, V, Map.put(&2, Maybe<&2, T.Entry<K, V>>, lo, key2, x)), Map.put(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), key2, rn_item(~K, ~enc, V, x)), ih_lo(key2))
    case True{}: Equal.cong(Map<&2, Maybe<&2, T.Entry<String, V>>>, Map<&2, Maybe<&2, T.Entry<String, V>>>, t => MNode{p2, rn_map(~K, ~enc, V, lo), t}, rn_map(~K, ~enc, V, Map.put(&2, Maybe<&2, T.Entry<K, V>>, hi, key2, x)), Map.put(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), key2, rn_item(~K, ~enc, V, x)), ih_hi(key2))

def put(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String, +x: Maybe<&2, T.Entry<K, V>>) -> {rn_map(~K, ~enc, V, Map.put(&2, Maybe<&2, T.Entry<K, V>>, m, key, x)) == Map.put(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key, rn_item(~K, ~enc, V, x)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{+pos, +lo, +hi}: put_bit(~K, ~enc, V, x, pos, lo, hi, Map.bit(key, pos), q => put(~K, ~enc, V, lo, q, x), q => put(~K, ~enc, V, hi, q, x))

def splice_bit(~K: Data, ~enc: K -> String, -V: Data, +x: Maybe<&2, T.Entry<K, V>>, +rest: Map<&2, Maybe<&2, T.Entry<K, V>>>, +pb: Nat, kb: String & Bool) -> {rn_map(~K, ~enc, V, Map.ins.splice.bit(&2, Maybe<&2, T.Entry<K, V>>, x, rest, pb, kb)) == Map.ins.splice.bit(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, x), rn_map(~K, ~enc, V, rest), pb, kb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (key2, b) = kb
  match b:
    case False{}: {==}
    case True{}: {==}

def splice(~K: Data, ~enc: K -> String, -V: Data, +p: Nat, +key: String, +x: Maybe<&2, T.Entry<K, V>>, +rest: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {rn_map(~K, ~enc, V, Map.ins.splice(&2, Maybe<&2, T.Entry<K, V>>, p, key, x, rest)) == Map.ins.splice(&2, Maybe<&2, T.Entry<String, V>>, p, key, rn_item(~K, ~enc, V, x), rn_map(~K, ~enc, V, rest)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  splice_bit(~K, ~enc, V, x, rest, p, Map.bit(key, p))

def ins_deep(~K: Data, ~enc: K -> String, -V: Data, +x: Maybe<&2, T.Entry<K, V>>, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, +pb: Nat, +qb: Nat, kb: String & Bool, ih_lo: @+k: String -> {rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, lo, k, x, pb)) == Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), k, rn_item(~K, ~enc, V, x), pb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}, ih_hi: @+k: String -> {rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, hi, k, x, pb)) == Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), k, rn_item(~K, ~enc, V, x), pb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}) -> {rn_map(~K, ~enc, V, Map.ins.deep(&2, Maybe<&2, T.Entry<K, V>>, x, lo, hi, pb, qb, kb)) == Map.ins.deep(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, x), rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), pb, qb, kb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (+key2, b) = kb
  match b:
    case False{}: Equal.cong(Map<&2, Maybe<&2, T.Entry<String, V>>>, Map<&2, Maybe<&2, T.Entry<String, V>>>, t => MNode{qb, t, rn_map(~K, ~enc, V, hi)}, rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, lo, key2, x, pb)), Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), key2, rn_item(~K, ~enc, V, x), pb), ih_lo(key2))
    case True{}: Equal.cong(Map<&2, Maybe<&2, T.Entry<String, V>>>, Map<&2, Maybe<&2, T.Entry<String, V>>>, t => MNode{qb, rn_map(~K, ~enc, V, lo), t}, rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, hi, key2, x, pb)), Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), key2, rn_item(~K, ~enc, V, x), pb), ih_hi(key2))

def ins_if(~K: Data, ~enc: K -> String, -V: Data, +key: String, +x: Maybe<&2, T.Entry<K, V>>, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, +p2: Nat, +pb: Nat, ih_lo: @+k: String -> {rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, lo, k, x, pb)) == Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), k, rn_item(~K, ~enc, V, x), pb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}, ih_hi: @+k: String -> {rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, hi, k, x, pb)) == Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), k, rn_item(~K, ~enc, V, x), pb) : Map<&2, Maybe<&2, T.Entry<String, V>>>}, t: Bool) -> {rn_map(~K, ~enc, V, Map.ins.if(&2, Maybe<&2, T.Entry<K, V>>, key, x, lo, hi, p2, pb, t)) == Map.ins.if(&2, Maybe<&2, T.Entry<String, V>>, key, rn_item(~K, ~enc, V, x), rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), p2, pb, t) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  match t:
    case False{}: splice(~K, ~enc, V, pb, key, x, MNode{p2, lo, hi})
    case True{}: ins_deep(~K, ~enc, V, x, lo, hi, pb, p2, Map.bit(key, p2), ih_lo, ih_hi)

def ins(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String, +x: Maybe<&2, T.Entry<K, V>>, +p: Nat) -> {rn_map(~K, ~enc, V, Map.ins(&2, Maybe<&2, T.Entry<K, V>>, m, key, x, p)) == Map.ins(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key, rn_item(~K, ~enc, V, x), p) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  match m:
    case MTip{}: {==}
    case MLeaf{+k, +v}: splice(~K, ~enc, V, p, key, x, MLeaf{k, v})
    case MNode{+pos, +lo, +hi}: ins_if(~K, ~enc, V, key, x, lo, hi, pos, p, q => ins(~K, ~enc, V, lo, q, x, p), q => ins(~K, ~enc, V, hi, q, x, p), Nat.is_lt(pos, p))

def set_fin_go(~K: Data, ~enc: K -> String, -V: Data, +m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String, +x: Maybe<&2, T.Entry<K, V>>, r: (String & String) & Cmp) -> {rn_map(~K, ~enc, V, Map.set.fin.go(&2, Maybe<&2, T.Entry<K, V>>, m, key, x, r)) == Map.set.fin.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key, rn_item(~K, ~enc, V, x), r) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  ((keyb2, k2), c) = r
  match c:
    case LT{}: ins(~K, ~enc, V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}: put(~K, ~enc, V, m, key, x)
    case GT{}: ins(~K, ~enc, V, m, key, x, Map.diff(keyb2, k2))

def set_go(~K: Data, ~enc: K -> String, -V: Data, +x: Maybe<&2, T.Entry<K, V>>, r: Map<&2, Maybe<&2, T.Entry<K, V>>> & String & Maybe<&2, String>) -> {rn_map(~K, ~enc, V, Map.set.go(&2, Maybe<&2, T.Entry<K, V>>, x, r)) == Map.set.go(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, x), rn_seek(~K, ~enc, V, r)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (+m2, +key2, found) = r
  match found:
    case None{}: {==}
    case Some{+k}: set_fin_go(~K, ~enc, V, m2, key2, x, String.cmp(key2, k))

# Native update commutes with the value renaming.
def set(~K: Data, ~enc: K -> String, -V: Data, +m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String, +x: Maybe<&2, T.Entry<K, V>>) -> {rn_map(~K, ~enc, V, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, key, x)) == Map.set(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key, rn_item(~K, ~enc, V, x)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  %Equal.sym(Map<&2, Maybe<&2, T.Entry<String, V>>> & String & Maybe<&2, String>, Map.seek(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key), rn_seek(~K, ~enc, V, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, m, key)), seek(~K, ~enc, V, m, key)) : {rn_map(~K, ~enc, V, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, key, x)) == Map.set.go(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, x), _) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
  set_go(~K, ~enc, V, x, Map.seek(&2, Maybe<&2, T.Entry<K, V>>, m, key))

# ---------------------------------------------------------------------------
# Deletion (the map part of pop).
def pop_leaf(~K: Data, ~enc: K -> String, -V: Data, +v: Maybe<&2, T.Entry<K, V>>, r: (String & String) & Cmp) -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.leaf(&2, Maybe<&2, T.Entry<K, V>>, v, r))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.leaf(&2, Maybe<&2, T.Entry<String, V>>, rn_item(~K, ~enc, V, v), r)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  ((key2, k2), c) = r
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def pop_lo(~K: Data, ~enc: K -> String, -V: Data, +pos: Nat, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, Maybe<&2, T.Entry<K, V>>>, r1: Map<&2, Maybe<&2, T.Entry<String, V>>> & Maybe<&2, Maybe<&2, T.Entry<String, V>>>, same: {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, r0)) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, r1) : Map<&2, Maybe<&2, T.Entry<String, V>>>}) -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<K, V>>, pos, hi, r0))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, hi), r1)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (m0, v0) = r0
  match m0:
    case MTip{}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<K, V>>, pos, hi, (MTip{}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, hi), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}
    case MLeaf{k, v}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<K, V>>, pos, hi, (MLeaf{k, v}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, hi), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}
    case MNode{p, lo, hi2}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<K, V>>, pos, hi, (MNode{p, lo, hi2}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.lo(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, hi), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}

def pop_hi(~K: Data, ~enc: K -> String, -V: Data, +pos: Nat, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, r0: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, Maybe<&2, T.Entry<K, V>>>, r1: Map<&2, Maybe<&2, T.Entry<String, V>>> & Maybe<&2, Maybe<&2, T.Entry<String, V>>>, same: {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, r0)) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, r1) : Map<&2, Maybe<&2, T.Entry<String, V>>>}) -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<K, V>>, pos, lo, r0))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, lo), r1)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (m0, v0) = r0
  match m0:
    case MTip{}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<K, V>>, pos, lo, (MTip{}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, lo), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}
    case MLeaf{k, v}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<K, V>>, pos, lo, (MLeaf{k, v}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, lo), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}
    case MNode{p, lo2, hi2}:
      (m1, v1) = r1
      %same : {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<K, V>>, pos, lo, (MNode{p, lo2, hi2}, v0)))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.hi(&2, Maybe<&2, T.Entry<String, V>>, pos, rn_map(~K, ~enc, V, lo), (_, v1))) : Map<&2, Maybe<&2, T.Entry<String, V>>>}
      {==}

def pop_bit(~K: Data, ~enc: K -> String, -V: Data, +lo: Map<&2, Maybe<&2, T.Entry<K, V>>>, +hi: Map<&2, Maybe<&2, T.Entry<K, V>>>, +p2: Nat, kb: String & Bool, ih_lo: @+k: String -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop(&2, Maybe<&2, T.Entry<K, V>>, lo, k))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), k)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}, ih_hi: @+k: String -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop(&2, Maybe<&2, T.Entry<K, V>>, hi, k))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), k)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}) -> {rn_map(~K, ~enc, V, Map.del.fin(&2, Maybe<&2, T.Entry<K, V>>, Map.pop.bit(&2, Maybe<&2, T.Entry<K, V>>, lo, hi, p2, kb))) == Map.del.fin(&2, Maybe<&2, T.Entry<String, V>>, Map.pop.bit(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi), p2, kb)) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  (+key2, b) = kb
  match b:
    case False{}: pop_lo(~K, ~enc, V, p2, hi, Map.pop(&2, Maybe<&2, T.Entry<K, V>>, lo, key2), Map.pop(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), key2), ih_lo(key2))
    case True{}: pop_hi(~K, ~enc, V, p2, lo, Map.pop(&2, Maybe<&2, T.Entry<K, V>>, hi, key2), Map.pop(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), key2), ih_hi(key2))

# Native deletion commutes with the value renaming.
def del(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +key: String) -> {rn_map(~K, ~enc, V, Map.del(&2, Maybe<&2, T.Entry<K, V>>, m, key)) == Map.del(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), key) : Map<&2, Maybe<&2, T.Entry<String, V>>>}:
  match m:
    case MTip{}: {==}
    case MLeaf{+k, +v}: pop_leaf(~K, ~enc, V, v, String.cmp(key, k))
    case MNode{+pos, +lo, +hi}: pop_bit(~K, ~enc, V, lo, hi, pos, Map.bit(key, pos), q => del(~K, ~enc, V, lo, q), q => del(~K, ~enc, V, hi, q))

# ---------------------------------------------------------------------------
# Size, keys and enumeration.
def size(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {Map.size(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m)) == Map.size(&2, Maybe<&2, T.Entry<K, V>>, m) : Nat}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Nat, Map.size(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)), Map.size(&2, Maybe<&2, T.Entry<K, V>>, lo), size(~K, ~enc, V, lo)) : {Nat.add(_, Map.size(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi))) == Nat.add(Map.size(&2, Maybe<&2, T.Entry<K, V>>, lo), Map.size(&2, Maybe<&2, T.Entry<K, V>>, hi)) : Nat}
      Equal.cong(Nat, Nat, n => Nat.add(Map.size(&2, Maybe<&2, T.Entry<K, V>>, lo), n), Map.size(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)), Map.size(&2, Maybe<&2, T.Entry<K, V>>, hi), size(~K, ~enc, V, hi))

def keys_go(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +acc: List<&2, String>) -> {Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), acc) == Map.keys.go(&2, Maybe<&2, T.Entry<K, V>>, m, acc) : List<&2, String>}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(List<&2, String>, Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), acc), Map.keys.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc), keys_go(~K, ~enc, V, hi, acc)) : {Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), _) == Map.keys.go(&2, Maybe<&2, T.Entry<K, V>>, lo, Map.keys.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc)) : List<&2, String>}
      keys_go(~K, ~enc, V, lo, Map.keys.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc))

def keys(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {Map.keys(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m)) == Map.keys(&2, Maybe<&2, T.Entry<K, V>>, m) : List<&2, String>}:
  keys_go(~K, ~enc, V, m, Nil{})

def rn_pairs(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>:
  match xs:
    case Nil{}: Nil{}
    case Con{Tuple{k, v}, rest}: Con{Tuple{k, rn_item(~K, ~enc, V, v)}, rn_pairs(~K, ~enc, V, rest)}

def to_list_go(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> {Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), rn_pairs(~K, ~enc, V, acc)) == rn_pairs(~K, ~enc, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, m, acc)) : List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), rn_pairs(~K, ~enc, V, acc)), rn_pairs(~K, ~enc, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc)), to_list_go(~K, ~enc, V, hi, acc)) : {Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), _) == rn_pairs(~K, ~enc, V, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc))) : List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>}
      to_list_go(~K, ~enc, V, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<K, V>>, hi, acc))

def to_list(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m)) == rn_pairs(~K, ~enc, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, m)) : List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>}:
  to_list_go(~K, ~enc, V, m, Nil{})

# ---------------------------------------------------------------------------
# Shape predicates depend only on keys and structure.
def routed(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +pos: Nat, +side: Bool) -> {Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), pos, side) == Inv.routed(Maybe<&2, T.Entry<K, V>>, m, pos, side) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Bool, Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), pos, side), Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, pos, side), routed(~K, ~enc, V, lo, pos, side)) : {Bool.and(_, Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), pos, side)) == Bool.and(Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, pos, side), Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, pos, side)) : Bool}
      Equal.cong(Bool, Bool, b => Bool.and(Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, pos, side), b), Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), pos, side), Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, pos, side), routed(~K, ~enc, V, hi, pos, side))

def nonempty(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m)) == Inv.nonempty(Maybe<&2, T.Entry<K, V>>, m) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, lo, hi}: {==}

def below(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +parent: Nat) -> {Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), parent) == Inv.below(Maybe<&2, T.Entry<K, V>>, m, parent) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, lo, hi}: {==}

def prefix_against(~K: Data, ~enc: K -> String, -V: Data, +key: String, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +limit: Nat) -> {Inv.prefix_against(Maybe<&2, T.Entry<String, V>>, key, rn_map(~K, ~enc, V, m), limit) == Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, m, limit) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{p, +lo, +hi}:
      %Equal.sym(Bool, Inv.prefix_against(Maybe<&2, T.Entry<String, V>>, key, rn_map(~K, ~enc, V, lo), limit), Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, lo, limit), prefix_against(~K, ~enc, V, key, lo, limit)) : {Bool.and(_, Inv.prefix_against(Maybe<&2, T.Entry<String, V>>, key, rn_map(~K, ~enc, V, hi), limit)) == Bool.and(Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, lo, limit), Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, hi, limit)) : Bool}
      Equal.cong(Bool, Bool, b => Bool.and(Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, lo, limit), b), Inv.prefix_against(Maybe<&2, T.Entry<String, V>>, key, rn_map(~K, ~enc, V, hi), limit), Inv.prefix_against(Maybe<&2, T.Entry<K, V>>, key, hi, limit), prefix_against(~K, ~enc, V, key, hi, limit))

def common_prefix(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>, +whole: Map<&2, Maybe<&2, T.Entry<K, V>>>, +limit: Nat) -> {Inv.common_prefix(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m), rn_map(~K, ~enc, V, whole), limit) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, m, whole, limit) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{+k, v}: prefix_against(~K, ~enc, V, k, whole, limit)
    case MNode{p, +lo, +hi}:
      %Equal.sym(Bool, Inv.common_prefix(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, whole), limit), Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, lo, whole, limit), common_prefix(~K, ~enc, V, lo, whole, limit)) : {Bool.and(_, Inv.common_prefix(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), rn_map(~K, ~enc, V, whole), limit)) == Bool.and(Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, lo, whole, limit), Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, hi, whole, limit)) : Bool}
      Equal.cong(Bool, Bool, b => Bool.and(Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, lo, whole, limit), b), Inv.common_prefix(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), rn_map(~K, ~enc, V, whole), limit), Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, hi, whole, limit), common_prefix(~K, ~enc, V, hi, whole, limit))

def critbit(~K: Data, ~enc: K -> String, -V: Data, m: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> {Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, m)) == Inv.critbit(Maybe<&2, T.Entry<K, V>>, m) : Bool}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{+p, +lo, +hi}:
      %Equal.sym(Bool, Inv.common_prefix(Maybe<&2, T.Entry<String, V>>, MNode{p, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi)}, MNode{p, rn_map(~K, ~enc, V, lo), rn_map(~K, ~enc, V, hi)}, p), Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p), common_prefix(~K, ~enc, V, MNode{p, lo, hi}, MNode{p, lo, hi}, p)) : {_ && Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p) && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)), Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo), nonempty(~K, ~enc, V, lo)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && _ && Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p) && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.nonempty(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)), Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi), nonempty(~K, ~enc, V, hi)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && _ && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p) && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p), Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p), below(~K, ~enc, V, lo, p)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && _ && Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.below(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p), Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p), below(~K, ~enc, V, hi, p)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && _ && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}) && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo), p, False{}), Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}), routed(~K, ~enc, V, lo, p, False{})) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && _ && Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.routed(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi), p, True{}), Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}), routed(~K, ~enc, V, hi, p, True{})) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && _ && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)) && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, lo)), Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo), critbit(~K, ~enc, V, lo)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && _ && Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)) == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      %Equal.sym(Bool, Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, hi)), Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi), critbit(~K, ~enc, V, hi)) : {Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && _ == Inv.common_prefix(Maybe<&2, T.Entry<K, V>>, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, lo) && Inv.nonempty(Maybe<&2, T.Entry<K, V>>, hi) && Inv.below(Maybe<&2, T.Entry<K, V>>, lo, p) && Inv.below(Maybe<&2, T.Entry<K, V>>, hi, p) && Inv.routed(Maybe<&2, T.Entry<K, V>>, lo, p, False{}) && Inv.routed(Maybe<&2, T.Entry<K, V>>, hi, p, True{}) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, lo) && Inv.critbit(Maybe<&2, T.Entry<K, V>>, hi) : Bool}
      {==}

def identities(~K: Data, ~enc: K -> String, -V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<K, V>>>>) -> {Inv.identities(~String, ~Codec.string_encode, V, rn_pairs(~K, ~enc, V, xs)) == Inv.identities(~K, ~enc, V, xs) : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{code, None{}}, rest}: {==}
    case Con{Tuple{+code, Some{T.Item{+k, v, d}}}, +rest}: Equal.cong(Bool, Bool, b => Bool.and(String.eq(code, enc(k)), b), Inv.identities(~String, ~Codec.string_encode, V, rn_pairs(~K, ~enc, V, rest)), Inv.identities(~K, ~enc, V, rest), identities(~K, ~enc, V, rest))

# ---------------------------------------------------------------------------
# Caches.
def rn_cache(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> C.Cache<String, V>:
  C.State{cap, table, order, life, counts, cb} = c
  C.State{cap, rn_map(~K, ~enc, V, table), order, life, counts, cb}

# The String representation of the renamed cache is the K representation.
def representation(~K: Data, ~enc: K -> String, -V: Data, c: C.Cache<K, V>) -> {Inv.representation(~String, ~Codec.string_encode, V, rn_cache(~K, ~enc, V, c)) == Inv.representation(~K, ~enc, V, c) : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(List<&2, String>, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table)), Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), keys(~K, ~enc, V, table)) : {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap)), Inv.unique(order)), Inv.unique(_)), Inv.included(order, _)), Inv.included(_, order)), Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table))), Inv.identities(~String, ~Codec.string_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table)))) == Inv.representation(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}) : Bool}
  %Equal.sym(Bool, Inv.critbit(Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table)), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table), critbit(~K, ~enc, V, table)) : {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap)), Inv.unique(order)), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order)), _), Inv.identities(~String, ~Codec.string_encode, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table)))) == Inv.representation(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}) : Bool}
  %Equal.sym(List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, rn_map(~K, ~enc, V, table)), rn_pairs(~K, ~enc, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), to_list(~K, ~enc, V, table)) : {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap)), Inv.unique(order)), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order)), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table)), Inv.identities(~String, ~Codec.string_encode, V, _)) == Inv.representation(~K, ~enc, V, C.State{cap, table, order, life, counts, cb}) : Bool}
  Equal.cong(Bool, Bool, b => Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Nat.is_gt(cap, 0n), Nat.is_le(List.length(&2, String, order), cap)), Inv.unique(order)), Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order)), Inv.critbit(Maybe<&2, T.Entry<K, V>>, table)), b), Inv.identities(~String, ~Codec.string_encode, V, rn_pairs(~K, ~enc, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table))), Inv.identities(~K, ~enc, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)), identities(~K, ~enc, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)))
