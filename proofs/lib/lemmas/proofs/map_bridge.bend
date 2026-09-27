import Base

# Bend 2.0.32 rewrote Base's Map descents (get, has, put, pop, seek, ins) as
# one-level `Map.X.go` functions over the whole node. The lemmas in this
# library were written against 2.0.28's shape, where Map.X on a node branched
# through a `.bit` helper (`.deep`/`.if` for ins) that recursed with Map.X on
# the chosen child. Mutual recursion is no longer allowed, so those helpers
# are defined here non-recursively, each calling Base's current Map.X on the
# child, and each comes with a bridge law: Map.X on a node equals the helper.
# Every bridge holds by unfolding both sides (no induction).

# ---- the routed key: Map.bit keeps the key (from native_map.bend) ----

def routed_key(r: String & Bool) -> String:
  (key, bit) = r
  key

law recursive_bit_key:
  for c: Char
  for r: String & Bool
  {routed_key(Map.bit.go.rec(c, r)) == SCon{c, routed_key(r)} : String}
def recursive_bit_key(c, r):
  match r:
    case Tuple{key, bit}:
      {==}

law bit_go_preserves_key:
  for key: String
  for +character: Nat
  for +offset: Nat
  {routed_key(Map.bit.go(key, character, offset)) == key : String}
def bit_go_preserves_key(key, character, offset):
  match key character offset:
    case SNil{} ci off:
      {==}
    case SCon{Chr{x}, tail} 0n 0n:
      {==}
    case SCon{Chr{x}, tail} 0n 1n+off:
      {==}
    case SCon{Chr{x}, +tail} 1n+ci off:
      +c = {Chr{x} : Char}
      Equal.trans(String, routed_key(Map.bit.go.rec(c, Map.bit.go(tail, ci, off))),
        SCon{c, routed_key(Map.bit.go(tail, ci, off))}, SCon{c, tail},
        recursive_bit_key(c, Map.bit.go(tail, ci, off)),
        Equal.cong(String, String, t => SCon{c, t}, routed_key(Map.bit.go(tail, ci, off)), tail, bit_go_preserves_key(tail, ci, off)))

law bit_at_preserves_key:
  for key: String
  for coordinates: Nat & Nat
  {routed_key(Map.bit.at(key, coordinates)) == key : String}
def bit_at_preserves_key(key, coordinates):
  match coordinates:
    case Tuple{ci, off}:
      bit_go_preserves_key(key, ci, off)

law bit_preserves_key:
  for key: String
  for position: Nat
  {routed_key(Map.bit(key, position)) == key : String}
def bit_preserves_key(key, position):
  bit_at_preserves_key(key, Nat.divmod(position, 33n))

# ---- one-step helpers (2.0.28's `.bit` shape over Base's current Map) ----

def get_bit(-V: Data, d: V, lo: Map<&2, V>, hi: Map<&2, V>, p2: Nat, kb: String & Bool) -> Map<&2, V> & V:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(&2, V, V, p2, hi, Map.get(V, d, lo, key2))
    case True{}:
      Map.hi(&2, V, V, p2, lo, Map.get(V, d, hi, key2))

def has_bit(-a: Quant, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool) -> Map<a, V> & Bool:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(a, V, Bool, p2, hi, Map.has(a, V, lo, key2))
    case True{}:
      Map.hi(a, V, Bool, p2, lo, Map.has(a, V, hi, key2))

def put_bit(-a: Quant, -V: Kind(a), x: V, p2: Nat, lo: Map<a, V>, hi: Map<a, V>, kb: String & Bool) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{p2, Map.put(a, V, lo, key2, x), hi}
    case True{}:
      MNode{p2, lo, Map.put(a, V, hi, key2, x)}

def pop_bit(-a: Quant, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool) -> Map<a, V> & Maybe<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      Map.pop.lo(a, V, p2, hi, Map.pop(a, V, lo, key2))
    case True{}:
      Map.pop.hi(a, V, p2, lo, Map.pop(a, V, hi, key2))

def seek_bit(-a: Quant, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool) -> Map<a, V> & String & Maybe<&2, String>:
  (key2, b) = kb
  match b:
    case False{}:
      Map.lo(a, V, String & Maybe<&2, String>, p2, hi, Map.seek(a, V, lo, key2))
    case True{}:
      Map.hi(a, V, String & Maybe<&2, String>, p2, lo, Map.seek(a, V, hi, key2))

def ins_deep(-a: Quant, -V: Kind(a), x: V, lo: Map<a, V>, hi: Map<a, V>, pb: Nat, qb: Nat, kb: String & Bool) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{qb, Map.ins(a, V, lo, key2, x, pb), hi}
    case True{}:
      MNode{qb, lo, Map.ins(a, V, hi, key2, x, pb)}

def ins_if(-a: Quant, -V: Kind(a), key: String, x: V, lo: Map<a, V>, hi: Map<a, V>, +p2: Nat, pb: Nat, t: Bool) -> Map<a, V>:
  match t:
    case False{}:
      Map.ins.splice(a, V, pb, key, x, MNode{p2, lo, hi})
    case True{}:
      ins_deep(a, V, x, lo, hi, pb, p2, Map.bit(key, p2))

# ---- bridges: Base Map.X on a node is the one-step helper ----

law get_go_bridge:
  for -V: Data
    for d: V
for +p: Nat
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for kb: String & Bool
  {Map.get.go(V, MNode{p, lo, hi}, d, kb) == get_bit(V, d, lo, hi, p, kb) : Map<&2, V> & V}
def get_go_bridge(V, d, p, lo, hi, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{q, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{q, c, e} Tuple{key2, True{}}:
      {==}

law get_node:
  for -V: Data
    for d: V
for +p: Nat
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for key: String
  {Map.get(V, d, MNode{p, lo, hi}, key) == get_bit(V, d, lo, hi, p, Map.bit(key, p)) : Map<&2, V> & V}
def get_node(V, d, p, lo, hi, key):
  get_go_bridge(V, d, p, lo, hi, Map.bit(key, p))

law has_go_bridge:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for kb: String & Bool
  {Map.has.go(a, V, MNode{p, lo, hi}, kb) == has_bit(a, V, lo, hi, p, kb) : Map<a, V> & Bool}
def has_go_bridge(a, V, p, lo, hi, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{q, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{q, c, e} Tuple{key2, True{}}:
      {==}

law has_node:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for key: String
  {Map.has(a, V, MNode{p, lo, hi}, key) == has_bit(a, V, lo, hi, p, Map.bit(key, p)) : Map<a, V> & Bool}
def has_node(a, V, p, lo, hi, key):
  has_go_bridge(a, V, p, lo, hi, Map.bit(key, p))

law put_go_bridge:
  for -a: Quant
  for -V: Kind(a)
    for x: V
for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for kb: String & Bool
  {Map.put.go(a, V, MNode{p, lo, hi}, x, kb) == put_bit(a, V, x, p, lo, hi, kb) : Map<a, V>}
def put_go_bridge(a, V, x, p, lo, hi, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{q, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{q, c, e} Tuple{key2, True{}}:
      {==}

law put_node:
  for -a: Quant
  for -V: Kind(a)
    for x: V
for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for key: String
  {Map.put(a, V, MNode{p, lo, hi}, key, x) == put_bit(a, V, x, p, lo, hi, Map.bit(key, p)) : Map<a, V>}
def put_node(a, V, x, p, lo, hi, key):
  put_go_bridge(a, V, x, p, lo, hi, Map.bit(key, p))

law pop_go_bridge:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for kb: String & Bool
  {Map.pop.go(a, V, MNode{p, lo, hi}, kb) == pop_bit(a, V, lo, hi, p, kb) : Map<a, V> & Maybe<a, V>}
def pop_go_bridge(a, V, p, lo, hi, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{q, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{q, c, e} Tuple{key2, True{}}:
      {==}

law pop_node:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for key: String
  {Map.pop(a, V, MNode{p, lo, hi}, key) == pop_bit(a, V, lo, hi, p, Map.bit(key, p)) : Map<a, V> & Maybe<a, V>}
def pop_node(a, V, p, lo, hi, key):
  pop_go_bridge(a, V, p, lo, hi, Map.bit(key, p))

law seek_go_bridge:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for kb: String & Bool
  {Map.seek.go(a, V, MNode{p, lo, hi}, kb) == seek_bit(a, V, lo, hi, p, kb) : Map<a, V> & String & Maybe<&2, String>}
def seek_go_bridge(a, V, p, lo, hi, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{q, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{q, c, e} Tuple{key2, True{}}:
      {==}

law seek_node:
  for -a: Quant
  for -V: Kind(a)
  for +p: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for key: String
  {Map.seek(a, V, MNode{p, lo, hi}, key) == seek_bit(a, V, lo, hi, p, Map.bit(key, p)) : Map<a, V> & String & Maybe<&2, String>}
def seek_node(a, V, p, lo, hi, key):
  seek_go_bridge(a, V, p, lo, hi, Map.bit(key, p))

law ins_splice_bridge:
  for -a: Quant
  for -V: Kind(a)
  for +q: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for x: V
  for +p: Nat
  for key: String
  for kb: String & Bool
  for hk: {routed_key(kb) == key : String}
  {Map.ins.go(a, V, MNode{q, lo, hi}, x, p, kb, False{}) == Map.ins.splice(a, V, p, key, x, MNode{q, lo, hi}) : Map<a, V>}
def ins_splice_bridge(a, V, q, lo, hi, x, p, key, kb, hk):
  match lo hi kb:
    case MTip{} MTip{} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MTip{}}) : Map<a, V>}
      {==}
    case MTip{} MTip{} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MTip{}}) : Map<a, V>}
      {==}
    case MTip{} MLeaf{k3, v3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MTip{} MLeaf{k3, v3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MTip{} MNode{r3, c3, e3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}
    case MTip{} MNode{r3, c3, e3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MTip{}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MTip{}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MTip{} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MTip{}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MTip{} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MTip{}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MLeaf{k3, v3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MLeaf{k3, v3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MNode{r3, c3, e3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}
    case MLeaf{k1, v1} MNode{r3, c3, e3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MLeaf{k1, v1}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MLeaf{k1, v1}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MTip{} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MTip{}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MTip{} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MTip{}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MTip{}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MLeaf{k3, v3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MLeaf{k3, v3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MLeaf{k3, v3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MLeaf{k3, v3}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MNode{r3, c3, e3} Tuple{k2, False{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}
    case MNode{r1, c1, e1} MNode{r3, c3, e3} Tuple{k2, True{}}:
      %Equal.sym(String, k2, key, hk) : {Map.ins.splice(a, V, p, _, x, MNode{q, MNode{r1, c1, e1}, MNode{r3, c3, e3}}) == Map.ins.splice(a, V, p, key, x, MNode{q, MNode{r1, c1, e1}, MNode{r3, c3, e3}}) : Map<a, V>}
      {==}

law ins_deep_bridge:
  for -a: Quant
  for -V: Kind(a)
  for +q: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for x: V
  for +p: Nat
  for kb: String & Bool
  {Map.ins.go(a, V, MNode{q, lo, hi}, x, p, kb, True{}) == ins_deep(a, V, x, lo, hi, p, q, kb) : Map<a, V>}
def ins_deep_bridge(a, V, q, lo, hi, x, p, kb):
  match lo hi kb:
    case MTip{} _ Tuple{key2, False{}}:
      {==}
    case MLeaf{k, v} _ Tuple{key2, False{}}:
      {==}
    case MNode{r, c, e} _ Tuple{key2, False{}}:
      {==}
    case _ MTip{} Tuple{key2, True{}}:
      {==}
    case _ MLeaf{k, v} Tuple{key2, True{}}:
      {==}
    case _ MNode{r, c, e} Tuple{key2, True{}}:
      {==}

law ins_t:
  for -a: Quant
  for -V: Kind(a)
  for +pos: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for +key: String
  for x: V
  for +p: Nat
  for t: Bool
  {Map.ins.go(a, V, MNode{pos, lo, hi}, x, p, Map.bit(key, pos), t) == ins_if(a, V, key, x, lo, hi, pos, p, t) : Map<a, V>}
def ins_t(a, V, pos, lo, hi, key, x, p, t):
  match t:
    case False{}:
      ins_splice_bridge(a, V, pos, lo, hi, x, p, key, Map.bit(key, pos), bit_preserves_key(key, pos))
    case True{}:
      ins_deep_bridge(a, V, pos, lo, hi, x, p, Map.bit(key, pos))

law ins_node:
  for -a: Quant
  for -V: Kind(a)
  for +pos: Nat
  for lo: Map<a, V>
  for hi: Map<a, V>
  for +key: String
  for x: V
  for +p: Nat
  {Map.ins(a, V, MNode{pos, lo, hi}, key, x, p) == ins_if(a, V, key, x, lo, hi, pos, p, Nat.is_lt(pos, p)) : Map<a, V>}
def ins_node(a, V, pos, lo, hi, key, x, p):
  ins_t(a, V, pos, lo, hi, key, x, p, Nat.is_lt(pos, p))
