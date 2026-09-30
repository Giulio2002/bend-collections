import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ../dynamic_array/state.bend as DAS
import ./bk.bend as BK
import ./nsr.bend as NR

# The TreeMap's node store by field: the key list of a node list (length,
# reads, updates, appends, dropping the last) and its block under Array.get /
# Array.set / doubling, and the two pair lists of the links array (two fields
# of every node side by side), for every node list of length at most the
# capacity 2^d, d <= l <= 29.


def l31(+l: Nat, +hl: {Nat.is_le(l, 29n) == True{} : Bool}) -> {Nat.is_le(l, 31n) == True{} : Bool}:
  N.le_trans(l, 29n, 31n, hl, {==})

# Some{x} gives x
def unsome(~K: Data, m: Maybe<&2, M.Node<K>>, +dv: M.Node<K>) -> M.Node<K>:
  match m:
    case None{}:
      dv
    case Some{x}:
      x

def mb(~K: Data, m: Maybe<&2, M.Node<K>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def unsomeA(-A: Data, m: Maybe<&2, A>, +dv: A) -> A:
  match m:
    case None{}:
      dv
    case Some{x}:
      x

# updating a slot with the value it holds changes nothing
def upd_same(-A: Data, +ys: List<&2, A>, +i: Nat, +z: A, +h: {SC.nth(A, ys, i) == Some{z} : Maybe<&2, A>}) -> {SC.update(A, ys, i, z) == ys : List<&2, A>}:
  match ys i:
    case Nil{} _:
      {==}
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, A>, List<&2, A>, w => Con{unsomeA(A, w, x), r}, Some{z}, Some{x}, Equal.sym(Maybe<&2, A>, Some{x}, Some{z}, h))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(A, x, SC.update(A, r, q, z), r, upd_same(A, r, q, z, h))

def keys_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Maybe<&2, K>, NR.keys(~K, xs)) == SC.length(M.Node<K>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(SC.length(Maybe<&2, K>, NR.keys(~K, r)), SC.length(M.Node<K>, r), keys_len(~K, r))

def keys_nth(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Maybe<&2, K>, NR.keys(~K, xs), i) == Some{M.nkey(~K, y)} : Maybe<&2, Maybe<&2, K>>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Maybe<&2, K>, Nil{}, i) == Some{M.nkey(~K, y)} : Maybe<&2, Maybe<&2, K>>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Maybe<&2, K>>, z => Some{M.nkey(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      keys_nth(~K, r, q, y, h)

def keys_upd(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Maybe<&2, K>, NR.keys(~K, xs), i, M.nkey(~K, y)) == NR.keys(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Maybe<&2, K>>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Maybe<&2, K>, M.nkey(~K, x), SC.update(Maybe<&2, K>, NR.keys(~K, r), q, M.nkey(~K, y)), NR.keys(~K, SC.update(M.Node<K>, r, q, y)), keys_upd(~K, r, q, y))

def keys_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Maybe<&2, K>, NR.keys(~K, xs), M.nkey(~K, y)) == NR.keys(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Maybe<&2, K>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Maybe<&2, K>, M.nkey(~K, x), SC.snoc(Maybe<&2, K>, NR.keys(~K, r), M.nkey(~K, y)), NR.keys(~K, SC.snoc(M.Node<K>, r, y)), keys_snoc(~K, r, y))

def keys_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Maybe<&2, K>, NR.keys(~K, xs)) == NR.keys(~K, SC.init(M.Node<K>, xs)) : List<&2, Maybe<&2, K>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Maybe<&2, K>, M.nkey(~K, x), SC.init(Maybe<&2, K>, NR.keys(~K, Con{y, t})), NR.keys(~K, SC.init(M.Node<K>, Con{y, t})), keys_init(~K, Con{y, t}))

# the field block: a slot below the length reads the field
def key_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i)) == (AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), M.nkey(~K, y)) : Array<Maybe<&2, K>> & Maybe<&2, K>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, l31(l, hl)), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), i), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), Some{M.nkey(~K, y)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, i), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), SC.nth(Maybe<&2, K>, fl, i), Some{M.nkey(~K, y)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, i, hiF, hcF), keys_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y)} : Maybe<&2, Maybe<&2, K>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Maybe<&2, K>, d, t, U32.from_nat(i), M.nkey(~K, y), DAS.lt32(d, l, hd, l31(l, hl)), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))

# a slot below the length written with a node's field
def key_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i), M.nkey(~K, y)) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, l31(l, hl)), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), i), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), Some{M.nkey(~K, y0)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, i), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), SC.nth(Maybe<&2, K>, fl, i), Some{M.nkey(~K, y0)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, i, hiF, hcF), keys_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y0)} : Maybe<&2, Maybe<&2, K>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(i), M.nkey(~K, y)), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(i)), M.nkey(~K, y))), AR.set(Maybe<&2, K>, d, t, U32.from_nat(i), M.nkey(~K, y), M.nkey(~K, y0), DAS.lt32(d, l, hd, l31(l, hl)), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, i, M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, i, M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, SC.update(Maybe<&2, K>, fl, i, M.nkey(~K, y)), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{}), BK.bk_set(Maybe<&2, K>, d, fl, None{}, i, M.nkey(~K, y), hiF, hcF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.update(Maybe<&2, K>, fl, i, M.nkey(~K, y)), NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), keys_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def key_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(SC.length(M.Node<K>, xs)), M.nkey(~K, y)) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +n = SC.length(M.Node<K>, xs)
  +hlen = keys_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, l31(l, hl)), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), SC.length(Maybe<&2, K>, fl)), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), SC.length(Maybe<&2, K>, fl)), Some{None{}}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, SC.length(Maybe<&2, K>, fl)), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), BK.fill_at_len(Maybe<&2, K>, SC.pow2(d), fl, None{}, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{None{}} : Maybe<&2, Maybe<&2, K>>}, SC.length(Maybe<&2, K>, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{None{}} : Maybe<&2, Maybe<&2, K>>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(n), M.nkey(~K, y)), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(n)), M.nkey(~K, y))), AR.set(Maybe<&2, K>, d, t, U32.from_nat(n), M.nkey(~K, y), None{}, DAS.lt32(d, l, hd, l31(l, hl)), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  %hlen : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, SC.length(Maybe<&2, K>, fl), M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, SC.length(Maybe<&2, K>, fl), M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, SC.snoc(Maybe<&2, K>, fl, M.nkey(~K, y)), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{}), BK.bk_push(Maybe<&2, K>, d, fl, None{}, M.nkey(~K, y), hnF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.snoc(Maybe<&2, K>, fl, M.nkey(~K, y)), NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), keys_snoc(~K, xs, y))))

# the block doubled with a default half
def key_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), Array.new(Maybe<&2, K>, d, None{})} == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, NR.keys(~K, xs), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), keys_len(~K, xs)), hc)
  %Equal.sym(Array<Maybe<&2, K>>, Array.new(Maybe<&2, K>, d, None{}), AR.thaw(Maybe<&2, K>, AR.trep(Maybe<&2, K>, d, None{})), AR.new(Maybe<&2, K>, d, None{})) : {ANode{AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, fl, None{})), _} == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, fl, None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.TNode{BK.bk(Maybe<&2, K>, d, fl, None{}), AR.trep(Maybe<&2, K>, d, None{})}, BK.bk(Maybe<&2, K>, 1n+d, fl, None{}), BK.bk_grow(Maybe<&2, K>, d, fl, None{}, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def key_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(m), M.nkey(~K, M.Free{0n})) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, l31(l, hl)), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), m), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), m), Some{M.nkey(~K, y0)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, m), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), m), SC.nth(Maybe<&2, K>, fl, m), Some{M.nkey(~K, y0)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, m, hiF, hcF), keys_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y0)} : Maybe<&2, Maybe<&2, K>>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(m), None{}), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(m)), None{})), AR.set(Maybe<&2, K>, d, t, U32.from_nat(m), None{}, M.nkey(~K, y0), DAS.lt32(d, l, hd, l31(l, hl)), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, None{})) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, m, None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, m, None{}), BK.bk(Maybe<&2, K>, d, SC.init(Maybe<&2, K>, fl), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}), BK.bk_pop(Maybe<&2, K>, d, fl, None{}, m, hmF, hcF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.init(Maybe<&2, K>, fl), NR.keys(~K, SC.init(M.Node<K>, xs)), keys_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def keys_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.nkey(~K, x) == M.nkey(~K, y) : Maybe<&2, K>}) -> {NR.keys(~K, SC.update(M.Node<K>, xs, i, x)) == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}:
  %keys_upd(~K, xs, i, x) : {_ == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}
  %Equal.sym(Maybe<&2, K>, M.nkey(~K, x), M.nkey(~K, y), he) : {SC.update(Maybe<&2, K>, NR.keys(~K, xs), i, _) == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}
  upd_same(Maybe<&2, K>, NR.keys(~K, xs), i, M.nkey(~K, y), keys_nth(~K, xs, i, y, hy))


# ---- the pair lists of the links array ----

def some_inj(~K: Data, +x: M.Node<K>, +y: M.Node<K>, +h: {Some{x} == Some{y} : Maybe<&2, M.Node<K>>}) -> {x == y : M.Node<K>}:
  Equal.cong(Maybe<&2, M.Node<K>>, M.Node<K>, z => unsome(~K, z, x), Some{x}, Some{y}, h)

def lrs_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.lrs(~K, xs)) == Nat.double(SC.length(M.Node<K>, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(1n+SC.length(Nat, NR.lrs(~K, r)), 1n+Nat.double(SC.length(M.Node<K>, r)), N.succ_cong(SC.length(Nat, NR.lrs(~K, r)), Nat.double(SC.length(M.Node<K>, r)), lrs_len(~K, r)))

# slot 2i holds the first field of node i, slot 2i+1 the second
def lrs_nth0(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.lrs(~K, xs), Nat.double(i)) == Some{M.nleft(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, Nat.double(i)) == Some{M.nleft(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nleft(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      lrs_nth0(~K, r, q, y, h)

def lrs_nth1(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.lrs(~K, xs), 1n+Nat.double(i)) == Some{M.nright(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, 1n+Nat.double(i)) == Some{M.nright(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nright(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      lrs_nth1(~K, r, q, y, h)

# one field of node i written, the node's other field of the pair kept
def lrs_upd0(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +he: {M.nright(~K, y0) == M.nright(~K, y) : Nat}) -> {SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, y)) == NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      Equal.cong(Nat, List<&2, Nat>, z => Con{M.nleft(~K, y), Con{z, NR.lrs(~K, r)}}, M.nright(~K, x), M.nright(~K, y), Equal.trans(Nat, M.nright(~K, x), M.nright(~K, y0), M.nright(~K, y), Equal.cong(M.Node<K>, Nat, z => M.nright(~K, z), x, y0, some_inj(~K, x, y0, h)), he))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), SC.update(Nat, NR.lrs(~K, r), Nat.double(q), M.nleft(~K, y))}, Con{M.nright(~K, x), NR.lrs(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nright(~K, x), SC.update(Nat, NR.lrs(~K, r), Nat.double(q), M.nleft(~K, y)), NR.lrs(~K, SC.update(M.Node<K>, r, q, y)), lrs_upd0(~K, r, q, y0, y, h, he)))

def lrs_upd1(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +he: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}) -> {SC.update(Nat, NR.lrs(~K, xs), 1n+Nat.double(i), M.nright(~K, y)) == NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      Equal.cong(Nat, List<&2, Nat>, z => Con{z, Con{M.nright(~K, y), NR.lrs(~K, r)}}, M.nleft(~K, x), M.nleft(~K, y), Equal.trans(Nat, M.nleft(~K, x), M.nleft(~K, y0), M.nleft(~K, y), Equal.cong(M.Node<K>, Nat, z => M.nleft(~K, z), x, y0, some_inj(~K, x, y0, h)), he))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), SC.update(Nat, NR.lrs(~K, r), 1n+Nat.double(q), M.nright(~K, y))}, Con{M.nright(~K, x), NR.lrs(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nright(~K, x), SC.update(Nat, NR.lrs(~K, r), 1n+Nat.double(q), M.nright(~K, y)), NR.lrs(~K, SC.update(M.Node<K>, r, q, y)), lrs_upd1(~K, r, q, y0, y, h, he)))

# both fields of node i written
def lrs_put(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, y)), 1n+Nat.double(i), M.nright(~K, y)) == NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), SC.update(Nat, SC.update(Nat, NR.lrs(~K, r), Nat.double(q), M.nleft(~K, y)), 1n+Nat.double(q), M.nright(~K, y))}, Con{M.nright(~K, x), NR.lrs(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nright(~K, x), SC.update(Nat, SC.update(Nat, NR.lrs(~K, r), Nat.double(q), M.nleft(~K, y)), 1n+Nat.double(q), M.nright(~K, y)), NR.lrs(~K, SC.update(M.Node<K>, r, q, y)), lrs_put(~K, r, q, y)))

# a node that keeps both fields leaves the pair list
def lrs_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +ha: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +hb: {M.nright(~K, y0) == M.nright(~K, y) : Nat}) -> {NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)) == NR.lrs(~K, xs) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      +ea = Equal.trans(Nat, M.nleft(~K, y), M.nleft(~K, y0), M.nleft(~K, x), Equal.sym(Nat, M.nleft(~K, y0), M.nleft(~K, y), ha), Equal.cong(M.Node<K>, Nat, z => M.nleft(~K, z), y0, x, Equal.sym(M.Node<K>, x, y0, some_inj(~K, x, y0, h))))
      +eb = Equal.trans(Nat, M.nright(~K, y), M.nright(~K, y0), M.nright(~K, x), Equal.sym(Nat, M.nright(~K, y0), M.nright(~K, y), hb), Equal.cong(M.Node<K>, Nat, z => M.nright(~K, z), y0, x, Equal.sym(M.Node<K>, x, y0, some_inj(~K, x, y0, h))))
      Equal.trans(List<&2, Nat>, Con{M.nleft(~K, y), Con{M.nright(~K, y), NR.lrs(~K, r)}}, Con{M.nleft(~K, x), Con{M.nright(~K, y), NR.lrs(~K, r)}}, Con{M.nleft(~K, x), Con{M.nright(~K, x), NR.lrs(~K, r)}}, Equal.cong(Nat, List<&2, Nat>, z => Con{z, Con{M.nright(~K, y), NR.lrs(~K, r)}}, M.nleft(~K, y), M.nleft(~K, x), ea), Equal.cong(Nat, List<&2, Nat>, z => Con{M.nleft(~K, x), Con{z, NR.lrs(~K, r)}}, M.nright(~K, y), M.nright(~K, x), eb))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), NR.lrs(~K, SC.update(M.Node<K>, r, q, y))}, Con{M.nright(~K, x), NR.lrs(~K, r)}, LL.cons_cong(Nat, M.nright(~K, x), NR.lrs(~K, SC.update(M.Node<K>, r, q, y)), NR.lrs(~K, r), lrs_keep(~K, r, q, y0, y, h, ha, hb)))

def lrs_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, SC.snoc(Nat, NR.lrs(~K, xs), M.nleft(~K, y)), M.nright(~K, y)) == NR.lrs(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), SC.snoc(Nat, SC.snoc(Nat, NR.lrs(~K, r), M.nleft(~K, y)), M.nright(~K, y))}, Con{M.nright(~K, x), NR.lrs(~K, SC.snoc(M.Node<K>, r, y))}, LL.cons_cong(Nat, M.nright(~K, x), SC.snoc(Nat, SC.snoc(Nat, NR.lrs(~K, r), M.nleft(~K, y)), M.nright(~K, y)), NR.lrs(~K, SC.snoc(M.Node<K>, r, y)), lrs_snoc(~K, r, y)))

def lrs_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, SC.init(Nat, NR.lrs(~K, xs))) == NR.lrs(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.nleft(~K, x), Con{M.nright(~K, x), SC.init(Nat, SC.init(Nat, NR.lrs(~K, Con{y, t})))}, Con{M.nright(~K, x), NR.lrs(~K, SC.init(M.Node<K>, Con{y, t}))}, LL.cons_cong(Nat, M.nright(~K, x), SC.init(Nat, SC.init(Nat, NR.lrs(~K, Con{y, t}))), NR.lrs(~K, SC.init(M.Node<K>, Con{y, t})), lrs_init(~K, Con{y, t})))

# the pair list fits its block of depth 1 + d
def lrs_cap(~K: Data, +d: Nat, +xs: List<&2, M.Node<K>>, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_le(SC.length(Nat, NR.lrs(~K, xs)), SC.pow2(1n+d)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, NR.lrs(~K, xs)), Nat.double(SC.length(M.Node<K>, xs)), lrs_len(~K, xs)) : {Nat.is_le(_, SC.pow2(1n+d)) == True{} : Bool}
  N.double_le(SC.length(M.Node<K>, xs), SC.pow2(d), hc)

def tps_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.tps(~K, xs)) == Nat.double(SC.length(M.Node<K>, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(1n+SC.length(Nat, NR.tps(~K, r)), 1n+Nat.double(SC.length(M.Node<K>, r)), N.succ_cong(SC.length(Nat, NR.tps(~K, r)), Nat.double(SC.length(M.Node<K>, r)), tps_len(~K, r)))

# slot 2i holds the first field of node i, slot 2i+1 the second
def tps_nth0(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.tps(~K, xs), Nat.double(i)) == Some{M.ntag(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, Nat.double(i)) == Some{M.ntag(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.ntag(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      tps_nth0(~K, r, q, y, h)

def tps_nth1(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.tps(~K, xs), 1n+Nat.double(i)) == Some{M.nparent(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, 1n+Nat.double(i)) == Some{M.nparent(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nparent(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      tps_nth1(~K, r, q, y, h)

# one field of node i written, the node's other field of the pair kept
def tps_upd0(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +he: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, y)) == NR.tps(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      Equal.cong(Nat, List<&2, Nat>, z => Con{M.ntag(~K, y), Con{z, NR.tps(~K, r)}}, M.nparent(~K, x), M.nparent(~K, y), Equal.trans(Nat, M.nparent(~K, x), M.nparent(~K, y0), M.nparent(~K, y), Equal.cong(M.Node<K>, Nat, z => M.nparent(~K, z), x, y0, some_inj(~K, x, y0, h)), he))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), SC.update(Nat, NR.tps(~K, r), Nat.double(q), M.ntag(~K, y))}, Con{M.nparent(~K, x), NR.tps(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nparent(~K, x), SC.update(Nat, NR.tps(~K, r), Nat.double(q), M.ntag(~K, y)), NR.tps(~K, SC.update(M.Node<K>, r, q, y)), tps_upd0(~K, r, q, y0, y, h, he)))

def tps_upd1(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +he: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}) -> {SC.update(Nat, NR.tps(~K, xs), 1n+Nat.double(i), M.nparent(~K, y)) == NR.tps(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      Equal.cong(Nat, List<&2, Nat>, z => Con{z, Con{M.nparent(~K, y), NR.tps(~K, r)}}, M.ntag(~K, x), M.ntag(~K, y), Equal.trans(Nat, M.ntag(~K, x), M.ntag(~K, y0), M.ntag(~K, y), Equal.cong(M.Node<K>, Nat, z => M.ntag(~K, z), x, y0, some_inj(~K, x, y0, h)), he))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), SC.update(Nat, NR.tps(~K, r), 1n+Nat.double(q), M.nparent(~K, y))}, Con{M.nparent(~K, x), NR.tps(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nparent(~K, x), SC.update(Nat, NR.tps(~K, r), 1n+Nat.double(q), M.nparent(~K, y)), NR.tps(~K, SC.update(M.Node<K>, r, q, y)), tps_upd1(~K, r, q, y0, y, h, he)))

# both fields of node i written
def tps_put(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, y)), 1n+Nat.double(i), M.nparent(~K, y)) == NR.tps(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), SC.update(Nat, SC.update(Nat, NR.tps(~K, r), Nat.double(q), M.ntag(~K, y)), 1n+Nat.double(q), M.nparent(~K, y))}, Con{M.nparent(~K, x), NR.tps(~K, SC.update(M.Node<K>, r, q, y))}, LL.cons_cong(Nat, M.nparent(~K, x), SC.update(Nat, SC.update(Nat, NR.tps(~K, r), Nat.double(q), M.ntag(~K, y)), 1n+Nat.double(q), M.nparent(~K, y)), NR.tps(~K, SC.update(M.Node<K>, r, q, y)), tps_put(~K, r, q, y)))

# a node that keeps both fields leaves the pair list
def tps_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +ha: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}, +hb: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {NR.tps(~K, SC.update(M.Node<K>, xs, i, y)) == NR.tps(~K, xs) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +r} 0n:
      +ea = Equal.trans(Nat, M.ntag(~K, y), M.ntag(~K, y0), M.ntag(~K, x), Equal.sym(Nat, M.ntag(~K, y0), M.ntag(~K, y), ha), Equal.cong(M.Node<K>, Nat, z => M.ntag(~K, z), y0, x, Equal.sym(M.Node<K>, x, y0, some_inj(~K, x, y0, h))))
      +eb = Equal.trans(Nat, M.nparent(~K, y), M.nparent(~K, y0), M.nparent(~K, x), Equal.sym(Nat, M.nparent(~K, y0), M.nparent(~K, y), hb), Equal.cong(M.Node<K>, Nat, z => M.nparent(~K, z), y0, x, Equal.sym(M.Node<K>, x, y0, some_inj(~K, x, y0, h))))
      Equal.trans(List<&2, Nat>, Con{M.ntag(~K, y), Con{M.nparent(~K, y), NR.tps(~K, r)}}, Con{M.ntag(~K, x), Con{M.nparent(~K, y), NR.tps(~K, r)}}, Con{M.ntag(~K, x), Con{M.nparent(~K, x), NR.tps(~K, r)}}, Equal.cong(Nat, List<&2, Nat>, z => Con{z, Con{M.nparent(~K, y), NR.tps(~K, r)}}, M.ntag(~K, y), M.ntag(~K, x), ea), Equal.cong(Nat, List<&2, Nat>, z => Con{M.ntag(~K, x), Con{z, NR.tps(~K, r)}}, M.nparent(~K, y), M.nparent(~K, x), eb))
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), NR.tps(~K, SC.update(M.Node<K>, r, q, y))}, Con{M.nparent(~K, x), NR.tps(~K, r)}, LL.cons_cong(Nat, M.nparent(~K, x), NR.tps(~K, SC.update(M.Node<K>, r, q, y)), NR.tps(~K, r), tps_keep(~K, r, q, y0, y, h, ha, hb)))

def tps_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, SC.snoc(Nat, NR.tps(~K, xs), M.ntag(~K, y)), M.nparent(~K, y)) == NR.tps(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), SC.snoc(Nat, SC.snoc(Nat, NR.tps(~K, r), M.ntag(~K, y)), M.nparent(~K, y))}, Con{M.nparent(~K, x), NR.tps(~K, SC.snoc(M.Node<K>, r, y))}, LL.cons_cong(Nat, M.nparent(~K, x), SC.snoc(Nat, SC.snoc(Nat, NR.tps(~K, r), M.ntag(~K, y)), M.nparent(~K, y)), NR.tps(~K, SC.snoc(M.Node<K>, r, y)), tps_snoc(~K, r, y)))

def tps_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, SC.init(Nat, NR.tps(~K, xs))) == NR.tps(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.ntag(~K, x), Con{M.nparent(~K, x), SC.init(Nat, SC.init(Nat, NR.tps(~K, Con{y, t})))}, Con{M.nparent(~K, x), NR.tps(~K, SC.init(M.Node<K>, Con{y, t}))}, LL.cons_cong(Nat, M.nparent(~K, x), SC.init(Nat, SC.init(Nat, NR.tps(~K, Con{y, t}))), NR.tps(~K, SC.init(M.Node<K>, Con{y, t})), tps_init(~K, Con{y, t})))

# the pair list fits its block of depth 1 + d
def tps_cap(~K: Data, +d: Nat, +xs: List<&2, M.Node<K>>, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_le(SC.length(Nat, NR.tps(~K, xs)), SC.pow2(1n+d)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, NR.tps(~K, xs)), Nat.double(SC.length(M.Node<K>, xs)), tps_len(~K, xs)) : {Nat.is_le(_, SC.pow2(1n+d)) == True{} : Bool}
  N.double_le(SC.length(M.Node<K>, xs), SC.pow2(d), hc)

