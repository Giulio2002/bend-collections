import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ../dynamic_array/state.bend as DAS
import ./bk.bend as BK
import ./nsr.bend as NR

# One field of the TreeMap's node store: the field list of a node list
# (length, reads, updates, appends, dropping the last) and the field's block
# under Array.get / Array.set / doubling, for every node list of length at
# most the capacity 2^d, d <= l <= 31.


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

def tags_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.tags(~K, xs)) == SC.length(M.Node<K>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(SC.length(Nat, NR.tags(~K, r)), SC.length(M.Node<K>, r), tags_len(~K, r))

def tags_nth(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.tags(~K, xs), i) == Some{M.ntag(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, i) == Some{M.ntag(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.ntag(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      tags_nth(~K, r, q, y, h)

def tags_upd(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, NR.tags(~K, xs), i, M.ntag(~K, y)) == NR.tags(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.ntag(~K, x), SC.update(Nat, NR.tags(~K, r), q, M.ntag(~K, y)), NR.tags(~K, SC.update(M.Node<K>, r, q, y)), tags_upd(~K, r, q, y))

def tags_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, NR.tags(~K, xs), M.ntag(~K, y)) == NR.tags(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.ntag(~K, x), SC.snoc(Nat, NR.tags(~K, r), M.ntag(~K, y)), NR.tags(~K, SC.snoc(M.Node<K>, r, y)), tags_snoc(~K, r, y))

def tags_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, NR.tags(~K, xs)) == NR.tags(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.ntag(~K, x), SC.init(Nat, NR.tags(~K, Con{y, t})), NR.tags(~K, SC.init(M.Node<K>, Con{y, t})), tags_init(~K, Con{y, t}))

# the field block: a slot below the length reads the field
def tag_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), U32.from_nat(i)) == (AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), M.ntag(~K, y)) : Array<Nat> & Nat}:
  +fl = NR.tags(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = tags_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.ntag(~K, y)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.ntag(~K, y)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), tags_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.ntag(~K, y)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Nat, d, t, U32.from_nat(i), M.ntag(~K, y), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))

# a slot below the length written with a node's field
def tag_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), U32.from_nat(i), M.ntag(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}:
  +fl = NR.tags(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = tags_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.ntag(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.ntag(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), tags_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.ntag(~K, y0)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(i), M.ntag(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(i)), M.ntag(~K, y))), AR.set(Nat, d, t, U32.from_nat(i), M.ntag(~K, y), M.ntag(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.ntag(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, i, M.ntag(~K, y)), BK.bk(Nat, d, NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, i, M.ntag(~K, y)), BK.bk(Nat, d, SC.update(Nat, fl, i, M.ntag(~K, y)), 0n), BK.bk(Nat, d, NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk_set(Nat, d, fl, 0n, i, M.ntag(~K, y), hiF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.update(Nat, fl, i, M.ntag(~K, y)), NR.tags(~K, SC.update(M.Node<K>, xs, i, y)), tags_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def tag_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), U32.from_nat(SC.length(M.Node<K>, xs)), M.ntag(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}:
  +fl = NR.tags(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +n = SC.length(M.Node<K>, xs)
  +hlen = tags_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, hl), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), SC.length(Nat, fl)), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), SC.length(Nat, fl)), Some{0n}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, SC.length(Nat, fl)), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), BK.fill_at_len(Nat, SC.pow2(d), fl, 0n, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, SC.length(Nat, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(n), M.ntag(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(n)), M.ntag(~K, y))), AR.set(Nat, d, t, U32.from_nat(n), M.ntag(~K, y), 0n, DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.ntag(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %hlen : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.ntag(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, SC.length(Nat, fl), M.ntag(~K, y)), BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, SC.length(Nat, fl), M.ntag(~K, y)), BK.bk(Nat, d, SC.snoc(Nat, fl, M.ntag(~K, y)), 0n), BK.bk(Nat, d, NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), 0n), BK.bk_push(Nat, d, fl, 0n, M.ntag(~K, y), hnF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.snoc(Nat, fl, M.ntag(~K, y)), NR.tags(~K, SC.snoc(M.Node<K>, xs, y)), tags_snoc(~K, xs, y))))

# the block doubled with a default half
def tag_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), Array.new(Nat, d, 0n)} == AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.tags(~K, xs), 0n)) : Array<Nat>}:
  +fl = NR.tags(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), tags_len(~K, xs)), hc)
  %Equal.sym(Array<Nat>, Array.new(Nat, d, 0n), AR.thaw(Nat, AR.trep(Nat, d, 0n)), AR.new(Nat, d, 0n)) : {ANode{AR.thaw(Nat, BK.bk(Nat, d, fl, 0n)), _} == AR.thaw(Nat, BK.bk(Nat, 1n+d, fl, 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.TNode{BK.bk(Nat, d, fl, 0n), AR.trep(Nat, d, 0n)}, BK.bk(Nat, 1n+d, fl, 0n), BK.bk_grow(Nat, d, fl, 0n, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def tag_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, xs), 0n)), U32.from_nat(m), M.ntag(~K, M.Free{0n})) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}:
  +fl = NR.tags(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = tags_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), m), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), Some{M.ntag(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, m), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), SC.nth(Nat, fl, m), Some{M.ntag(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, m, hiF, hcF), tags_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.ntag(~K, y0)} : Maybe<&2, Nat>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(m), 0n), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(m)), 0n)), AR.set(Nat, d, t, U32.from_nat(m), 0n, M.ntag(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, 0n)) == AR.thaw(Nat, BK.bk(Nat, d, NR.tags(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, NR.tags(~K, SC.init(M.Node<K>, xs)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, SC.init(Nat, fl), 0n), BK.bk(Nat, d, NR.tags(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk_pop(Nat, d, fl, 0n, m, hmF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.init(Nat, fl), NR.tags(~K, SC.init(M.Node<K>, xs)), tags_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def tags_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.ntag(~K, x) == M.ntag(~K, y) : Nat}) -> {NR.tags(~K, SC.update(M.Node<K>, xs, i, x)) == NR.tags(~K, xs) : List<&2, Nat>}:
  %tags_upd(~K, xs, i, x) : {_ == NR.tags(~K, xs) : List<&2, Nat>}
  %Equal.sym(Nat, M.ntag(~K, x), M.ntag(~K, y), he) : {SC.update(Nat, NR.tags(~K, xs), i, _) == NR.tags(~K, xs) : List<&2, Nat>}
  upd_same(Nat, NR.tags(~K, xs), i, M.ntag(~K, y), tags_nth(~K, xs, i, y, hy))

def lefts_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.lefts(~K, xs)) == SC.length(M.Node<K>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(SC.length(Nat, NR.lefts(~K, r)), SC.length(M.Node<K>, r), lefts_len(~K, r))

def lefts_nth(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.lefts(~K, xs), i) == Some{M.nleft(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, i) == Some{M.nleft(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nleft(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      lefts_nth(~K, r, q, y, h)

def lefts_upd(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, NR.lefts(~K, xs), i, M.nleft(~K, y)) == NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nleft(~K, x), SC.update(Nat, NR.lefts(~K, r), q, M.nleft(~K, y)), NR.lefts(~K, SC.update(M.Node<K>, r, q, y)), lefts_upd(~K, r, q, y))

def lefts_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, NR.lefts(~K, xs), M.nleft(~K, y)) == NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.nleft(~K, x), SC.snoc(Nat, NR.lefts(~K, r), M.nleft(~K, y)), NR.lefts(~K, SC.snoc(M.Node<K>, r, y)), lefts_snoc(~K, r, y))

def lefts_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, NR.lefts(~K, xs)) == NR.lefts(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.nleft(~K, x), SC.init(Nat, NR.lefts(~K, Con{y, t})), NR.lefts(~K, SC.init(M.Node<K>, Con{y, t})), lefts_init(~K, Con{y, t}))

# the field block: a slot below the length reads the field
def left_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), U32.from_nat(i)) == (AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), M.nleft(~K, y)) : Array<Nat> & Nat}:
  +fl = NR.lefts(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = lefts_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nleft(~K, y)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nleft(~K, y)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), lefts_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nleft(~K, y)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Nat, d, t, U32.from_nat(i), M.nleft(~K, y), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))

# a slot below the length written with a node's field
def left_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), U32.from_nat(i), M.nleft(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}:
  +fl = NR.lefts(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = lefts_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nleft(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nleft(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), lefts_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nleft(~K, y0)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(i), M.nleft(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(i)), M.nleft(~K, y))), AR.set(Nat, d, t, U32.from_nat(i), M.nleft(~K, y), M.nleft(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nleft(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, i, M.nleft(~K, y)), BK.bk(Nat, d, NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, i, M.nleft(~K, y)), BK.bk(Nat, d, SC.update(Nat, fl, i, M.nleft(~K, y)), 0n), BK.bk(Nat, d, NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk_set(Nat, d, fl, 0n, i, M.nleft(~K, y), hiF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.update(Nat, fl, i, M.nleft(~K, y)), NR.lefts(~K, SC.update(M.Node<K>, xs, i, y)), lefts_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def left_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), U32.from_nat(SC.length(M.Node<K>, xs)), M.nleft(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}:
  +fl = NR.lefts(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +n = SC.length(M.Node<K>, xs)
  +hlen = lefts_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, hl), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), SC.length(Nat, fl)), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), SC.length(Nat, fl)), Some{0n}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, SC.length(Nat, fl)), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), BK.fill_at_len(Nat, SC.pow2(d), fl, 0n, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, SC.length(Nat, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(n), M.nleft(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(n)), M.nleft(~K, y))), AR.set(Nat, d, t, U32.from_nat(n), M.nleft(~K, y), 0n, DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nleft(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %hlen : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nleft(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, SC.length(Nat, fl), M.nleft(~K, y)), BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, SC.length(Nat, fl), M.nleft(~K, y)), BK.bk(Nat, d, SC.snoc(Nat, fl, M.nleft(~K, y)), 0n), BK.bk(Nat, d, NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), 0n), BK.bk_push(Nat, d, fl, 0n, M.nleft(~K, y), hnF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.snoc(Nat, fl, M.nleft(~K, y)), NR.lefts(~K, SC.snoc(M.Node<K>, xs, y)), lefts_snoc(~K, xs, y))))

# the block doubled with a default half
def left_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), Array.new(Nat, d, 0n)} == AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.lefts(~K, xs), 0n)) : Array<Nat>}:
  +fl = NR.lefts(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), lefts_len(~K, xs)), hc)
  %Equal.sym(Array<Nat>, Array.new(Nat, d, 0n), AR.thaw(Nat, AR.trep(Nat, d, 0n)), AR.new(Nat, d, 0n)) : {ANode{AR.thaw(Nat, BK.bk(Nat, d, fl, 0n)), _} == AR.thaw(Nat, BK.bk(Nat, 1n+d, fl, 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.TNode{BK.bk(Nat, d, fl, 0n), AR.trep(Nat, d, 0n)}, BK.bk(Nat, 1n+d, fl, 0n), BK.bk_grow(Nat, d, fl, 0n, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def left_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, xs), 0n)), U32.from_nat(m), M.nleft(~K, M.Free{0n})) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}:
  +fl = NR.lefts(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = lefts_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), m), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), Some{M.nleft(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, m), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), SC.nth(Nat, fl, m), Some{M.nleft(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, m, hiF, hcF), lefts_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nleft(~K, y0)} : Maybe<&2, Nat>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(m), 0n), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(m)), 0n)), AR.set(Nat, d, t, U32.from_nat(m), 0n, M.nleft(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, 0n)) == AR.thaw(Nat, BK.bk(Nat, d, NR.lefts(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, NR.lefts(~K, SC.init(M.Node<K>, xs)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, SC.init(Nat, fl), 0n), BK.bk(Nat, d, NR.lefts(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk_pop(Nat, d, fl, 0n, m, hmF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.init(Nat, fl), NR.lefts(~K, SC.init(M.Node<K>, xs)), lefts_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def lefts_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.nleft(~K, x) == M.nleft(~K, y) : Nat}) -> {NR.lefts(~K, SC.update(M.Node<K>, xs, i, x)) == NR.lefts(~K, xs) : List<&2, Nat>}:
  %lefts_upd(~K, xs, i, x) : {_ == NR.lefts(~K, xs) : List<&2, Nat>}
  %Equal.sym(Nat, M.nleft(~K, x), M.nleft(~K, y), he) : {SC.update(Nat, NR.lefts(~K, xs), i, _) == NR.lefts(~K, xs) : List<&2, Nat>}
  upd_same(Nat, NR.lefts(~K, xs), i, M.nleft(~K, y), lefts_nth(~K, xs, i, y, hy))

def rights_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.rights(~K, xs)) == SC.length(M.Node<K>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(SC.length(Nat, NR.rights(~K, r)), SC.length(M.Node<K>, r), rights_len(~K, r))

def rights_nth(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.rights(~K, xs), i) == Some{M.nright(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, i) == Some{M.nright(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nright(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      rights_nth(~K, r, q, y, h)

def rights_upd(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, NR.rights(~K, xs), i, M.nright(~K, y)) == NR.rights(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nright(~K, x), SC.update(Nat, NR.rights(~K, r), q, M.nright(~K, y)), NR.rights(~K, SC.update(M.Node<K>, r, q, y)), rights_upd(~K, r, q, y))

def rights_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, NR.rights(~K, xs), M.nright(~K, y)) == NR.rights(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.nright(~K, x), SC.snoc(Nat, NR.rights(~K, r), M.nright(~K, y)), NR.rights(~K, SC.snoc(M.Node<K>, r, y)), rights_snoc(~K, r, y))

def rights_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, NR.rights(~K, xs)) == NR.rights(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.nright(~K, x), SC.init(Nat, NR.rights(~K, Con{y, t})), NR.rights(~K, SC.init(M.Node<K>, Con{y, t})), rights_init(~K, Con{y, t}))

# the field block: a slot below the length reads the field
def right_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), U32.from_nat(i)) == (AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), M.nright(~K, y)) : Array<Nat> & Nat}:
  +fl = NR.rights(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = rights_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nright(~K, y)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nright(~K, y)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), rights_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nright(~K, y)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Nat, d, t, U32.from_nat(i), M.nright(~K, y), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))

# a slot below the length written with a node's field
def right_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), U32.from_nat(i), M.nright(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}:
  +fl = NR.rights(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = rights_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nright(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nright(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), rights_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nright(~K, y0)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(i), M.nright(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(i)), M.nright(~K, y))), AR.set(Nat, d, t, U32.from_nat(i), M.nright(~K, y), M.nright(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nright(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, i, M.nright(~K, y)), BK.bk(Nat, d, NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, i, M.nright(~K, y)), BK.bk(Nat, d, SC.update(Nat, fl, i, M.nright(~K, y)), 0n), BK.bk(Nat, d, NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk_set(Nat, d, fl, 0n, i, M.nright(~K, y), hiF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.update(Nat, fl, i, M.nright(~K, y)), NR.rights(~K, SC.update(M.Node<K>, xs, i, y)), rights_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def right_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), U32.from_nat(SC.length(M.Node<K>, xs)), M.nright(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}:
  +fl = NR.rights(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +n = SC.length(M.Node<K>, xs)
  +hlen = rights_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, hl), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), SC.length(Nat, fl)), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), SC.length(Nat, fl)), Some{0n}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, SC.length(Nat, fl)), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), BK.fill_at_len(Nat, SC.pow2(d), fl, 0n, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, SC.length(Nat, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(n), M.nright(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(n)), M.nright(~K, y))), AR.set(Nat, d, t, U32.from_nat(n), M.nright(~K, y), 0n, DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nright(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %hlen : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nright(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, SC.length(Nat, fl), M.nright(~K, y)), BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, SC.length(Nat, fl), M.nright(~K, y)), BK.bk(Nat, d, SC.snoc(Nat, fl, M.nright(~K, y)), 0n), BK.bk(Nat, d, NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), 0n), BK.bk_push(Nat, d, fl, 0n, M.nright(~K, y), hnF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.snoc(Nat, fl, M.nright(~K, y)), NR.rights(~K, SC.snoc(M.Node<K>, xs, y)), rights_snoc(~K, xs, y))))

# the block doubled with a default half
def right_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), Array.new(Nat, d, 0n)} == AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.rights(~K, xs), 0n)) : Array<Nat>}:
  +fl = NR.rights(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), rights_len(~K, xs)), hc)
  %Equal.sym(Array<Nat>, Array.new(Nat, d, 0n), AR.thaw(Nat, AR.trep(Nat, d, 0n)), AR.new(Nat, d, 0n)) : {ANode{AR.thaw(Nat, BK.bk(Nat, d, fl, 0n)), _} == AR.thaw(Nat, BK.bk(Nat, 1n+d, fl, 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.TNode{BK.bk(Nat, d, fl, 0n), AR.trep(Nat, d, 0n)}, BK.bk(Nat, 1n+d, fl, 0n), BK.bk_grow(Nat, d, fl, 0n, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def right_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, xs), 0n)), U32.from_nat(m), M.nright(~K, M.Free{0n})) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}:
  +fl = NR.rights(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = rights_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), m), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), Some{M.nright(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, m), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), SC.nth(Nat, fl, m), Some{M.nright(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, m, hiF, hcF), rights_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nright(~K, y0)} : Maybe<&2, Nat>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(m), 0n), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(m)), 0n)), AR.set(Nat, d, t, U32.from_nat(m), 0n, M.nright(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, 0n)) == AR.thaw(Nat, BK.bk(Nat, d, NR.rights(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, NR.rights(~K, SC.init(M.Node<K>, xs)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, SC.init(Nat, fl), 0n), BK.bk(Nat, d, NR.rights(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk_pop(Nat, d, fl, 0n, m, hmF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.init(Nat, fl), NR.rights(~K, SC.init(M.Node<K>, xs)), rights_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def rights_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.nright(~K, x) == M.nright(~K, y) : Nat}) -> {NR.rights(~K, SC.update(M.Node<K>, xs, i, x)) == NR.rights(~K, xs) : List<&2, Nat>}:
  %rights_upd(~K, xs, i, x) : {_ == NR.rights(~K, xs) : List<&2, Nat>}
  %Equal.sym(Nat, M.nright(~K, x), M.nright(~K, y), he) : {SC.update(Nat, NR.rights(~K, xs), i, _) == NR.rights(~K, xs) : List<&2, Nat>}
  upd_same(Nat, NR.rights(~K, xs), i, M.nright(~K, y), rights_nth(~K, xs, i, y, hy))

def parents_len(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.length(Nat, NR.parents(~K, xs)) == SC.length(M.Node<K>, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      N.succ_cong(SC.length(Nat, NR.parents(~K, r)), SC.length(M.Node<K>, r), parents_len(~K, r))

def parents_nth(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +h: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {SC.nth(Nat, NR.parents(~K, xs), i) == Some{M.nparent(~K, y)} : Maybe<&2, Nat>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(Nat, Nil{}, i) == Some{M.nparent(~K, y)} : Maybe<&2, Nat>}, L.false_true(Equal.cong(Maybe<&2, M.Node<K>>, Bool, z => mb(~K, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, M.Node<K>>, Maybe<&2, Nat>, z => Some{M.nparent(~K, unsome(~K, z, x))}, Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      parents_nth(~K, r, q, y, h)

def parents_upd(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>) -> {SC.update(Nat, NR.parents(~K, xs), i, M.nparent(~K, y)) == NR.parents(~K, SC.update(M.Node<K>, xs, i, y)) : List<&2, Nat>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+q:
      LL.cons_cong(Nat, M.nparent(~K, x), SC.update(Nat, NR.parents(~K, r), q, M.nparent(~K, y)), NR.parents(~K, SC.update(M.Node<K>, r, q, y)), parents_upd(~K, r, q, y))

def parents_snoc(~K: Data, +xs: List<&2, M.Node<K>>, +y: M.Node<K>) -> {SC.snoc(Nat, NR.parents(~K, xs), M.nparent(~K, y)) == NR.parents(~K, SC.snoc(M.Node<K>, xs, y)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LL.cons_cong(Nat, M.nparent(~K, x), SC.snoc(Nat, NR.parents(~K, r), M.nparent(~K, y)), NR.parents(~K, SC.snoc(M.Node<K>, r, y)), parents_snoc(~K, r, y))

def parents_init(~K: Data, +xs: List<&2, M.Node<K>>) -> {SC.init(Nat, NR.parents(~K, xs)) == NR.parents(~K, SC.init(M.Node<K>, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, Nil{}}:
      {==}
    case Con{+x, Con{+y, +t}}:
      LL.cons_cong(Nat, M.nparent(~K, x), SC.init(Nat, NR.parents(~K, Con{y, t})), NR.parents(~K, SC.init(M.Node<K>, Con{y, t})), parents_init(~K, Con{y, t}))

# the field block: a slot below the length reads the field
def parent_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), U32.from_nat(i)) == (AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), M.nparent(~K, y)) : Array<Nat> & Nat}:
  +fl = NR.parents(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = parents_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nparent(~K, y)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nparent(~K, y)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), parents_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nparent(~K, y)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Nat, d, t, U32.from_nat(i), M.nparent(~K, y), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))

# a slot below the length written with a node's field
def parent_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), U32.from_nat(i), M.nparent(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}:
  +fl = NR.parents(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = parents_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), i), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), Some{M.nparent(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, i), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), i), SC.nth(Nat, fl, i), Some{M.nparent(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, i, hiF, hcF), parents_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nparent(~K, y0)} : Maybe<&2, Nat>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(i), M.nparent(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(i)), M.nparent(~K, y))), AR.set(Nat, d, t, U32.from_nat(i), M.nparent(~K, y), M.nparent(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nparent(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, i, M.nparent(~K, y)), BK.bk(Nat, d, NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, i, M.nparent(~K, y)), BK.bk(Nat, d, SC.update(Nat, fl, i, M.nparent(~K, y)), 0n), BK.bk(Nat, d, NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk_set(Nat, d, fl, 0n, i, M.nparent(~K, y), hiF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.update(Nat, fl, i, M.nparent(~K, y)), NR.parents(~K, SC.update(M.Node<K>, xs, i, y)), parents_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def parent_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), U32.from_nat(SC.length(M.Node<K>, xs)), M.nparent(~K, y)) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}:
  +fl = NR.parents(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +n = SC.length(M.Node<K>, xs)
  +hlen = parents_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, hl), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), SC.length(Nat, fl)), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), SC.length(Nat, fl)), Some{0n}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, SC.length(Nat, fl)), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), BK.fill_at_len(Nat, SC.pow2(d), fl, 0n, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, SC.length(Nat, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{0n} : Maybe<&2, Nat>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(n), M.nparent(~K, y)), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(n)), M.nparent(~K, y))), AR.set(Nat, d, t, U32.from_nat(n), M.nparent(~K, y), 0n, DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nparent(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  %hlen : {AR.thaw(Nat, AR.upd(Nat, d, t, _, M.nparent(~K, y))) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, SC.length(Nat, fl), M.nparent(~K, y)), BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, SC.length(Nat, fl), M.nparent(~K, y)), BK.bk(Nat, d, SC.snoc(Nat, fl, M.nparent(~K, y)), 0n), BK.bk(Nat, d, NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), 0n), BK.bk_push(Nat, d, fl, 0n, M.nparent(~K, y), hnF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.snoc(Nat, fl, M.nparent(~K, y)), NR.parents(~K, SC.snoc(M.Node<K>, xs, y)), parents_snoc(~K, xs, y))))

# the block doubled with a default half
def parent_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), Array.new(Nat, d, 0n)} == AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.parents(~K, xs), 0n)) : Array<Nat>}:
  +fl = NR.parents(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), parents_len(~K, xs)), hc)
  %Equal.sym(Array<Nat>, Array.new(Nat, d, 0n), AR.thaw(Nat, AR.trep(Nat, d, 0n)), AR.new(Nat, d, 0n)) : {ANode{AR.thaw(Nat, BK.bk(Nat, d, fl, 0n)), _} == AR.thaw(Nat, BK.bk(Nat, 1n+d, fl, 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.TNode{BK.bk(Nat, d, fl, 0n), AR.trep(Nat, d, 0n)}, BK.bk(Nat, 1n+d, fl, 0n), BK.bk_grow(Nat, d, fl, 0n, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def parent_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Nat, AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, xs), 0n)), U32.from_nat(m), M.nparent(~K, M.Free{0n})) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}:
  +fl = NR.parents(~K, xs)
  +t = BK.bk(Nat, d, fl, 0n)
  +hlen = parents_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Nat, fl), Equal.sym(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Nat, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, AR.slots(Nat, t), m), SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), Some{M.nparent(~K, y0)}, Equal.cong(List<&2, Nat>, Maybe<&2, Nat>, z => SC.nth(Nat, z, m), AR.slots(Nat, t), BK.fillv(Nat, SC.pow2(d), fl, 0n), BK.bk_slots(Nat, d, fl, 0n)), Equal.trans(Maybe<&2, Nat>, SC.nth(Nat, BK.fillv(Nat, SC.pow2(d), fl, 0n), m), SC.nth(Nat, fl, m), Some{M.nparent(~K, y0)}, BK.fill_nth(Nat, SC.pow2(d), fl, 0n, m, hiF, hcF), parents_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Nat, AR.slots(Nat, t), z) == Some{M.nparent(~K, y0)} : Maybe<&2, Nat>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, t), U32.from_nat(m), 0n), AR.thaw(Nat, AR.upd(Nat, d, t, U32.to_nat(U32.from_nat(m)), 0n)), AR.set(Nat, d, t, U32.from_nat(m), 0n, M.nparent(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Nat, d, fl, 0n))) : {_ == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Nat, AR.upd(Nat, d, t, _, 0n)) == AR.thaw(Nat, BK.bk(Nat, d, NR.parents(~K, SC.init(M.Node<K>, xs)), 0n)) : Array<Nat>}
  Equal.cong(AR.Tree<Nat>, Array<Nat>, z => AR.thaw(Nat, z), AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, NR.parents(~K, SC.init(M.Node<K>, xs)), 0n), Equal.trans(AR.Tree<Nat>, AR.upd(Nat, d, t, m, 0n), BK.bk(Nat, d, SC.init(Nat, fl), 0n), BK.bk(Nat, d, NR.parents(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk_pop(Nat, d, fl, 0n, m, hmF, hcF), Equal.cong(List<&2, Nat>, AR.Tree<Nat>, z => BK.bk(Nat, d, z, 0n), SC.init(Nat, fl), NR.parents(~K, SC.init(M.Node<K>, xs)), parents_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def parents_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.nparent(~K, x) == M.nparent(~K, y) : Nat}) -> {NR.parents(~K, SC.update(M.Node<K>, xs, i, x)) == NR.parents(~K, xs) : List<&2, Nat>}:
  %parents_upd(~K, xs, i, x) : {_ == NR.parents(~K, xs) : List<&2, Nat>}
  %Equal.sym(Nat, M.nparent(~K, x), M.nparent(~K, y), he) : {SC.update(Nat, NR.parents(~K, xs), i, _) == NR.parents(~K, xs) : List<&2, Nat>}
  upd_same(Nat, NR.parents(~K, xs), i, M.nparent(~K, y), parents_nth(~K, xs, i, y, hy))

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
def key_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i)) == (AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), M.nkey(~K, y)) : Array<Maybe<&2, K>> & Maybe<&2, K>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y, hy)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), i), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), Some{M.nkey(~K, y)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, i), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), SC.nth(Maybe<&2, K>, fl, i), Some{M.nkey(~K, y)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, i, hiF, hcF), keys_nth(~K, xs, i, y, hy)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y)} : Maybe<&2, Maybe<&2, K>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  AR.get(Maybe<&2, K>, d, t, U32.from_nat(i), M.nkey(~K, y), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))

# a slot below the length written with a node's field
def key_set(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +y: M.Node<K>) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i), M.nkey(~K, y)) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)
  +hip = N.lt_le_trans(i, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(i, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), i), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), Some{M.nkey(~K, y0)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, i), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), i), SC.nth(Maybe<&2, K>, fl, i), Some{M.nkey(~K, y0)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, i, hiF, hcF), keys_nth(~K, xs, i, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y0)} : Maybe<&2, Maybe<&2, K>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu), hip)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(i), M.nkey(~K, y)), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(i)), M.nkey(~K, y))), AR.set(Maybe<&2, K>, d, t, U32.from_nat(i), M.nkey(~K, y), M.nkey(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, i, M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, i, M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, SC.update(Maybe<&2, K>, fl, i, M.nkey(~K, y)), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), None{}), BK.bk_set(Maybe<&2, K>, d, fl, None{}, i, M.nkey(~K, y), hiF, hcF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.update(Maybe<&2, K>, fl, i, M.nkey(~K, y)), NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), keys_upd(~K, xs, i, y))))

# the slot at the length (inside the capacity) written: an append
def key_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +y: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(SC.length(M.Node<K>, xs)), M.nkey(~K, y)) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +n = SC.length(M.Node<K>, xs)
  +hlen = keys_len(~K, xs)
  +eu = U.to_nat_from_nat(n, d, DAS.le32(d, l, hd, hl), hn)
  +hnF = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), n, hlen), hn)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), SC.length(Maybe<&2, K>, fl)), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), SC.length(Maybe<&2, K>, fl)), Some{None{}}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, SC.length(Maybe<&2, K>, fl)), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), BK.fill_at_len(Maybe<&2, K>, SC.pow2(d), fl, None{}, hnF))
  +hx1 = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{None{}} : Maybe<&2, Maybe<&2, K>>}, SC.length(Maybe<&2, K>, fl), n, hlen, hx0)
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{None{}} : Maybe<&2, Maybe<&2, K>>}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hx1)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, n, U32.to_nat(U32.from_nat(n)), Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu), hn)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(n), M.nkey(~K, y)), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(n)), M.nkey(~K, y))), AR.set(Maybe<&2, K>, d, t, U32.from_nat(n), M.nkey(~K, y), None{}, DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  %hlen : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, M.nkey(~K, y))) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, SC.length(Maybe<&2, K>, fl), M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, SC.length(Maybe<&2, K>, fl), M.nkey(~K, y)), BK.bk(Maybe<&2, K>, d, SC.snoc(Maybe<&2, K>, fl, M.nkey(~K, y)), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), None{}), BK.bk_push(Maybe<&2, K>, d, fl, None{}, M.nkey(~K, y), hnF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.snoc(Maybe<&2, K>, fl, M.nkey(~K, y)), NR.keys(~K, SC.snoc(M.Node<K>, xs, y)), keys_snoc(~K, xs, y))))

# the block doubled with a default half
def key_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {ANode{AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), Array.new(Maybe<&2, K>, d, None{})} == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, NR.keys(~K, xs), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), keys_len(~K, xs)), hc)
  %Equal.sym(Array<Maybe<&2, K>>, Array.new(Maybe<&2, K>, d, None{}), AR.thaw(Maybe<&2, K>, AR.trep(Maybe<&2, K>, d, None{})), AR.new(Maybe<&2, K>, d, None{})) : {ANode{AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, fl, None{})), _} == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, fl, None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.TNode{BK.bk(Maybe<&2, K>, d, fl, None{}), AR.trep(Maybe<&2, K>, d, None{})}, BK.bk(Maybe<&2, K>, 1n+d, fl, None{}), BK.bk_grow(Maybe<&2, K>, d, fl, None{}, hcF))

# the last slot reset to the encoding of Free{0}: a pop
def key_drop(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(m), M.nkey(~K, M.Free{0n})) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}:
  +fl = NR.keys(~K, xs)
  +t = BK.bk(Maybe<&2, K>, d, fl, None{})
  +hlen = keys_len(~K, xs)
  +hi = LL.nth_lt_length(M.Node<K>, xs, m, y0, hy0)
  +hip = N.lt_le_trans(m, SC.length(M.Node<K>, xs), SC.pow2(d), hi, hc)
  +eu = U.to_nat_from_nat(m, d, DAS.le32(d, l, hd, hl), hip)
  +hiF = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hi)
  +hcF = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), SC.length(Maybe<&2, K>, fl), Equal.sym(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), hlen), hc)
  +hmF = Equal.trans(Nat, SC.length(Maybe<&2, K>, fl), SC.length(M.Node<K>, xs), 1n+m, hlen, hm)
  +hx0 = Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), m), SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), m), Some{M.nkey(~K, y0)}, Equal.cong(List<&2, Maybe<&2, K>>, Maybe<&2, Maybe<&2, K>>, z => SC.nth(Maybe<&2, K>, z, m), AR.slots(Maybe<&2, K>, t), BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), BK.bk_slots(Maybe<&2, K>, d, fl, None{})), Equal.trans(Maybe<&2, Maybe<&2, K>>, SC.nth(Maybe<&2, K>, BK.fillv(Maybe<&2, K>, SC.pow2(d), fl, None{}), m), SC.nth(Maybe<&2, K>, fl, m), Some{M.nkey(~K, y0)}, BK.fill_nth(Maybe<&2, K>, SC.pow2(d), fl, None{}, m, hiF, hcF), keys_nth(~K, xs, m, y0, hy0)))
  +hx = L.subst(Nat, z => {SC.nth(Maybe<&2, K>, AR.slots(Maybe<&2, K>, t), z) == Some{M.nkey(~K, y0)} : Maybe<&2, Maybe<&2, K>>}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hx0)
  +hiu = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, m, U32.to_nat(U32.from_nat(m)), Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu), hip)
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, t), U32.from_nat(m), None{}), AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, U32.to_nat(U32.from_nat(m)), None{})), AR.set(Maybe<&2, K>, d, t, U32.from_nat(m), None{}, M.nkey(~K, y0), DAS.lt32(d, l, hd, hl), hiu, hx, BK.bk_perfect(Maybe<&2, K>, d, fl, None{}))) : {_ == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(m)), m, eu) : {AR.thaw(Maybe<&2, K>, AR.upd(Maybe<&2, K>, d, t, _, None{})) == AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})) : Array<Maybe<&2, K>>}
  Equal.cong(AR.Tree<Maybe<&2, K>>, Array<Maybe<&2, K>>, z => AR.thaw(Maybe<&2, K>, z), AR.upd(Maybe<&2, K>, d, t, m, None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}), Equal.trans(AR.Tree<Maybe<&2, K>>, AR.upd(Maybe<&2, K>, d, t, m, None{}), BK.bk(Maybe<&2, K>, d, SC.init(Maybe<&2, K>, fl), None{}), BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}), BK.bk_pop(Maybe<&2, K>, d, fl, None{}, m, hmF, hcF), Equal.cong(List<&2, Maybe<&2, K>>, AR.Tree<Maybe<&2, K>>, z => BK.bk(Maybe<&2, K>, d, z, None{}), SC.init(Maybe<&2, K>, fl), NR.keys(~K, SC.init(M.Node<K>, xs)), keys_init(~K, xs))))

# updating a node that keeps this field leaves the field list
def keys_keep(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +x: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}, +he: {M.nkey(~K, x) == M.nkey(~K, y) : Maybe<&2, K>}) -> {NR.keys(~K, SC.update(M.Node<K>, xs, i, x)) == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}:
  %keys_upd(~K, xs, i, x) : {_ == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}
  %Equal.sym(Maybe<&2, K>, M.nkey(~K, x), M.nkey(~K, y), he) : {SC.update(Maybe<&2, K>, NR.keys(~K, xs), i, _) == NR.keys(~K, xs) : List<&2, Maybe<&2, K>>}
  upd_same(Maybe<&2, K>, NR.keys(~K, xs), i, M.nkey(~K, y), keys_nth(~K, xs, i, y, hy))

