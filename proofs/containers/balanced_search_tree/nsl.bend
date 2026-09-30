import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ../../../src/containers/types/dynamic_array.bend as DE
import ./bk.bend as BK
import ./nsr.bend as NR
import ./nsf.bend as NF
import ./lk.bend as LKB
import ./da.bend as DA
import ./state.bend as ST

# The TreeMap's node store (the ns_* functions of the implementation) on the
# realization of a node list xs of length at most 2^d, d <= l <= 29: a read
# returns the list's node, a write in range updates the list, an append
# snocs it (doubling the capacity when full and below the limit), clear
# empties it. These are the statements the dynamic-array lemmas of arr.bend
# make for a dynamic array of nodes.


def isj(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# a slot below the length holds something
def nth_isj(-A: Data, +xs: List<&2, A>, +i: Nat, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {isj(A, SC.nth(A, xs, i)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({isj(A, SC.nth(A, Nil{}, i)) == True{} : Bool}, N.lt_zero_absurd(i, h))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+q:
      nth_isj(A, r, q, h)

def len_init(-A: Data, +xs: List<&2, A>, +m: Nat, +h: {SC.length(A, xs) == 1n+m : Nat}) -> {SC.length(A, SC.init(A, xs)) == m : Nat}:
  match xs m:
    case Nil{} _:
      Empty.absurd({SC.length(A, SC.init(A, Nil{})) == m : Nat}, N.zero_succ(m, h))
    case Con{x, Nil{}} 0n:
      {==}
    case Con{x, Nil{}} 1n+q:
      Empty.absurd({SC.length(A, SC.init(A, Con{x, Nil{}})) == 1n+q : Nat}, N.zero_succ(q, N.succ_inj(0n, 1n+q, h)))
    case Con{x, Con{y, t}} 0n:
      Empty.absurd({SC.length(A, SC.init(A, Con{x, Con{y, t}})) == 0n : Nat}, N.succ_zero(SC.length(A, t), N.succ_inj(1n+SC.length(A, t), 0n, h)))
    case Con{x, Con{+y, +t}} 1n+q:
      N.succ_cong(SC.length(A, SC.init(A, Con{y, t})), q, len_init(A, Con{y, t}, q, N.succ_inj(1n+SC.length(A, t), 1n+q, h)))

# a node is its encoding read back
def mk_enc(~K: Data, +y: M.Node<K>) -> {M.mk_node(~K, M.ntag(~K, y), M.nleft(~K, y), M.nright(~K, y), M.nparent(~K, y), M.nkey(~K, y)) == y : M.Node<K>}:
  match y:
    case M.Free{x}:
      {==}
    case M.N{True{}, lf, rt, pa, k}:
      {==}
    case M.N{False{}, lf, rt, pa, k}:
      {==}

# ---- length ----

def ns_length_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {M.ns_length(~K, NR.real(~K, l, d, xs)) == (NR.real(~K, l, d, xs), SC.length(M.Node<K>, xs)) : M.NodeStore<K> & Nat}:
  {==}

# ---- the links array: indices and bounds ----

# the depth of the links array's halves is below 31
def he2(+l: Nat, +d: Nat, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}) -> {Nat.is_lt(1n+(1n+d), 32n) == True{} : Bool}:
  N.le_lt_succ(d, 29n, N.le_trans(d, l, 29n, hd, hl))

# slot 2(p+i) of the array is slot 2i of its high half, 2(p+i)+1 slot 2i+1
def ixt(+p: Nat, +i: Nat) -> {Nat.add(Nat.double(p), Nat.double(i)) == Nat.double(Nat.add(p, i)) : Nat}:
  N.add_double(p, i)

def ixp(+p: Nat, +i: Nat) -> {Nat.add(Nat.double(p), 1n+Nat.double(i)) == 1n+Nat.double(Nat.add(p, i)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(p), 1n+Nat.double(i)), 1n+Nat.add(Nat.double(p), Nat.double(i)), 1n+Nat.double(Nat.add(p, i)), N.add_succ(Nat.double(p), Nat.double(i)), N.succ_cong(Nat.add(Nat.double(p), Nat.double(i)), Nat.double(Nat.add(p, i)), N.add_double(p, i)))

# both slots of node i are below the length of a pair list of n nodes
def dl0(+n: Nat, +i: Nat, +pl: List<&2, Nat>, +hlen: {SC.length(Nat, pl) == Nat.double(n) : Nat}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(Nat.double(i), SC.length(Nat, pl)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, pl), Nat.double(n), hlen) : {Nat.is_lt(Nat.double(i), _) == True{} : Bool}
  N.double_lt(i, n, hi)

def dl1(+n: Nat, +i: Nat, +pl: List<&2, Nat>, +hlen: {SC.length(Nat, pl) == Nat.double(n) : Nat}, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.double(i), SC.length(Nat, pl)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, pl), Nat.double(n), hlen) : {Nat.is_lt(1n+Nat.double(i), _) == True{} : Bool}
  N.succ_le_lt(1n+Nat.double(i), Nat.double(n), N.double_le(1n+i, n, N.lt_succ_le_succ(i, n, hi)))

# ---- the links array: reading a field of a node ----


def left_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i))) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nleft(~K, y)) : Array<Nat> & Nat}:
  LKB.get_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.nleft(~K, y), NF.lrs_nth0(~K, xs, i, y, hy))

def right_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i))) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nright(~K, y)) : Array<Nat> & Nat}:
  LKB.get_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), 1n+Nat.double(i), M.nright(~K, y), NF.lrs_nth1(~K, xs, i, y, hy))

def tag_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y)) : Array<Nat> & Nat}:
  %ixt(SC.pow2(d), i) : {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_)) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y)) : Array<Nat> & Nat}
  LKB.get_hi(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.ntag(~K, y), NF.tps_nth0(~K, xs, i, y, hy))

def parent_get(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i)))) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nparent(~K, y)) : Array<Nat> & Nat}:
  %ixp(SC.pow2(d), i) : {Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_)) == (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nparent(~K, y)) : Array<Nat> & Nat}
  LKB.get_hi(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), 1n+Nat.double(i), M.nparent(~K, y), NF.tps_nth1(~K, xs, i, y, hy))

# ---- the links array: writing one field of a node (the others kept) ----


def left_aset(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}:
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), LKB.set_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.nleft(~K, y), dl0(SC.length(M.Node<K>, xs), i, NR.lrs(~K, xs), NF.lrs_len(~K, xs), LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, y)), NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), NF.lrs_upd0(~K, xs, i, y0, y, hy0, er)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), NR.tps(~K, xs), NF.tps_keep(~K, xs, i, y0, y, hy0, et, ep)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, _, 0n)}) : Array<Nat>}
  {==}

def right_aset(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i)), M.nright(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}:
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i)), M.nright(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, SC.update(Nat, NR.lrs(~K, xs), 1n+Nat.double(i), M.nright(~K, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), LKB.set_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), 1n+Nat.double(i), M.nright(~K, y), dl1(SC.length(M.Node<K>, xs), i, NR.lrs(~K, xs), NF.lrs_len(~K, xs), LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, NR.lrs(~K, xs), 1n+Nat.double(i), M.nright(~K, y)), NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), NF.lrs_upd1(~K, xs, i, y0, y, hy0, el)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), NR.tps(~K, xs), NF.tps_keep(~K, xs, i, y0, y, hy0, et, ep)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, _, 0n)}) : Array<Nat>}
  {==}

def tag_aset(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}:
  %ixt(SC.pow2(d), i) : {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), M.ntag(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), Nat.double(i))), M.ntag(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, y)), 0n)}), LKB.set_hi(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.ntag(~K, y), dl0(SC.length(M.Node<K>, xs), i, NR.tps(~K, xs), NF.tps_len(~K, xs), LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, y)), NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), NF.tps_upd0(~K, xs, i, y0, y, hy0, ep)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, _, 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), NR.lrs(~K, xs), NF.lrs_keep(~K, xs, i, y0, y, hy0, el, er)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  {==}

def parent_aset(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}) -> {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}:
  %ixp(SC.pow2(d), i) : {Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), M.nparent(~K, y)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+Nat.double(i))), M.nparent(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, SC.update(Nat, NR.tps(~K, xs), 1n+Nat.double(i), M.nparent(~K, y)), 0n)}), LKB.set_hi(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), 1n+Nat.double(i), M.nparent(~K, y), dl1(SC.length(M.Node<K>, xs), i, NR.tps(~K, xs), NF.tps_len(~K, xs), LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0)))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, NR.tps(~K, xs), 1n+Nat.double(i), M.nparent(~K, y)), NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), NF.tps_upd1(~K, xs, i, y0, y, hy0, et)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, _, 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), NR.lrs(~K, xs), NF.lrs_keep(~K, xs, i, y0, y, hy0, el, er)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}) : Array<Nat>}
  {==}

# ---- read ----

def get_some(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y: M.Node<K>, +hy: {SC.nth(M.Node<K>, xs, i) == Some{y} : Maybe<&2, M.Node<K>>}) -> {M.ns_get_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}:
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y)), tag_get(~K, l, d, xs, hl, hd, hc, i, y, hy)) : {M.ns_rt(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, _) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nleft(~K, y)), left_get(~K, l, d, xs, hl, hd, hc, i, y, hy)) : {M.ns_rl(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, M.ntag(~K, y), _) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nright(~K, y)), right_get(~K, l, d, xs, hl, hd, hc, i, y, hy)) : {M.ns_rr(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, M.ntag(~K, y), M.nleft(~K, y), _) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nparent(~K, y)), parent_get(~K, l, d, xs, hl, hd, hc, i, y, hy)) : {M.ns_rp(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, M.ntag(~K, y), M.nleft(~K, y), M.nright(~K, y), _) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  %Equal.sym(Array<Maybe<&2, K>> & Maybe<&2, K>, Array.get(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i)), (AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), M.nkey(~K, y)), NF.key_get(~K, l, d, xs, hl, hd, hc, i, y, hy)) : {M.ns_rk(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y), M.nleft(~K, y), M.nright(~K, y), M.nparent(~K, y), _) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  %Equal.sym(M.Node<K>, M.mk_node(~K, M.ntag(~K, y), M.nleft(~K, y), M.nright(~K, y), M.nparent(~K, y), M.nkey(~K, y)), y, mk_enc(~K, y)) : {(M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))}, Done{_}) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, Some{y})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
  {==}

def gs(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_get_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, mv)) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_get_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, None{})) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      get_some(~K, l, d, xs, hl, hd, hc, i, y, hmv)

def gc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_get_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, SC.nth(M.Node<K>, xs, i))) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}:
  match b:
    case True{}:
      gs(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), None{}, LL.nth_none(M.Node<K>, xs, i, N.not_lt_le(i, SC.length(M.Node<K>, xs), hb))) : {M.ns_get_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, _)) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}
      {==}

# a read returns the list's node (IndexOutOfRange past the length)
def ns_get_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_get(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), DA.item(M.Node<K>, SC.nth(M.Node<K>, xs, i))) : M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>}:
  gc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

# ---- write ----


# the four link slots of a node below the length written: the node replaced
def links_put(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, x)), U32.from_nat(1n+Nat.double(i)), M.nright(~K, x)), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}:
  +cu = NF.lrs_cap(~K, d, SC.update(M.Node<K>, xs, i, x), LKB.cap_upd(M.Node<K>, SC.pow2(d), xs, i, x, hc))
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, x)), U32.from_nat(1n+Nat.double(i)), M.nright(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, SC.update(Nat, SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, x)), 1n+Nat.double(i), M.nright(~K, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), LKB.set2_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.nleft(~K, x), 1n+Nat.double(i), M.nright(~K, x), dl0(SC.length(M.Node<K>, xs), i, NR.lrs(~K, xs), NF.lrs_len(~K, xs), hi), dl1(SC.length(M.Node<K>, xs), i, NR.lrs(~K, xs), NF.lrs_len(~K, xs), hi))) : {Array.set(Nat, Array.set(Nat, _, U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, SC.update(Nat, NR.lrs(~K, xs), Nat.double(i), M.nleft(~K, x)), 1n+Nat.double(i), M.nright(~K, x)), NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), NF.lrs_put(~K, xs, i, x)) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  %ixt(SC.pow2(d), i) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  %ixp(SC.pow2(d), i) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), Nat.double(i))), M.ntag(~K, x)), U32.from_nat(_), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), Nat.double(i))), M.ntag(~K, x)), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+Nat.double(i))), M.nparent(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, SC.update(Nat, SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, x)), 1n+Nat.double(i), M.nparent(~K, x)), 0n)}), LKB.set2_hi(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), cu, NF.tps_cap(~K, d, xs, hc), Nat.double(i), M.ntag(~K, x), 1n+Nat.double(i), M.nparent(~K, x), dl0(SC.length(M.Node<K>, xs), i, NR.tps(~K, xs), NF.tps_len(~K, xs), hi), dl1(SC.length(M.Node<K>, xs), i, NR.tps(~K, xs), NF.tps_len(~K, xs), hi))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.update(Nat, SC.update(Nat, NR.tps(~K, xs), Nat.double(i), M.ntag(~K, x)), 1n+Nat.double(i), M.nparent(~K, x)), NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), NF.tps_put(~K, xs, i, x)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, _, 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}) : Array<Nat>}
  {==}

def set_some(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {M.ns_set_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, x, True{}) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, x)), U32.from_nat(1n+Nat.double(i)), M.nright(~K, x)), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}), links_put(~K, l, d, xs, hl, hd, hc, i, x, LL.nth_lt_length(M.Node<K>, xs, i, y0, hy0))) : {(M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), _, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i), M.nkey(~K, x))}, Done{Unit{}}) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i), M.nkey(~K, x)), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, x)), None{})), NF.key_set(~K, l, d, xs, hl, hd, hc, i, y0, hy0, x)) : {(M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}), _}, Done{Unit{}}) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, x)), SC.length(M.Node<K>, xs), LL.length_update(M.Node<K>, xs, i, x)) : {(M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, x)), None{}))}, Done{Unit{}}) == (M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, x)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.update(M.Node<K>, xs, i, x)), None{}))}, Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  {==}

def ws(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_set_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, x, True{}) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_set_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, x, True{}) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y0}:
      set_some(~K, l, d, xs, hl, hd, hc, i, x, y0, hmv)

# a write below the length updates the list
def ns_set_in(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +h: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_set(~K, NR.real(~K, l, d, xs), i, x) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), True{}, h) : {M.ns_set_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, x, _) == (NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  ws(~K, l, d, xs, hl, hd, hc, i, x, SC.nth(M.Node<K>, xs, i), {==}, h)

# a write past the length changes nothing
def ns_set_out(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +h: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == False{} : Bool}) -> {M.ns_set(~K, NR.real(~K, l, d, xs), i, x) == (NR.real(~K, l, d, xs), Fail{DE.IndexOutOfRange{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), False{}, h) : {M.ns_set_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, x, _) == (NR.real(~K, l, d, xs), Fail{DE.IndexOutOfRange{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  {==}


# ---- append ----


# room for both slots of a node past the length of a pair list
def dn1(+n: Nat, +p: Nat, +pl: List<&2, Nat>, +hlen: {SC.length(Nat, pl) == Nat.double(n) : Nat}, +h: {Nat.is_lt(n, p) == True{} : Bool}) -> {Nat.is_lt(1n+SC.length(Nat, pl), Nat.double(p)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, pl), Nat.double(n), hlen) : {Nat.is_lt(1n+_, Nat.double(p)) == True{} : Bool}
  N.succ_le_lt(1n+Nat.double(n), Nat.double(p), N.double_le(1n+n, p, N.lt_succ_le_succ(n, p, h)))

def cap_sn(~K: Data, +d: Nat, +xs: List<&2, M.Node<K>>, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_le(SC.length(M.Node<K>, SC.snoc(M.Node<K>, xs, x)), SC.pow2(d)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.snoc(M.Node<K>, xs, x)), 1n+SC.length(M.Node<K>, xs), LL.length_snoc(M.Node<K>, xs, x)) : {Nat.is_le(_, SC.pow2(d)) == True{} : Bool}
  N.lt_succ_le_succ(SC.length(M.Node<K>, xs), SC.pow2(d), hn)

# the four link slots at the length written: the node appended
def links_push(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(SC.length(M.Node<K>, xs))), M.nleft(~K, x)), U32.from_nat(1n+Nat.double(SC.length(M.Node<K>, xs))), M.nright(~K, x)), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}:
  +cs = NF.lrs_cap(~K, d, SC.snoc(M.Node<K>, xs, x), cap_sn(~K, d, xs, x, hn))
  %NF.lrs_len(~K, xs) : {Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), M.nleft(~K, x)), U32.from_nat(1n+_), M.nright(~K, x)), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(SC.length(Nat, NR.lrs(~K, xs))), M.nleft(~K, x)), U32.from_nat(1n+SC.length(Nat, NR.lrs(~K, xs))), M.nright(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, SC.snoc(Nat, SC.snoc(Nat, NR.lrs(~K, xs), M.nleft(~K, x)), M.nright(~K, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), LKB.push2_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), M.nleft(~K, x), M.nright(~K, x), dn1(SC.length(M.Node<K>, xs), SC.pow2(d), NR.lrs(~K, xs), NF.lrs_len(~K, xs), hn))) : {Array.set(Nat, Array.set(Nat, _, U32.from_nat(Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.snoc(Nat, SC.snoc(Nat, NR.lrs(~K, xs), M.nleft(~K, x)), M.nright(~K, x)), NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), NF.lrs_snoc(~K, xs, x)) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %ixt(SC.pow2(d), SC.length(M.Node<K>, xs)) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %ixp(SC.pow2(d), SC.length(M.Node<K>, xs)) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), Nat.double(SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(_), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %NF.tps_len(~K, xs) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), _)), M.ntag(~K, x)), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+_)), M.nparent(~K, x)) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), SC.length(Nat, NR.tps(~K, xs)))), M.ntag(~K, x)), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+SC.length(Nat, NR.tps(~K, xs)))), M.nparent(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, SC.snoc(Nat, SC.snoc(Nat, NR.tps(~K, xs), M.ntag(~K, x)), M.nparent(~K, x)), 0n)}), LKB.push2_hi(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), cs, NF.tps_cap(~K, d, xs, hc), M.ntag(~K, x), M.nparent(~K, x), dn1(SC.length(M.Node<K>, xs), SC.pow2(d), NR.tps(~K, xs), NF.tps_len(~K, xs), hn))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.snoc(Nat, SC.snoc(Nat, NR.tps(~K, xs), M.ntag(~K, x)), M.nparent(~K, x)), NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), NF.tps_snoc(~K, xs, x)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, _, 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}) : Array<Nat>}
  {==}

def push_at(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {M.ns_put(~K, l, d, SC.pow2(d), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), SC.length(M.Node<K>, xs), x) == NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(SC.length(M.Node<K>, xs))), M.nleft(~K, x)), U32.from_nat(1n+Nat.double(SC.length(M.Node<K>, xs))), M.nright(~K, x)), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.ntag(~K, x)), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), SC.length(M.Node<K>, xs)))), M.nparent(~K, x)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}), links_push(~K, l, d, xs, hl, hd, hc, x, hn)) : {M.NS{l, d, SC.pow2(d), 1n+SC.length(M.Node<K>, xs), _, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(SC.length(M.Node<K>, xs)), M.nkey(~K, x))} == NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)) : M.NodeStore<K>}
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(SC.length(M.Node<K>, xs)), M.nkey(~K, x)), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, x)), None{})), NF.key_push(~K, l, d, xs, hl, hd, hc, x, hn)) : {M.NS{l, d, SC.pow2(d), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}), _} == NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)) : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.snoc(M.Node<K>, xs, x)), 1n+SC.length(M.Node<K>, xs), LL.length_snoc(M.Node<K>, xs, x)) : {M.NS{l, d, SC.pow2(d), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, x)), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.snoc(M.Node<K>, xs, x)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.snoc(M.Node<K>, xs, x)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.snoc(M.Node<K>, xs, x)), None{}))} : M.NodeStore<K>}
  {==}

# with room: the node appended
def ns_push_room(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {M.ns_push(~K, NR.real(~K, l, d, xs), x) == (NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)), True{}, hn) : {M.ns_push_room(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), x, _, Nat.is_lt(d, l)) == (NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  Equal.cong(M.NodeStore<K>, M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>, z => (z, Done{Unit{}}), M.ns_put(~K, l, d, SC.pow2(d), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), SC.length(M.Node<K>, xs), x), NR.real(~K, l, d, SC.snoc(M.Node<K>, xs, x)), push_at(~K, l, d, xs, hl, hd, hc, x, hn))

# full and below the limit: the blocks doubled, then the node appended
def ns_push_grow(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == False{} : Bool}, +hdl: {Nat.is_lt(d, l) == True{} : Bool}) -> {M.ns_push(~K, NR.real(~K, l, d, xs), x) == (NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  +hd1 = N.lt_succ_le_succ(d, l, hdl)
  +hc1 = N.le_trans(SC.length(M.Node<K>, xs), SC.pow2(d), SC.pow2(1n+d), hc, N.lt_le(SC.pow2(d), SC.pow2(1n+d), N.pow2_lt_succ(d)))
  +hn1 = N.le_lt_trans(SC.length(M.Node<K>, xs), SC.pow2(d), SC.pow2(1n+d), hc, N.pow2_lt_succ(d))
  %Equal.sym(Bool, Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)), False{}, hn) : {M.ns_push_room(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), x, _, Nat.is_lt(d, l)) == (NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Bool, Nat.is_lt(d, l), True{}, hdl) : {M.ns_push_room(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), x, False{}, _) == (NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Nat>, ANode{ANode{AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n)), Array.new(Nat, 1n+d, 0n)}, ANode{AR.thaw(Nat, BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)), Array.new(Nat, 1n+d, 0n)}}, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+1n+d, NR.tps(~K, xs), 0n)}), LKB.grow(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc))) : {(M.ns_put(~K, l, 1n+d, Nat.double(SC.pow2(d)), 1n+SC.length(M.Node<K>, xs), _, M.ns_grow_keys(~K, d, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))), SC.length(M.Node<K>, xs), x), Done{Unit{}}) == (NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, K>>, ANode{AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), Array.new(Maybe<&2, K>, d, None{})}, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, NR.keys(~K, xs), None{})), NF.key_grow(~K, l, d, xs, hl, hd, hc)) : {(M.ns_put(~K, l, 1n+d, Nat.double(SC.pow2(d)), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+1n+d, NR.tps(~K, xs), 0n)}), _, SC.length(M.Node<K>, xs), x), Done{Unit{}}) == (NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), Done{Unit{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  Equal.cong(M.NodeStore<K>, M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>, z => (z, Done{Unit{}}), M.ns_put(~K, l, 1n+d, SC.pow2(1n+d), 1n+SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, 1n+d, NR.keys(~K, xs), None{})), SC.length(M.Node<K>, xs), x), NR.real(~K, l, 1n+d, SC.snoc(M.Node<K>, xs, x)), push_at(~K, l, 1n+d, xs, hl, hd1, hc1, x, hn1))

# full at the limit: nothing changes
def ns_push_full(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +x: M.Node<K>, +hn: {Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)) == False{} : Bool}, +hdl: {Nat.is_lt(d, l) == False{} : Bool}) -> {M.ns_push(~K, NR.real(~K, l, d, xs), x) == (NR.real(~K, l, d, xs), Fail{DE.CapacityExceeded{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(SC.length(M.Node<K>, xs), SC.pow2(d)), False{}, hn) : {M.ns_push_room(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), x, _, Nat.is_lt(d, l)) == (NR.real(~K, l, d, xs), Fail{DE.CapacityExceeded{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Bool, Nat.is_lt(d, l), False{}, hdl) : {M.ns_push_room(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), x, False{}, _) == (NR.real(~K, l, d, xs), Fail{DE.CapacityExceeded{}}) : M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>}
  {==}


# ---- clear ----


def len2(+n: Nat, +m: Nat, +pl: List<&2, Nat>, +hlen: {SC.length(Nat, pl) == Nat.double(n) : Nat}, +hm: {n == 1n+m : Nat}) -> {SC.length(Nat, pl) == 1n+(1n+Nat.double(m)) : Nat}:
  L.subst(Nat, z => {SC.length(Nat, pl) == Nat.double(z) : Nat}, n, 1n+m, hm, hlen)

# the four link slots of the last node zeroed: the node dropped
def links_wipe(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}) -> {Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(m)), 0n), U32.from_nat(Nat.double(m)), 0n), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), m))), 0n), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), m))), 0n) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}:
  +ci = NF.lrs_cap(~K, d, SC.init(M.Node<K>, xs), LKB.cap_init(M.Node<K>, SC.pow2(d), xs, m, hm, hc))
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(m)), 0n), U32.from_nat(Nat.double(m)), 0n), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, SC.init(Nat, SC.init(Nat, NR.lrs(~K, xs))), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), LKB.pop2_lo(Nat, 1n+d, NR.lrs(~K, xs), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), NF.lrs_cap(~K, d, xs, hc), NF.tps_cap(~K, d, xs, hc), Nat.double(m), len2(SC.length(M.Node<K>, xs), m, NR.lrs(~K, xs), NF.lrs_len(~K, xs), hm))) : {Array.set(Nat, Array.set(Nat, _, U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), m))), 0n), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), m))), 0n) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.init(Nat, SC.init(Nat, NR.lrs(~K, xs))), NR.lrs(~K, SC.init(M.Node<K>, xs)), NF.lrs_init(~K, xs)) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, _, 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), m))), 0n), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), m))), 0n) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  %ixp(SC.pow2(d), m) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(_), 0n), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), m))), 0n) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  %ixt(SC.pow2(d), m) : {Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+Nat.double(m))), 0n), U32.from_nat(_), 0n) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), 1n+Nat.double(m))), 0n), U32.from_nat(Nat.add(Nat.double(SC.pow2(d)), Nat.double(m))), 0n), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, SC.init(Nat, SC.init(Nat, NR.tps(~K, xs))), 0n)}), LKB.pop2_hi(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), NR.tps(~K, xs), 0n, he2(l, d, hl, hd), ci, NF.tps_cap(~K, d, xs, hc), Nat.double(m), len2(SC.length(M.Node<K>, xs), m, NR.tps(~K, xs), NF.tps_len(~K, xs), hm))) : {_ == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  %Equal.sym(List<&2, Nat>, SC.init(Nat, SC.init(Nat, NR.tps(~K, xs))), NR.tps(~K, SC.init(M.Node<K>, xs)), NF.tps_init(~K, xs)) : {AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, _, 0n)}) == AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}) : Array<Nat>}
  {==}

def drop_some(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +y0: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, m) == Some{y0} : Maybe<&2, M.Node<K>>}) -> {M.ns_drop(~K, NR.real(~K, l, d, xs), m) == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat>, Array.set(Nat, Array.set(Nat, Array.set(Nat, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(m)), 0n), U32.from_nat(Nat.double(m)), 0n), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), m))), 0n), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), m))), 0n), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}), links_wipe(~K, l, d, xs, hl, hd, hc, m, hm)) : {M.NS{l, d, SC.pow2(d), m, _, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(m), None{})} == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}
  %Equal.sym(Array<Maybe<&2, K>>, Array.set(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(m), M.nkey(~K, M.Free{0n})), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{})), NF.key_drop(~K, l, d, xs, hl, hd, hc, m, hm, y0, hy0)) : {M.NS{l, d, SC.pow2(d), m, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}), _} == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.init(M.Node<K>, xs)), m, len_init(M.Node<K>, xs, m, hm)) : {M.NS{l, d, SC.pow2(d), m, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.init(M.Node<K>, xs)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.init(M.Node<K>, xs)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, SC.init(M.Node<K>, xs)), None{}))} : M.NodeStore<K>}
  {==}

def dr(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, m) == mv : Maybe<&2, M.Node<K>>}) -> {M.ns_drop(~K, NR.real(~K, l, d, xs), m) == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}:
  match mv:
    case None{}:
      +hi = L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, 1n+m, SC.length(M.Node<K>, xs), Equal.sym(Nat, SC.length(M.Node<K>, xs), 1n+m, hm), N.lt_succ(m))
      Empty.absurd({M.ns_drop(~K, NR.real(~K, l, d, xs), m) == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, m), None{}, hmv, nth_isj(M.Node<K>, xs, m, hi))))
    case Some{+y0}:
      drop_some(~K, l, d, xs, hl, hd, hc, m, hm, y0, hmv)

# dropping the last live slot: the list without its last node
def ns_drop_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +m: Nat, +hm: {SC.length(M.Node<K>, xs) == 1n+m : Nat}) -> {M.ns_drop(~K, NR.real(~K, l, d, xs), m) == NR.real(~K, l, d, SC.init(M.Node<K>, xs)) : M.NodeStore<K>}:
  dr(~K, l, d, xs, hl, hd, hc, m, hm, SC.nth(M.Node<K>, xs, m), {==})

def clr(~K: Data, +k: Nat, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +hk: {SC.length(M.Node<K>, xs) == k : Nat}) -> {M.ns_clear_go(~K, k, NR.real(~K, l, d, xs)) == NR.real(~K, l, d, Nil{}) : M.NodeStore<K>}:
  match k:
    case 0n:
      Equal.cong(List<&2, M.Node<K>>, M.NodeStore<K>, z => NR.real(~K, l, d, z), xs, Nil{}, LL.length_zero_nil(M.Node<K>, xs, hk))
    case 1n+ +m:
      +hm2 = len_init(M.Node<K>, xs, m, hk)
      %Equal.sym(M.NodeStore<K>, M.ns_drop(~K, NR.real(~K, l, d, xs), m), NR.real(~K, l, d, SC.init(M.Node<K>, xs)), ns_drop_ok(~K, l, d, xs, hl, hd, hc, m, hk)) : {M.ns_clear_go(~K, m, _) == NR.real(~K, l, d, Nil{}) : M.NodeStore<K>}
      clr(~K, m, l, d, SC.init(M.Node<K>, xs), hl, hd, N.le_trans(SC.length(M.Node<K>, SC.init(M.Node<K>, xs)), 1n+m, SC.pow2(d), L.subst(Nat, z => {Nat.is_le(z, 1n+m) == True{} : Bool}, m, SC.length(M.Node<K>, SC.init(M.Node<K>, xs)), Equal.sym(Nat, SC.length(M.Node<K>, SC.init(M.Node<K>, xs)), m, hm2), N.le_succ(m)), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, xs), 1n+m, hk, hc)), hm2)

# clear empties the list, keeping the capacity
def ns_clear_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}) -> {M.ns_clear(~K, NR.real(~K, l, d, xs)) == NR.real(~K, l, d, Nil{}) : M.NodeStore<K>}:
  clr(~K, SC.length(M.Node<K>, xs), l, d, xs, hl, hd, hc, {==})

# ---- reading one field of a slot ----


def ors(-X: Data, m: Maybe<&2, X>, +dv: X) -> X:
  match m:
    case None{}:
      dv
    case Some{x}:
      x

def nth_or_some(-X: Data, +xs: List<&2, X>, +i: Nat, +y: X, +dv: X, +h: {SC.nth(X, xs, i) == Some{y} : Maybe<&2, X>}) -> {ST.nth_or(X, xs, i, dv) == y : X}:
  match xs i:
    case Nil{} _:
      Empty.absurd({dv == y : X}, L.false_true(Equal.cong(Maybe<&2, X>, Bool, z => isj(X, z), None{}, Some{y}, h)))
    case Con{+x, r} 0n:
      Equal.cong(Maybe<&2, X>, X, z => ors(X, z, x), Some{x}, Some{y}, h)
    case Con{x, +r} 1n+q:
      nth_or_some(X, r, q, y, dv, h)

def nth_or_hi(-X: Data, +xs: List<&2, X>, +i: Nat, +dv: X, +h: {Nat.is_lt(i, SC.length(X, xs)) == False{} : Bool}) -> {ST.nth_or(X, xs, i, dv) == dv : X}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({x == dv : X}, L.true_false(h))
    case Con{x, +t} 1n+q:
      nth_or_hi(X, t, q, dv, h)

def tag_ats(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_tag_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.ntag(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_tag_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.ntag(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), y, nth_or_some(M.Node<K>, xs, i, y, M.Free{0n}, hmv)) : {M.ns_tag_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.ntag(~K, _)) : M.NodeStore<K> & Nat}
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y)), tag_get(~K, l, d, xs, hl, hd, hc, i, y, hmv)) : {M.ns_field_fin(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), _) == (NR.real(~K, l, d, xs), M.ntag(~K, y)) : M.NodeStore<K> & Nat}
      {==}

def tag_atc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_tag_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), M.ntag(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match b:
    case True{}:
      tag_ats(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{0n}, nth_or_hi(M.Node<K>, xs, i, M.Free{0n}, hb)) : {M.ns_tag_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), M.ntag(~K, _)) : M.NodeStore<K> & Nat}
      {==}

# the field of the list's node (of Free{0} past the length)
def tag_at_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_tag_at(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), M.ntag(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  tag_atc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def left_ats(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nleft(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nleft(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), y, nth_or_some(M.Node<K>, xs, i, y, M.Free{0n}, hmv)) : {M.ns_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nleft(~K, _)) : M.NodeStore<K> & Nat}
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nleft(~K, y)), left_get(~K, l, d, xs, hl, hd, hc, i, y, hmv)) : {M.ns_field_fin(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), _) == (NR.real(~K, l, d, xs), M.nleft(~K, y)) : M.NodeStore<K> & Nat}
      {==}

def left_atc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), M.nleft(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match b:
    case True{}:
      left_ats(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{0n}, nth_or_hi(M.Node<K>, xs, i, M.Free{0n}, hb)) : {M.ns_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), M.nleft(~K, _)) : M.NodeStore<K> & Nat}
      {==}

# the field of the list's node (of Free{0} past the length)
def left_at_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_left_at(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), M.nleft(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  left_atc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def right_ats(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nright(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nright(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), y, nth_or_some(M.Node<K>, xs, i, y, M.Free{0n}, hmv)) : {M.ns_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nright(~K, _)) : M.NodeStore<K> & Nat}
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nright(~K, y)), right_get(~K, l, d, xs, hl, hd, hc, i, y, hmv)) : {M.ns_field_fin(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), _) == (NR.real(~K, l, d, xs), M.nright(~K, y)) : M.NodeStore<K> & Nat}
      {==}

def right_atc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), M.nright(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match b:
    case True{}:
      right_ats(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{0n}, nth_or_hi(M.Node<K>, xs, i, M.Free{0n}, hb)) : {M.ns_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), M.nright(~K, _)) : M.NodeStore<K> & Nat}
      {==}

# the field of the list's node (of Free{0} past the length)
def right_at_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_right_at(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), M.nright(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  right_atc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def parent_ats(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nparent(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nparent(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), y, nth_or_some(M.Node<K>, xs, i, y, M.Free{0n}, hmv)) : {M.ns_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nparent(~K, _)) : M.NodeStore<K> & Nat}
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.nparent(~K, y)), parent_get(~K, l, d, xs, hl, hd, hc, i, y, hmv)) : {M.ns_field_fin(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), _) == (NR.real(~K, l, d, xs), M.nparent(~K, y)) : M.NodeStore<K> & Nat}
      {==}

def parent_atc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), M.nparent(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  match b:
    case True{}:
      parent_ats(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{0n}, nth_or_hi(M.Node<K>, xs, i, M.Free{0n}, hb)) : {M.ns_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), M.nparent(~K, _)) : M.NodeStore<K> & Nat}
      {==}

# the field of the list's node (of Free{0} past the length)
def parent_at_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_parent_at(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), M.nparent(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Nat}:
  parent_atc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})


# ---- writing one field of a slot ----

def isn(~K: Data, n: M.Node<K>) -> Bool:
  match n:
    case M.Free{x}:
      False{}
    case M.N{c, lf, rt, pa, k}:
      True{}

# a live node is below the length
def nth_or_lt(~K: Data, +xs: List<&2, M.Node<K>>, +i: Nat, +y: M.Node<K>, +hn: {isn(~K, y) == True{} : Bool}, +h: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == y : M.Node<K>}) -> {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(i, 0n) == True{} : Bool}, L.false_true(L.subst(M.Node<K>, z => {isn(~K, z) == True{} : Bool}, y, M.Free{0n}, Equal.sym(M.Node<K>, M.Free{0n}, y, h), hn)))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+q:
      nth_or_lt(~K, r, q, y, hn, h)

def nth_of_or(-X: Data, +xs: List<&2, X>, +i: Nat, +dv: X, +h: {Nat.is_lt(i, SC.length(X, xs)) == True{} : Bool}) -> {SC.nth(X, xs, i) == Some{ST.nth_or(X, xs, i, dv)} : Maybe<&2, X>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(X, Nil{}, i) == Some{dv} : Maybe<&2, X>}, N.lt_zero_absurd(i, h))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+q:
      nth_of_or(X, r, q, dv, h)

def red_tag_eq(~K: Data, +v: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K) -> {M.ns_red_tag(v) == M.ntag(~K, M.N{v, lf, rt, q, k}) : Nat}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}



# QN: the field; QT: the written value's type; QV: the value written; QF: the
# field of a node; QIX: its slot; QAS: the links lemma; QHD, QHU: the fields
# kept; QNEW(c): the node written over N{c, lf, rt, q, k}; QHV: its field is
# the value written
def left_set_k(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +v: Nat, +t: Nat, +ht0: {M.ntag(~K, y0) == 1n+t : Nat}, +hv: {M.nleft(~K, y) == v : Nat}, +hk: {M.nkey(~K, y) == M.nkey(~K, y0) : Maybe<&2, K>}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {M.ns_set_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y0)), tag_get(~K, l, d, xs, hl, hd, hc, i, y0, hy0)) : {M.ns_set_left_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Nat, M.ntag(~K, y0), 1n+t, ht0) : {M.ns_set_left_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), _)) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %hv : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), _), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(i)), M.nleft(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), left_aset(~K, l, d, xs, hl, hd, hc, i, y0, y, hy0, er, et, ep)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), _, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(List<&2, Maybe<&2, K>>, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), NR.keys(~K, xs), NF.keys_keep(~K, xs, i, y0, y, hy0, hk)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, _, None{}))} : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), SC.length(M.Node<K>, xs), LL.length_update(M.Node<K>, xs, i, y)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} : M.NodeStore<K>}
  {==}

def left_set_c(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy2: {SC.nth(M.Node<K>, xs, i) == Some{M.N{c, lf, rt, q, k}} : Maybe<&2, M.Node<K>>}) -> {M.ns_set_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, v, rt, q, k})) : M.NodeStore<K>}:
  match c:
    case True{}:
      left_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{True{}, lf, rt, q, k}, M.N{True{}, v, rt, q, k}, hy2, v, 1n, {==}, {==}, {==}, {==}, {==}, {==})
    case False{}:
      left_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{False{}, lf, rt, q, k}, M.N{False{}, v, rt, q, k}, hy2, v, 0n, {==}, {==}, {==}, {==}, {==}, {==})

# writing the field of a live node: the list with that field replaced
def left_set_node(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.N{c, lf, rt, q, k} : M.Node<K>}) -> {M.ns_set_left(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, v, rt, q, k})) : M.NodeStore<K>}:
  +hlt = nth_or_lt(~K, xs, i, M.N{c, lf, rt, q, k}, {==}, hy)
  +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.N{c, lf, rt, q, k}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hlt), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, z => Some{z}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.N{c, lf, rt, q, k}, hy))
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), True{}, hlt) : {M.ns_set_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, v, rt, q, k})) : M.NodeStore<K>}
  left_set_c(~K, l, d, xs, hl, hd, hc, i, v, c, lf, rt, q, k, hy2)

def left_set_fc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_set_left_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, b) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.Free{z}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hb), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, w => Some{w}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{z}, hy))
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, M.Free{z})), tag_get(~K, l, d, xs, hl, hd, hc, i, M.Free{z}, hy2)) : {M.ns_set_left_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, xs) : M.NodeStore<K>}
      {==}

# writing the field of a free slot (or past the length) changes nothing
def left_set_free(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}) -> {M.ns_set_left(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  left_set_fc(~K, l, d, xs, hl, hd, hc, i, v, z, hy, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def right_set_k(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +v: Nat, +t: Nat, +ht0: {M.ntag(~K, y0) == 1n+t : Nat}, +hv: {M.nright(~K, y) == v : Nat}, +hk: {M.nkey(~K, y) == M.nkey(~K, y0) : Maybe<&2, K>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {M.ns_set_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y0)), tag_get(~K, l, d, xs, hl, hd, hc, i, y0, hy0)) : {M.ns_set_right_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Nat, M.ntag(~K, y0), 1n+t, ht0) : {M.ns_set_right_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), _)) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %hv : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i)), _), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(i)), M.nright(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), right_aset(~K, l, d, xs, hl, hd, hc, i, y0, y, hy0, el, et, ep)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), _, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(List<&2, Maybe<&2, K>>, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), NR.keys(~K, xs), NF.keys_keep(~K, xs, i, y0, y, hy0, hk)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, _, None{}))} : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), SC.length(M.Node<K>, xs), LL.length_update(M.Node<K>, xs, i, y)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} : M.NodeStore<K>}
  {==}

def right_set_c(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy2: {SC.nth(M.Node<K>, xs, i) == Some{M.N{c, lf, rt, q, k}} : Maybe<&2, M.Node<K>>}) -> {M.ns_set_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, v, q, k})) : M.NodeStore<K>}:
  match c:
    case True{}:
      right_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{True{}, lf, rt, q, k}, M.N{True{}, lf, v, q, k}, hy2, v, 1n, {==}, {==}, {==}, {==}, {==}, {==})
    case False{}:
      right_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{False{}, lf, rt, q, k}, M.N{False{}, lf, v, q, k}, hy2, v, 0n, {==}, {==}, {==}, {==}, {==}, {==})

# writing the field of a live node: the list with that field replaced
def right_set_node(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.N{c, lf, rt, q, k} : M.Node<K>}) -> {M.ns_set_right(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, v, q, k})) : M.NodeStore<K>}:
  +hlt = nth_or_lt(~K, xs, i, M.N{c, lf, rt, q, k}, {==}, hy)
  +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.N{c, lf, rt, q, k}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hlt), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, z => Some{z}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.N{c, lf, rt, q, k}, hy))
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), True{}, hlt) : {M.ns_set_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, v, q, k})) : M.NodeStore<K>}
  right_set_c(~K, l, d, xs, hl, hd, hc, i, v, c, lf, rt, q, k, hy2)

def right_set_fc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_set_right_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, b) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.Free{z}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hb), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, w => Some{w}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{z}, hy))
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, M.Free{z})), tag_get(~K, l, d, xs, hl, hd, hc, i, M.Free{z}, hy2)) : {M.ns_set_right_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, xs) : M.NodeStore<K>}
      {==}

# writing the field of a free slot (or past the length) changes nothing
def right_set_free(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}) -> {M.ns_set_right(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  right_set_fc(~K, l, d, xs, hl, hd, hc, i, v, z, hy, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def parent_set_k(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +v: Nat, +t: Nat, +ht0: {M.ntag(~K, y0) == 1n+t : Nat}, +hv: {M.nparent(~K, y) == v : Nat}, +hk: {M.nkey(~K, y) == M.nkey(~K, y0) : Maybe<&2, K>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +et: {M.ntag(~K, y0) == M.ntag(~K, y) : Nat}) -> {M.ns_set_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y0)), tag_get(~K, l, d, xs, hl, hd, hc, i, y0, hy0)) : {M.ns_set_parent_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Nat, M.ntag(~K, y0), 1n+t, ht0) : {M.ns_set_parent_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), _)) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %hv : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), _), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(1n+Nat.double(Nat.add(SC.pow2(d), i))), M.nparent(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), parent_aset(~K, l, d, xs, hl, hd, hc, i, y0, y, hy0, el, er, et)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), _, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(List<&2, Maybe<&2, K>>, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), NR.keys(~K, xs), NF.keys_keep(~K, xs, i, y0, y, hy0, hk)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, _, None{}))} : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), SC.length(M.Node<K>, xs), LL.length_update(M.Node<K>, xs, i, y)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} : M.NodeStore<K>}
  {==}

def parent_set_c(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy2: {SC.nth(M.Node<K>, xs, i) == Some{M.N{c, lf, rt, q, k}} : Maybe<&2, M.Node<K>>}) -> {M.ns_set_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, rt, v, k})) : M.NodeStore<K>}:
  match c:
    case True{}:
      parent_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{True{}, lf, rt, q, k}, M.N{True{}, lf, rt, v, k}, hy2, v, 1n, {==}, {==}, {==}, {==}, {==}, {==})
    case False{}:
      parent_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{False{}, lf, rt, q, k}, M.N{False{}, lf, rt, v, k}, hy2, v, 0n, {==}, {==}, {==}, {==}, {==}, {==})

# writing the field of a live node: the list with that field replaced
def parent_set_node(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.N{c, lf, rt, q, k} : M.Node<K>}) -> {M.ns_set_parent(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, rt, v, k})) : M.NodeStore<K>}:
  +hlt = nth_or_lt(~K, xs, i, M.N{c, lf, rt, q, k}, {==}, hy)
  +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.N{c, lf, rt, q, k}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hlt), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, z => Some{z}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.N{c, lf, rt, q, k}, hy))
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), True{}, hlt) : {M.ns_set_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{c, lf, rt, v, k})) : M.NodeStore<K>}
  parent_set_c(~K, l, d, xs, hl, hd, hc, i, v, c, lf, rt, q, k, hy2)

def parent_set_fc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_set_parent_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, b) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.Free{z}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hb), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, w => Some{w}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{z}, hy))
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, M.Free{z})), tag_get(~K, l, d, xs, hl, hd, hc, i, M.Free{z}, hy2)) : {M.ns_set_parent_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, xs) : M.NodeStore<K>}
      {==}

# writing the field of a free slot (or past the length) changes nothing
def parent_set_free(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Nat, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}) -> {M.ns_set_parent(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  parent_set_fc(~K, l, d, xs, hl, hd, hc, i, v, z, hy, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})

def red_set_k(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +y0: M.Node<K>, +y: M.Node<K>, +hy0: {SC.nth(M.Node<K>, xs, i) == Some{y0} : Maybe<&2, M.Node<K>>}, +v: Bool, +t: Nat, +ht0: {M.ntag(~K, y0) == 1n+t : Nat}, +hv: {M.ntag(~K, y) == M.ns_red_tag(v) : Nat}, +hk: {M.nkey(~K, y) == M.nkey(~K, y0) : Maybe<&2, K>}, +el: {M.nleft(~K, y0) == M.nleft(~K, y) : Nat}, +er: {M.nright(~K, y0) == M.nright(~K, y) : Nat}, +ep: {M.nparent(~K, y0) == M.nparent(~K, y) : Nat}) -> {M.ns_set_red_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}:
  %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, y0)), tag_get(~K, l, d, xs, hl, hd, hc, i, y0, hy0)) : {M.ns_set_red_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Nat, M.ntag(~K, y0), 1n+t, ht0) : {M.ns_set_red_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), _)) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %hv : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), _), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(Array<Nat>, Array.set(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i))), M.ntag(~K, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), tag_aset(~K, l, d, xs, hl, hd, hc, i, y0, y, hy0, el, er, ep)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), _, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, y)) : M.NodeStore<K>}
  %Equal.sym(List<&2, Maybe<&2, K>>, NR.keys(~K, SC.update(M.Node<K>, xs, i, y)), NR.keys(~K, xs), NF.keys_keep(~K, xs, i, y0, y, hy0, hk)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, _, None{}))} : M.NodeStore<K>}
  %Equal.sym(Nat, SC.length(M.Node<K>, SC.update(M.Node<K>, xs, i, y)), SC.length(M.Node<K>, xs), LL.length_update(M.Node<K>, xs, i, y)) : {M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} == M.NS{l, d, SC.pow2(d), _, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, SC.update(M.Node<K>, xs, i, y)), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, SC.update(M.Node<K>, xs, i, y)), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{}))} : M.NodeStore<K>}
  {==}

def red_set_c(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Bool, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy2: {SC.nth(M.Node<K>, xs, i) == Some{M.N{c, lf, rt, q, k}} : Maybe<&2, M.Node<K>>}) -> {M.ns_set_red_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, True{}) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{v, lf, rt, q, k})) : M.NodeStore<K>}:
  match c:
    case True{}:
      red_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{True{}, lf, rt, q, k}, M.N{v, lf, rt, q, k}, hy2, v, 1n, {==}, Equal.sym(Nat, M.ns_red_tag(v), M.ntag(~K, M.N{v, lf, rt, q, k}), red_tag_eq(~K, v, lf, rt, q, k)), {==}, {==}, {==}, {==})
    case False{}:
      red_set_k(~K, l, d, xs, hl, hd, hc, i, M.N{False{}, lf, rt, q, k}, M.N{v, lf, rt, q, k}, hy2, v, 0n, {==}, Equal.sym(Nat, M.ns_red_tag(v), M.ntag(~K, M.N{v, lf, rt, q, k}), red_tag_eq(~K, v, lf, rt, q, k)), {==}, {==}, {==}, {==})

# writing the field of a live node: the list with that field replaced
def red_set_node(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Bool, +c: Bool, +lf: Nat, +rt: Nat, +q: Nat, +k: K, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.N{c, lf, rt, q, k} : M.Node<K>}) -> {M.ns_set_red(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{v, lf, rt, q, k})) : M.NodeStore<K>}:
  +hlt = nth_or_lt(~K, xs, i, M.N{c, lf, rt, q, k}, {==}, hy)
  +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.N{c, lf, rt, q, k}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hlt), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, z => Some{z}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.N{c, lf, rt, q, k}, hy))
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(M.Node<K>, xs)), True{}, hlt) : {M.ns_set_red_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, SC.update(M.Node<K>, xs, i, M.N{v, lf, rt, q, k})) : M.NodeStore<K>}
  red_set_c(~K, l, d, xs, hl, hd, hc, i, v, c, lf, rt, q, k, hy2)

def red_set_fc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Bool, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_set_red_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, b) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hy2 = Equal.trans(Maybe<&2, M.Node<K>>, SC.nth(M.Node<K>, xs, i), Some{ST.nth_or(M.Node<K>, xs, i, M.Free{0n})}, Some{M.Free{z}}, nth_of_or(M.Node<K>, xs, i, M.Free{0n}, hb), Equal.cong(M.Node<K>, Maybe<&2, M.Node<K>>, w => Some{w}, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{z}, hy))
      %Equal.sym(Array<Nat> & Nat, Array.get(Nat, AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), U32.from_nat(Nat.double(Nat.add(SC.pow2(d), i)))), (AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), M.ntag(~K, M.Free{z})), tag_get(~K, l, d, xs, hl, hd, hc, i, M.Free{z}, hy2)) : {M.ns_set_red_tag(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, v, _) == NR.real(~K, l, d, xs) : M.NodeStore<K>}
      {==}

# writing the field of a free slot (or past the length) changes nothing
def red_set_free(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: Bool, +z: Nat, +hy: {ST.nth_or(M.Node<K>, xs, i, M.Free{0n}) == M.Free{z} : M.Node<K>}) -> {M.ns_set_red(~K, NR.real(~K, l, d, xs), i, v) == NR.real(~K, l, d, xs) : M.NodeStore<K>}:
  red_set_fc(~K, l, d, xs, hl, hd, hc, i, v, z, hy, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})


# ---- reading a slot's key ----

def key_ats(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +mv: Maybe<&2, M.Node<K>>, +hmv: {SC.nth(M.Node<K>, xs, i) == mv : Maybe<&2, M.Node<K>>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == True{} : Bool}) -> {M.ns_key_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nkey(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Maybe<&2, K>}:
  match mv:
    case None{}:
      Empty.absurd({M.ns_key_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nkey(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Maybe<&2, K>}, L.false_true(L.subst(Maybe<&2, M.Node<K>>, z => {isj(M.Node<K>, z) == True{} : Bool}, SC.nth(M.Node<K>, xs, i), None{}, hmv, nth_isj(M.Node<K>, xs, i, hi))))
    case Some{+y}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), y, nth_or_some(M.Node<K>, xs, i, y, M.Free{0n}, hmv)) : {M.ns_key_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, True{}) == (NR.real(~K, l, d, xs), M.nkey(~K, _)) : M.NodeStore<K> & Maybe<&2, K>}
      %Equal.sym(Array<Maybe<&2, K>> & Maybe<&2, K>, Array.get(Maybe<&2, K>, AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), U32.from_nat(i)), (AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), M.nkey(~K, y)), NF.key_get(~K, l, d, xs, hl, hd, hc, i, y, hmv)) : {M.ns_key_fin(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), _) == (NR.real(~K, l, d, xs), M.nkey(~K, y)) : M.NodeStore<K> & Maybe<&2, K>}
      {==}

def key_atc(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, xs)) == b : Bool}) -> {M.ns_key_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, b) == (NR.real(~K, l, d, xs), M.nkey(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Maybe<&2, K>}:
  match b:
    case True{}:
      key_ats(~K, l, d, xs, hl, hd, hc, i, SC.nth(M.Node<K>, xs, i), {==}, hb)
    case False{}:
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}), M.Free{0n}, nth_or_hi(M.Node<K>, xs, i, M.Free{0n}, hb)) : {M.ns_key_ok(~K, l, d, SC.pow2(d), SC.length(M.Node<K>, xs), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, NR.lrs(~K, xs), 0n), BK.bk(Nat, 1n+d, NR.tps(~K, xs), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, NR.keys(~K, xs), None{})), i, False{}) == (NR.real(~K, l, d, xs), M.nkey(~K, _)) : M.NodeStore<K> & Maybe<&2, K>}
      {==}

# the key of the list's node (None for a free slot or past the length)
def key_at_ok(~K: Data, +l: Nat, +d: Nat, +xs: List<&2, M.Node<K>>, +hl: {Nat.is_le(l, 29n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {M.ns_key_at(~K, NR.real(~K, l, d, xs), i) == (NR.real(~K, l, d, xs), M.nkey(~K, ST.nth_or(M.Node<K>, xs, i, M.Free{0n}))) : M.NodeStore<K> & Maybe<&2, K>}:
  key_atc(~K, l, d, xs, hl, hd, hc, i, Nat.is_lt(i, SC.length(M.Node<K>, xs)), {==})
